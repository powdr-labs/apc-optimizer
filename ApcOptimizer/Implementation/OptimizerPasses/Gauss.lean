import ApcOptimizer.Implementation.OptimizerPasses.Affine
import ApcOptimizer.Implementation.OptimizerPasses.SubstMap
import ApcOptimizer.Implementation.OptimizerPasses.Normalize
import Batteries.Data.BinaryHeap

set_option autoImplicit false

/-! # Dense Gauss elimination

The affine substitution layer (`denseLinSubstF`, `denseSparseSolveAt`), then the sparse engine built
on it. Correctness and the wired `denseGaussElimFPass` live in `Proofs/Gauss.lean`.

Each algebraic constraint is walked **once** into either a sparse affine row or a *blocked* verdict
carrying the variables to watch (`gEval`); a blocked constraint is re-walked only when one of those
variables is solved, which is the only way its first surviving variable×variable product can
collapse. Rows are developed against the solution map when the scheduler reaches them, never
re-derived from the source expression. Every per-variable index is a `VarId.index`-keyed array.

Two schedulers, on the `denseMarkowitzMinRows` gate: source order below it (the SP1 `rsp` shapes need
that basis), shortest-row-first above it (in source order a substitution chain there inflates a
stored solution to hundreds of terms before it cancels back down).

`DenseSolved` is the plain solution map the domain / flag / fx / rootPair passes share. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- Fold variable leaves in left-to-right order without materializing `vars`. -/
def DenseExpr.foldVars {α : Type} (e : DenseExpr p) (f : α → VarId → α) (init : α) : α :=
  match e with
  | .const _ => init
  | .var x => f init x
  | .add a b => b.foldVars f (a.foldVars f init)
  | .mul a b => b.foldVars f (a.foldVars f init)

def DenseExpr.isVar : DenseExpr p → Bool
  | .var _ => true
  | _ => false

/-- Grow `a` so `i` is in range, filling with `d`; doubling, so repeated growth stays amortized.

The per-variable indexes below are `VarId.index`-keyed arrays rather than `Std.HashMap VarId _`
because `Array.modify` hands the element to its update function uniquely: a nested
`m.insert x ((m[x]?).getD ∅ |>.insert e)` instead copies the inner set on every update, the map
still holding a reference to it. -/
def denseArrEnsure {α : Type} (a : Array α) (i : Nat) (d : α) : Array α :=
  if i < a.size then a
  else a ++ Array.replicate (max (i + 1) (2 * a.size) - a.size) d

/-- A plain (proof-free) solution map keyed by `VarId`; correctness is established by the
    correctness proof (`Proofs/Gauss.lean`), not carried as a structure invariant. -/
structure DenseSolved (p : ℕ) where
  map : Std.HashMap VarId (DenseExpr p)
  revDeps : Std.HashMap VarId (Std.HashSet VarId)

namespace DenseSolved

def empty : DenseSolved p := { map := ∅, revDeps := ∅ }

/-- The map as a lookup function (what `substF` consumes). -/
def fn (dσ : DenseSolved p) : VarId → Option (DenseExpr p) := fun i => dσ.map[i]?

/-- Insert a list of pairs: for each, insert into the map and fold the value's variables into the
    reverse-dependency index. -/
def insertAll (dσ : DenseSolved p) : List (VarId × DenseExpr p) → DenseSolved p
  | [] => dσ
  | (x, t) :: rest =>
      DenseSolved.insertAll
        { map := dσ.map.insert x t,
          revDeps := t.foldVars (fun rd z => rd.insert z (((rd[z]?).getD ∅).insert x)) dσ.revDeps }
        rest

theorem insertAll_map :
    ∀ (pairs : List (VarId × DenseExpr p)) (dσ : DenseSolved p),
      (dσ.insertAll pairs).map = pairs.foldl (fun m p => m.insert p.1 p.2) dσ.map := by
  intro pairs
  induction pairs with
  | nil => intro dσ; rfl
  | cons hd tl ih =>
      intro dσ; obtain ⟨x, t⟩ := hd
      simp only [insertAll, List.foldl_cons]
      rw [ih]

end DenseSolved

/-! ## Sparse affine substitution -/

/-- Substitute sparse affine rows into an affine row, preserving first-occurrence term order. -/
def denseLinSubstF (l : DenseLinExpr p) (σ : VarId → Option (DenseLinExpr p)) :
    DenseLinExpr p :=
  let const := l.terms.foldl (fun out yc =>
    match σ yc.1 with
    | some t => out + yc.2 * t.const
    | none => out) l.const
  let terms := l.terms.flatMap (fun yc =>
    match σ yc.1 with
    | some t => t.terms.map (fun zc => (zc.1, yc.2 * zc.2))
    | none => [yc])
  (DenseLinExpr.mk const terms).norm

/-- Substitute one canonical affine row into another. -/
def denseLinSubst (l : DenseLinExpr p) (x : VarId) (t : DenseLinExpr p) : DenseLinExpr p :=
  denseLinSubstF l (fun y => if y = x then some t else none)

def denseLinScale (k : ZMod p) (l : DenseLinExpr p) : DenseLinExpr p :=
  (l.scale k).norm

/-- Boxed twin of `denseLinSubstF`, sharing one `DenseZModOps p` with the normal form it builds. -/
def denseLinSubstFWith (ops : DenseZModOps p) (l : DenseLinExpr p)
    (σ : VarId → Option (DenseLinExpr p)) : DenseLinExpr p :=
  let const := l.terms.foldl (fun out yc =>
    match σ yc.1 with
    | some t => ops.add out (ops.mul yc.2 t.const)
    | none => out) l.const
  let terms := l.terms.flatMap (fun yc =>
    match σ yc.1 with
    | some t => denseScaleTermsWith ops yc.2 t.terms
    | none => [yc])
  (DenseLinExpr.mk const terms).normWith ops

theorem denseLinSubstFWith_eq (ops : DenseZModOps p) (l : DenseLinExpr p)
    (σ : VarId → Option (DenseLinExpr p)) : denseLinSubstFWith ops l σ = denseLinSubstF l σ := by
  simp only [denseLinSubstFWith, denseLinSubstF, DenseLinExpr.normWith_eq, ops.add_eq, ops.mul_eq,
    denseScaleTermsWith_eq]

def denseLinScaleWith (ops : DenseZModOps p) (k : ZMod p) (l : DenseLinExpr p) : DenseLinExpr p :=
  (l.scaleWith ops k).normWith ops

theorem denseLinScaleWith_eq (ops : DenseZModOps p) (k : ZMod p) (l : DenseLinExpr p) :
    denseLinScaleWith ops k l = denseLinScale k l := by
  simp only [denseLinScaleWith, denseLinScale, DenseLinExpr.scaleWith_eq, DenseLinExpr.normWith_eq]

def DenseLinExpr.mentions (l : DenseLinExpr p) (x : VarId) : Bool :=
  l.terms.any (fun yc => yc.1 = x)


def denseSparseSolveAt (l : DenseLinExpr p) (x : VarId) :
    Option (VarId × DenseLinExpr p) :=
  if l.coeff x = 1 then some (x, denseLinScale (-1) (l.others x))
  else if l.coeff x = -1 then some (x, l.others x)
  else if l.coeff x * (l.coeff x)⁻¹ = 1 then
    some (x, denseLinScale (-(l.coeff x)⁻¹) (l.others x))
  else none

/-- Boxed twin of `denseSparseSolveAt`, binding the pivot coefficient once. -/
def denseSparseSolveAtWith (ops : DenseZModOps p) (l : DenseLinExpr p) (x : VarId) :
    Option (VarId × DenseLinExpr p) :=
  let c := denseCoeffSumWith ops x l.terms
  if c = ops.one then some (x, denseLinScaleWith ops ops.negOne (l.others x))
  else if c = ops.negOne then some (x, l.others x)
  else if ops.mul c c⁻¹ = ops.one then
    some (x, denseLinScaleWith ops (ops.mul ops.negOne c⁻¹) (l.others x))
  else none

theorem denseSparseSolveAtWith_eq (ops : DenseZModOps p) (l : DenseLinExpr p) (x : VarId) :
    denseSparseSolveAtWith ops l x = denseSparseSolveAt l x := by
  simp only [denseSparseSolveAtWith, denseSparseSolveAt, DenseLinExpr.coeff,
    denseCoeffSumWith_eq, denseLinScaleWith_eq, ops.one_eq, ops.negOne_eq, ops.mul_eq,
    ← neg_eq_neg_one_mul]

/-- Every variable of `l.others v` is a variable of `l`; consumed by `denseSparseSolveAt_terms`. -/
theorem DenseLinExpr.others_terms_fst_mem (l : DenseLinExpr p) (v : VarId) (x : VarId)
    (h : x ∈ (l.others v).terms.map Prod.fst) : x ∈ l.terms.map Prod.fst := by
  simp only [DenseLinExpr.others, List.mem_map] at h ⊢
  obtain ⟨tt, htt, rfl⟩ := h
  exact ⟨tt, List.mem_of_mem_filter htt, rfl⟩

/-- Above this many constraints the fill-aware scheduler takes over from source order. Below it the
    SP1 `rsp` shapes need the source-order basis: the fill-aware one there costs 8 of its 100 cases
    +88 variables (`agent-docs/log.md` entry 160). -/
def denseMarkowitzMinRows : Nat := 8192

/-! ## The substituted-evaluation walk -/

/-- Substituted evaluation of a subtree: a constant, an affine form (terms not yet merged), or
    blocked by a surviving variable×variable product, carrying the variables to watch. -/
inductive GRes (p : ℕ) where
  | cst (c : ZMod p)
  | lin (l : DenseLinExpr p)
  | blk (ws : List VarId)

/-- The solution map as a lookup function; `VarId.index`-keyed, so no hashing. -/
def gSolFn (sol : Array (Option (DenseLinExpr p))) : VarId → Option (DenseLinExpr p) :=
  fun i => (sol[i.index]?).getD none

def gAddRes (ops : DenseZModOps p) : GRes p → GRes p → GRes p
  | .blk w, _ => .blk w
  | _, .blk w => .blk w
  | .cst c1, .cst c2 => .cst (ops.add c1 c2)
  | .cst c1, .lin l2 => .lin ⟨ops.add c1 l2.const, l2.terms⟩
  | .lin l1, .cst c2 => .lin ⟨ops.add l1.const c2, l1.terms⟩
  | .lin l1, .lin l2 => .lin (l1.addWith ops l2)

/-- A product is affine exactly when one side's *merged* substituted form is constant; otherwise the
    node blocks, and the merged sides' variables are what can unblock it. -/
def gMulRes (ops : DenseZModOps p) : GRes p → GRes p → GRes p
  | .blk w, _ => .blk w
  | _, .blk w => .blk w
  | .cst c1, .cst c2 => .cst (ops.mul c1 c2)
  | .cst c1, .lin l2 => .lin (l2.scaleWith ops c1)
  | .lin l1, .cst c2 => .lin (l1.scaleWith ops c2)
  | .lin l1, .lin l2 =>
      let n1 := l1.normWith ops
      if n1.terms.isEmpty then .lin (l2.scaleWith ops n1.const)
      else
        let n2 := l2.normWith ops
        if n2.terms.isEmpty then .lin (n1.scaleWith ops n2.const)
        else .blk (n1.terms.map Prod.fst ++ n2.terms.map Prod.fst)

/-- Walk `e` under the solution map. Blocking propagates unconditionally through `add` and `mul`, so
    the walk stops at the first surviving product and allocates nothing on that path. -/
def gEval (ops : DenseZModOps p) (sol : Array (Option (DenseLinExpr p))) :
    DenseExpr p → GRes p
  | .const n => .cst n
  | .var x =>
      match gSolFn sol x with
      | some t => .lin t
      | none => .lin ⟨ops.zero, [(x, ops.one)]⟩
  | .add a b =>
      match gEval ops sol a with
      | .blk w => .blk w
      | ra => gAddRes ops ra (gEval ops sol b)
  | .mul a b =>
      match gEval ops sol a with
      | .blk w => .blk w
      | ra => gMulRes ops ra (gEval ops sol b)

/-- The walk's verdict at a constraint root: a merged row, or the variables to watch. -/
inductive GTop (p : ℕ) where
  | row (l : DenseLinExpr p)
  | blocked (ws : List VarId)

def gRoot (ops : DenseZModOps p) (sol : Array (Option (DenseLinExpr p))) (e : DenseExpr p) :
    GTop p :=
  match gEval ops sol e with
  | .cst c => .row ⟨c, []⟩
  | .lin l => .row (l.normWith ops)
  | .blk ws => .blocked ws

/-! ## Pivot selection

`denseGaussScore` on a merged row is `(occ[v] - 1) * |terms|`, plus `1000000` when protected, since
every variable of a merged row occurs exactly once. So the choice is: smallest score, `±1`
coefficients before other units, earliest term — one scan, with `occ`/`prot` as arrays. -/

def gScore (occ : Array Nat) (prot : Array Bool) (v : VarId) (n : Nat) : Nat :=
  let base := ((occ[v.index]?).getD 1 - 1) * n
  if (prot[v.index]?).getD false then base + 1000000 else base

def gIsPm1 (ops : DenseZModOps p) (c : ZMod p) : Bool :=
  zmodIsOne c || zmodIsOne (ops.mul ops.negOne c)

/-- Best candidate by `(score, ±1 first, position)`, skipping `banned` variables. -/
def gBestGo (ops : DenseZModOps p) (occ : Array Nat) (prot : Array Bool) (n : Nat)
    (banned : List VarId) : List (VarId × ZMod p) → Option (VarId × Nat × Bool) → Option VarId
  | [], best => best.map (·.1)
  | (v, c) :: rest, best =>
      if banned.contains v then gBestGo ops occ prot n banned rest best
      else
        let s := gScore occ prot v n
        let pm1 := gIsPm1 ops c
        match best with
        | none => gBestGo ops occ prot n banned rest (some (v, s, pm1))
        | some (bv, bs, bpm1) =>
            if s < bs || (s == bs && pm1 && !bpm1) then
              gBestGo ops occ prot n banned rest (some (v, s, pm1))
            else gBestGo ops occ prot n banned rest (some (bv, bs, bpm1))

/-- Pick the best pivot and solve for it, skipping candidates whose coefficient is not a unit (only
    reachable on a non-prime modulus — `denseSparseSolveAt` decides). -/
def gPick (ops : DenseZModOps p) (occ : Array Nat) (prot : Array Bool) (l : DenseLinExpr p) :
    Nat → List VarId → Option (VarId × DenseLinExpr p)
  | 0, _ => none
  | fuel + 1, banned =>
      match gBestGo ops occ prot l.terms.length banned l.terms none with
      | none => none
      | some x =>
          match denseSparseSolveAtWith ops l x with
          | some xt => some xt
          | none => gPick ops occ prot l fuel (x :: banned)

/-- A byte-ladder scale: `256^k`, `1 ≤ k ≤ 3`. -/
def gLadderPow (r : ZMod p) : Bool :=
  r.val = 256 || r.val = 65536 || r.val = 16777216

/-- The head of a base-256 ladder row `±(x − Σ 256^k·yₖ)`: a `±1`-coefficient variable whose
    co-terms all carry `−c·256^k` with at least one `k ≥ 1`. -/
def gIsLadderHead (ops : DenseZModOps p) (terms : List (VarId × ZMod p))
    (v : VarId) (c : ZMod p) : Bool :=
  gIsPm1 ops c &&
    (let negc := ops.mul ops.negOne c
     terms.all (fun t => t.1 == v ||
       (let r := ops.mul t.2 negc
        r.val = 1 || gLadderPow r)) &&
     terms.any (fun t => !(t.1 == v) && gLadderPow (ops.mul t.2 negc)))

/-- The co-terms to ban when the row has a *protected* ladder head, `[]` otherwise (or on a long
    row — ladders of interest have a handful of terms and the head scan is quadratic). A protected
    head is a range-checked wire whose check turns into a recognizable digit-pair check when the
    head is solved for the tail (`L := p₀ + 256·p₁`); solving the other way smears a digit into
    every payload the head's byte checks sit in (`p₀ := L − 256·p₁`), which the byte-granularity
    passes downstream cannot see through. An unprotected head is a hub (e.g. a frame pointer
    decomposed into its word bytes) that occurrence economics already orient correctly. -/
def gLadderBan (ops : DenseZModOps p) (prot : Array Bool)
    (terms : List (VarId × ZMod p)) : List VarId :=
  if terms.length ≤ 8 && terms.any (fun t =>
      (prot[t.1.index]?).getD false && gIsLadderHead ops terms t.1 t.2) then
    (terms.filter (fun t =>
      !((prot[t.1.index]?).getD false && gIsLadderHead ops terms t.1 t.2))).map (·.1)
  else []

/-- `gPick`, preferring ladder heads: try the pick restricted to the row's protected ladder heads
    first, falling back to the unrestricted pick. -/
def gPickLadder (ops : DenseZModOps p) (occ : Array Nat) (prot : Array Bool)
    (l : DenseLinExpr p) : Option (VarId × DenseLinExpr p) :=
  match gLadderBan ops prot l.terms with
  | [] => gPick ops occ prot l (l.terms.length + 1) []
  | ban =>
    match gPick ops occ prot l (l.terms.length + 1) ban with
    | some xt => some xt
    | none => gPick ops occ prot l (l.terms.length + 1) []

/-! ## Engine state

`rows` and `sol` carry the entailment invariant (`Proofs/Gauss.lean`); everything else is
scheduling data that occurs in no theorem — a stale entry costs time, never soundness. -/

structure GSt (p : ℕ) where
  /-- Pending row per constraint slot, developed against `sol` when the scheduler reaches it. -/
  rows : Array (DenseLinExpr p)
  /-- `0` blocked · `1` pending affine row · `2` used or dead. -/
  status : Array UInt8
  /-- The solution map, kept fully back-substituted. -/
  sol : Array (Option (DenseLinExpr p))
  /-- Variable → solved variables whose row mentions it (stale-tolerant, re-checked at use). -/
  solRev : Array (Array VarId)
  /-- Variable → blocked constraints to re-walk when it is solved. -/
  watch : Array (Array Nat)
  woken : Array Bool
  /-- Adoption order; the domain of the solution map. -/
  order : Array VarId

def GSt.empty (nc nv : Nat) : GSt p :=
  { rows := Array.replicate nc ⟨zmodZeroP p, []⟩
    status := Array.replicate nc 0
    sol := Array.replicate nv none
    solRev := Array.replicate nv #[]
    watch := Array.replicate nv #[]
    woken := Array.replicate nc false
    order := #[] }

/-- Substitute `x := t` into one stored solution. -/
def gSubst1 (ops : DenseZModOps p) (s : DenseLinExpr p) (x : VarId) (t : DenseLinExpr p) :
    DenseLinExpr p :=
  denseLinSubstFWith ops s (fun z => if z = x then some t else none)

def gAddRev (t : DenseLinExpr p) (y : VarId) (solRev : Array (Array VarId)) :
    Array (Array VarId) :=
  t.terms.foldl (fun rd zc => (denseArrEnsure rd zc.1.index #[]).modify zc.1.index (·.push y))
    solRev

def gWatchOne (i : Nat) (w : Array (Array Nat)) (v : VarId) : Array (Array Nat) :=
  (denseArrEnsure w v.index #[]).modify v.index (·.push i)

/-! ### Field updates

Each helper destructures the state before writing, so the array being written is uniquely owned.
`{ S with f := g S.f }` instead leaves `S.f` shared and copies the whole array — measured at 7× on
keccak when `gAdopt` did it to `watch`. -/

def GSt.setStatus (S : GSt p) (i : Nat) (v : UInt8) : GSt p :=
  let ⟨rows, status, sol, solRev, watch, woken, order⟩ := S
  { rows := rows, status := status.setIfInBounds i v, sol := sol, solRev := solRev,
    watch := watch, woken := woken, order := order }

def GSt.setRow (S : GSt p) (i : Nat) (l : DenseLinExpr p) : GSt p :=
  let ⟨rows, status, sol, solRev, watch, woken, order⟩ := S
  { rows := rows.setIfInBounds i l, status := status, sol := sol, solRev := solRev,
    watch := watch, woken := woken, order := order }

def GSt.setPending (S : GSt p) (i : Nat) (l : DenseLinExpr p) : GSt p :=
  let ⟨rows, status, sol, solRev, watch, woken, order⟩ := S
  { rows := rows.setIfInBounds i l, status := status.setIfInBounds i 1, sol := sol,
    solRev := solRev, watch := watch, woken := woken, order := order }

def GSt.clearWoken (S : GSt p) (i : Nat) : GSt p :=
  let ⟨rows, status, sol, solRev, watch, woken, order⟩ := S
  { rows := rows, status := status, sol := sol, solRev := solRev, watch := watch,
    woken := woken.setIfInBounds i false, order := order }

def GSt.addWatch (S : GSt p) (i : Nat) (ws : List VarId) : GSt p :=
  let ⟨rows, status, sol, solRev, watch, woken, order⟩ := S
  { rows := rows, status := status, sol := sol, solRev := solRev,
    watch := ws.foldl (gWatchOne i) watch, woken := woken, order := order }

def GSt.setSol (S : GSt p) (y : VarId) (v : Option (DenseLinExpr p)) : GSt p :=
  let ⟨rows, status, sol, solRev, watch, woken, order⟩ := S
  { rows := rows, status := status, sol := sol.setIfInBounds y.index v, solRev := solRev,
    watch := watch, woken := woken, order := order }

/-- Record that the variables of `t` are now mentioned by `y`'s stored solution. -/
def GSt.pushRev (S : GSt p) (t : DenseLinExpr p) (y : VarId) : GSt p :=
  let ⟨rows, status, sol, solRev, watch, woken, order⟩ := S
  { rows := rows, status := status, sol := sol, solRev := gAddRev t y solRev,
    watch := watch, woken := woken, order := order }

def GSt.clearRev (S : GSt p) (x : VarId) : GSt p :=
  let ⟨rows, status, sol, solRev, watch, woken, order⟩ := S
  { rows := rows, status := status, sol := sol, solRev := solRev.setIfInBounds x.index #[],
    watch := watch, woken := woken, order := order }

/-- Wake every constraint watching `x`, and drop its watch list. -/
def GSt.fireWatch (S : GSt p) (x : VarId) : GSt p :=
  let ⟨rows, status, sol, solRev, watch, woken, order⟩ := S
  let ws := (watch[x.index]?).getD #[]
  { rows := rows, status := status, sol := sol, solRev := solRev,
    watch := watch.setIfInBounds x.index #[],
    woken := ws.foldl (fun w c => w.setIfInBounds c true) woken, order := order }

def GSt.pushOrder (S : GSt p) (x : VarId) : GSt p :=
  let ⟨rows, status, sol, solRev, watch, woken, order⟩ := S
  { rows := rows, status := status, sol := sol, solRev := solRev, watch := watch,
    woken := woken, order := order.push x }

/-- Develop `x := t` into the stored solutions listed in `ys`, keeping the map back-substituted. -/
def gRewriteStored (ops : DenseZModOps p) (x : VarId) (t : DenseLinExpr p) (ys : Array VarId) :
    Nat → GSt p → GSt p
  | 0, S => S
  | k + 1, S =>
      match ys[ys.size - (k + 1)]? with
      | none => gRewriteStored ops x t ys k S
      | some y =>
          match gSolFn S.sol y with
          | some s =>
              if s.mentions x then
                gRewriteStored ops x t ys k
                  ((S.setSol y (some (gSubst1 ops s x t))).pushRev t y)
              else gRewriteStored ops x t ys k S
          | none => gRewriteStored ops x t ys k S

/-- Adopt `x := t`, solved from constraint `i`: keep the stored solutions back-substituted, record
    the solution, and wake the constraints watching `x`. Pending rows are untouched — they are
    developed when the scheduler reaches them. -/
def gAdopt (ops : DenseZModOps p) (S : GSt p) (i : Nat) (x : VarId) (t : DenseLinExpr p) : GSt p :=
  -- Every field is read out once and then updated through a destructuring helper: reading a field
  -- twice inside one record update leaves it shared, and the write copies the whole array
  -- (measured: 7× on keccak).
  let ys := ((S.solRev[x.index]?).getD #[])
  let S := gRewriteStored ops x t ys ys.size (S.clearRev x)
  (((((S.setSol x (some t)).pushRev t x).fireWatch x).pushOrder x).setStatus i 2)

/-- Develop a pending row against the solution map. A row mentioning no solved variable is returned
    as it stands, which is the common case and costs no allocation. -/
def gDevelop (ops : DenseZModOps p) (sol : Array (Option (DenseLinExpr p))) (r : DenseLinExpr p) :
    DenseLinExpr p :=
  if r.terms.any (fun t => (gSolFn sol t.1).isSome) then denseLinSubstFWith ops r (gSolFn sol)
  else r

/-! ## Visiting a constraint -/

/-- Take the pivot of a developed row, or retire the slot. -/
def gTake (ops : DenseZModOps p) (occ : Array Nat) (prot : Array Bool) (S : GSt p) (i : Nat)
    (l : DenseLinExpr p) : GSt p :=
  if l.terms.isEmpty then S.setStatus i 2
  else
    match gPickLadder ops occ prot l with
    | none => S.setPending i l
    | some (x, t) => gAdopt ops S i x t

/-- Visit constraint `i`: develop its pending row and pivot, or — if a watched variable was solved
    since the last look — re-walk it from the source expression. -/
def gVisit (ops : DenseZModOps p) (occ : Array Nat) (prot : Array Bool)
    (cs : Array (DenseExpr p)) (S : GSt p) (i : Nat) : GSt p :=
  let st := (S.status[i]?).getD 2
  if st == 1 then
    match S.rows[i]? with
    | none => S
    | some r => gTake ops occ prot S i (gDevelop ops S.sol r)
  else if st == 0 && (S.woken[i]?).getD false then
    let S := S.clearWoken i
    match cs[i]? with
    | none => S
    | some c =>
        match gRoot ops S.sol c with
        | .blocked ws => S.addWatch i ws
        | .row l => gTake ops occ prot S i l
  else S

/-- One walk per constraint: a pending row, or a watch registration. -/
def gBuildGo (ops : DenseZModOps p) (cs : Array (DenseExpr p)) : Nat → GSt p → GSt p
  | 0, S => S
  | k + 1, S =>
      let i := cs.size - (k + 1)
      gBuildGo ops cs k <|
        match cs[i]? with
        | none => S
        | some c =>
            match gRoot ops S.sol c with
            | .row l => if l.terms.isEmpty then S.setStatus i 2 else S.setPending i l
            | .blocked ws => S.addWatch i ws

def gBuild (ops : DenseZModOps p) (cs : Array (DenseExpr p)) (nv : Nat) : GSt p :=
  gBuildGo ops cs cs.size (GSt.empty cs.size nv)

/-! ## Source-order scheduling (below the gate) -/

def gSweepGo (ops : DenseZModOps p) (occ : Array Nat) (prot : Array Bool)
    (cs : Array (DenseExpr p)) : Nat → GSt p → GSt p
  | 0, S => S
  | k + 1, S => gSweepGo ops occ prot cs k (gVisit ops occ prot cs S (cs.size - (k + 1)))

/-- Two source-order sweeps: every constraint once, then the woken ones. -/
def gRun (ops : DenseZModOps p) (occ : Array Nat) (prot : Array Bool)
    (cs : Array (DenseExpr p)) (nv : Nat) : GSt p :=
  gSweepGo ops occ prot cs cs.size (gSweepGo ops occ prot cs cs.size (gBuild ops cs nv))

/-! ## Fill-aware scheduling (above the gate)

Rows are held in buckets by their last known term count; a row whose developed form outgrew its
bucket is re-filed rather than pivoted, so the key needs no eager maintenance. FIFO within a bucket,
so source order breaks ties. -/

def gMaxBucket : Nat := 16

structure GQueue where
  buckets : Array (Array Nat)
  heads : Array Nat

def GQueue.empty : GQueue :=
  { buckets := Array.replicate (gMaxBucket + 1) #[], heads := Array.replicate (gMaxBucket + 1) 0 }

def GQueue.push (q : GQueue) (n : Nat) (i : Nat) : GQueue :=
  let ⟨buckets, heads⟩ := q
  { buckets := buckets.modify (min n gMaxBucket) (·.push i), heads := heads }

/-- Smallest bucket with an unconsumed entry. -/
def GQueue.next (q : GQueue) : Nat → Option Nat
  | 0 => none
  | k + 1 =>
      let b := gMaxBucket + 1 - (k + 1)
      if 0 < b && (q.heads[b]?).getD 0 < ((q.buckets[b]?).getD #[]).size then some b
      else q.next k

def GQueue.pop (q : GQueue) (b : Nat) : Option Nat × GQueue :=
  let ⟨buckets, heads⟩ := q
  let h := (heads[b]?).getD 0
  let i? := ((buckets[b]?).getD #[])[h]?
  (i?, { buckets := buckets, heads := heads.setIfInBounds b (h + 1) })

/-- Seed the queue from the pending rows, in source order. -/
def gSeedGo (S : GSt p) : Nat → GQueue → GQueue
  | 0, q => q
  | k + 1, q =>
      let i := S.status.size - (k + 1)
      gSeedGo S k <|
        if (S.status[i]?).getD 2 == 1 then
          match S.rows[i]? with
          | some l => q.push l.terms.length i
          | none => q
        else q

/-- Handle the popped row `i`: develop it, then re-file it (it outgrew bucket `b`), retire it, or
    pivot on it. -/
def gDrainAt (ops : DenseZModOps p) (occ : Array Nat) (prot : Array Bool) (S : GSt p)
    (q : GQueue) (prog : Bool) (b i : Nat) : GSt p × GQueue × Bool :=
  if (S.status[i]?).getD 2 != 1 then (S, q, prog)
  else
    match S.rows[i]? with
    | none => (S, q, prog)
    | some r =>
        let l := gDevelop ops S.sol r
        if l.terms.isEmpty then (S.setStatus i 2, q, prog)
        else if min l.terms.length gMaxBucket > b then
          (S.setRow i l, q.push l.terms.length i, prog)
        else
          let S := gTake ops occ prot S i l
          -- Progress is read back off `status` (`gTake` retires slot `i` exactly when it pivots)
          -- rather than compared against `S.order.size` taken before the call: holding a reference
          -- to `order` across `gTake` makes `gAdopt`'s `pushOrder` copy the whole array, so every
          -- adoption costs O(|order|) — 34% of the pass on sha256.
          let adopted := (S.status[i]?).getD 1 == 2
          (S, q, prog || adopted)

/-- One queue step: pop the shortest pending row and handle it. -/
def gDrainStep (ops : DenseZModOps p) (occ : Array Nat) (prot : Array Bool) (S : GSt p)
    (q : GQueue) (prog : Bool) : GSt p × GQueue × Bool :=
  match q.next (gMaxBucket + 1) with
  | none => (S, q, prog)
  | some b =>
      match q.pop b with
      | (none, q) => (S, q, prog)
      | (some i, q) => gDrainAt ops occ prot S q prog b i

/-- Drain the queue, smallest bucket first. -/
def gDrainGo (ops : DenseZModOps p) (occ : Array Nat) (prot : Array Bool) :
    Nat → GSt p → GQueue → Bool → GSt p × GQueue × Bool
  | 0, S, q, prog => (S, q, prog)
  | fuel + 1, S, q, prog =>
      match q.next (gMaxBucket + 1) with
      | none => (S, q, prog)
      | some _ =>
          match gDrainStep ops occ prot S q prog with
          | (S, q, prog) => gDrainGo ops occ prot fuel S q prog

/-- Re-walk the constraints woken since the last round, queueing the ones that turned affine. -/
def gWakeGo (ops : DenseZModOps p) (cs : Array (DenseExpr p)) :
    Nat → GSt p → GQueue → Bool → GSt p × GQueue × Bool
  | 0, S, q, prog => (S, q, prog)
  | k + 1, S, q, prog =>
      let i := cs.size - (k + 1)
      if (S.status[i]?).getD 2 == 0 && (S.woken[i]?).getD false then
        let S := S.clearWoken i
        match cs[i]? with
        | none => gWakeGo ops cs k S q prog
        | some c =>
            match gRoot ops S.sol c with
            | .blocked ws => gWakeGo ops cs k (S.addWatch i ws) q prog
            | .row l =>
                if l.terms.isEmpty then gWakeGo ops cs k (S.setStatus i 2) q prog
                else gWakeGo ops cs k (S.setPending i l) (q.push l.terms.length i) true
      else gWakeGo ops cs k S q prog

def gRoundsGo (ops : DenseZModOps p) (occ : Array Nat) (prot : Array Bool)
    (cs : Array (DenseExpr p)) : Nat → GSt p → GQueue → GSt p
  | 0, S, _ => S
  | round + 1, S, q =>
      match gDrainGo ops occ prot ((gMaxBucket + 2) * cs.size + 8) S q false with
      | (S, q, _) =>
        match gWakeGo ops cs cs.size S q false with
        | (S, q, prog) => if prog then gRoundsGo ops occ prot cs round S q else S

def gRunFill (ops : DenseZModOps p) (occ : Array Nat) (prot : Array Bool)
    (cs : Array (DenseExpr p)) (nv : Nat) : GSt p :=
  let S := gBuild ops cs nv
  gRoundsGo ops occ prot cs (cs.size + 1) S (gSeedGo S S.status.size GQueue.empty)

/-! ## Prologue and output -/

def gOccAdd (m : Array Nat) (e : DenseExpr p) : Array Nat :=
  e.foldVars (fun m x => (denseArrEnsure m x.index 0).modify x.index (· + 1)) m

/-- `denseOccurrenceMap` and `denseProtectedVars` as `VarId.index`-keyed arrays. Both are scoring
    inputs only: they occur in no theorem. -/
def gPrepare (bs : BusSemantics p) (d : DenseConstraintSystem p) : Array Nat × Array Bool :=
  let occ := d.busInteractions.foldl
    (fun m bi => bi.payload.foldl gOccAdd (gOccAdd m bi.multiplicity))
    (d.algebraicConstraints.foldl gOccAdd #[])
  let prot := d.busInteractions.foldl (init := Array.replicate occ.size false) fun s bi =>
    if bs.isStateful bi.busId then s
    else bi.payload.foldl
      (fun s e => match e with | .var x => s.setIfInBounds x.index true | _ => s) s
  (occ, prot)

/-- The solution map as a `VarId.index`-keyed array of dense expressions. -/
def gOutGo (S : GSt p) : Nat → Array (Option (DenseExpr p)) → Array (Option (DenseExpr p))
  | 0, out => out
  | k + 1, out =>
      gOutGo S k <|
        match S.order[S.order.size - (k + 1)]? with
        | none => out
        | some x =>
            match gSolFn S.sol x with
            | some l => out.setIfInBounds x.index (some l.toExpr)
            | none => out

def gOutFn (out : Array (Option (DenseExpr p))) : VarId → Option (DenseExpr p) :=
  fun i => (out[i.index]?).getD none

/-- Solve the system: the prologue, then whichever scheduler the gate selects. -/
def gSolveSystem (bs : BusSemantics p) (d : DenseConstraintSystem p) : GSt p :=
  let ops : DenseZModOps p := denseZModOps
  let cs := d.algebraicConstraints.toArray
  match gPrepare bs d with
  | (occ, prot) =>
      if cs.size < denseMarkowitzMinRows then gRun ops occ prot cs occ.size
      else gRunFill ops occ prot cs occ.size

/-- The solution map as a `VarId.index`-keyed array; `sol` was sized to the variable bound. -/
def gOutOf (S : GSt p) : Array (Option (DenseExpr p)) :=
  gOutGo S S.order.size (Array.replicate S.sol.size none)

/-- Batch linear (Gauss) elimination. From a constraint like `x - 2*y - 3 = 0` it derives the
    assignment `x := 2*y + 3`, choosing pivots by occurrence-weighted duplication cost. -/
def denseGaussElimF (bs : BusSemantics p) (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  let S := gSolveSystem bs d
  if S.order.isEmpty then d else d.substF (gOutFn (gOutOf S))

end ApcOptimizer.Dense
