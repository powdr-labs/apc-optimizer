import ApcOptimizer.Implementation.OptimizerPasses.Bridge

set_option autoImplicit false

/-! # Disconnected-component removal

A *disconnected component* is a set of algebraic constraints and stateless bus interactions whose
variables never touch a stateful bus interaction. The pass finds one by union-find over the
co-occurrence hypergraph, tries the all-zero witness, and drops the component only if the witness
certifies it at run time (the same re-check `guardDegree` uses). Correctness is in
`Proofs/DisconnectedComponent.lean`, and is generic in the removable set: nothing below the
`denseDropGuarded` line is ever reasoned about. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Union-find over variable indices

Each item (constraint or interaction) is a hyperedge: unioning its variables makes the connected
component of the co-occurrence graph a single find away, so an item's whole `all disconnected` test
collapses to one array read. `dcUnion` attaches the larger root to the smaller, which keeps
`par[i] ≤ i` — that is what lets `dcFind` recurse on the strictly decreasing index (no fuel, no
invariant to carry) and what makes `dcFlatten` a single increasing sweep. A violated invariant would
cost precision, never soundness. -/

/-- Grow the parent array so that index `n - 1` exists, each new slot its own root. -/
def dcEnsure (par : Array Nat) (n : Nat) : Array Nat :=
  if _h : par.size < n then dcEnsure (par.push par.size) n else par
termination_by n - par.size
decreasing_by simp only [Array.size_push]; omega

/-- Find with path halving. -/
def dcFind (par : Array Nat) (x : Nat) : Array Nat × Nat :=
  let px := par.getD x x
  if _hx : px < x then
    let g := par.getD px px
    if _hg : g < px then dcFind (par.set! x g) g else (par, px)
  else (par, x)
termination_by x
decreasing_by exact Nat.lt_trans _hg _hx

def dcUnion (par : Array Nat) (a b : Nat) : Array Nat :=
  let (par, ra) := dcFind par a
  let (par, rb) := dcFind par b
  if ra == rb then par else if ra < rb then par.set! rb ra else par.set! ra rb

/-- `par[i] ≤ i`, so scanning upward finds every entry's parent already flattened: one pass makes
    every entry point straight at its root. -/
def dcFlatten (par : Array Nat) (x : Nat) : Array Nat :=
  if h : x < par.size then
    let px := par.getD x x
    dcFlatten (par.set! x (par.getD px px)) (x + 1)
  else par
termination_by par.size - x
decreasing_by simp only [Array.set!, Array.size_setIfInBounds]; omega

/-! ## Building the partition

The second component threaded through the walks is the item's *shifted* representative variable:
`0` for a variable-free item, `i + 1` for variable index `i`. Every argument is threaded linearly so
the parent array stays uniquely owned. -/

/-- Union every variable of `e` into the item's representative, which is maintained as the *root* of
    the item's component so each occurrence costs one find rather than the two a bare
    `dcUnion rep i` would. -/
def dcUnionExpr : DenseExpr p → Array Nat × Nat → Array Nat × Nat
  | .const _, st => st
  | .var i, (par, rep) =>
      let par := if i.index < par.size then par else dcEnsure par (i.index + 1)
      let (par, ri) := dcFind par i.index
      if rep == 0 then (par, ri + 1)
      else
        let r := rep - 1
        if ri == r then (par, rep)
        else if ri < r then (par.set! r ri, ri + 1) else (par.set! ri r, rep)
  | .add a b, st => dcUnionExpr b (dcUnionExpr a st)
  | .mul a b, st => dcUnionExpr b (dcUnionExpr a st)

def dcUnionBI (bi : BusInteraction (DenseExpr p)) (st : Array Nat × Nat) : Array Nat × Nat :=
  bi.payload.foldl (fun st e => dcUnionExpr e st) (dcUnionExpr bi.multiplicity st)

def dcBuildCs (par : Array Nat) (reps : Array Nat) :
    List (DenseExpr p) → Array Nat × Array Nat
  | [] => (par, reps)
  | c :: rest =>
      let (par, rep) := dcUnionExpr c (par, 0)
      dcBuildCs par (reps.push rep) rest

/-- Interactions are unioned like constraints, and every stateful one additionally joins one
    designated *stateful* component — whose members are exactly the variables the old breadth-first
    closure reached from the stateful seeds. -/
def dcBuildBis (bs : BusSemantics p) (par : Array Nat) (reps : Array Nat) (stRep : Nat) :
    List (BusInteraction (DenseExpr p)) → Array Nat × Array Nat × Nat
  | [] => (par, reps, stRep)
  | bi :: rest =>
      let (par, rep) := dcUnionBI bi (par, 0)
      if bs.isStateful bi.busId && rep != 0 then
        if stRep == 0 then dcBuildBis bs par (reps.push rep) rep rest
        else dcBuildBis bs (dcUnion par (stRep - 1) (rep - 1)) (reps.push rep) stRep rest
      else dcBuildBis bs par (reps.push rep) stRep rest

/-! ## The all-zero witness -/

/-- `e.eval (fun _ => 0)`, dictionary-free (`Encoding.lean`'s primitives), so no `CommRing (ZMod p)`
    chain is built per item. -/
def denseEvalZero : DenseExpr p → ZMod p
  | .const n => n
  | .var _ => zmodZeroP p
  | .add a b => zmodAddP (denseEvalZero a) (denseEvalZero b)
  | .mul a b => zmodMulP (denseEvalZero a) (denseEvalZero b)

def denseBIEvalZero (bi : BusInteraction (DenseExpr p)) : BusInteraction (ZMod p) :=
  { busId := bi.busId, multiplicity := denseEvalZero bi.multiplicity,
    payload := bi.payload.map denseEvalZero }

/-! ## Bad components

A disconnected item the all-zero witness fails on poisons its whole component; marking its root is
the mark-side of what used to be a second breadth-first closure. -/

def dcMarkBadCs (par : Array Nat) (connRoot : Nat) (reps : Array Nat) (i : Nat) (bad : Array Bool) :
    List (DenseExpr p) → Array Bool
  | [] => bad
  | c :: rest =>
      let rep := reps.getD i 0
      if rep == 0 then dcMarkBadCs par connRoot reps (i + 1) bad rest
      else
        let r := par.getD (rep - 1) connRoot
        if r == connRoot || zmodIsZero (denseEvalZero c) then
          dcMarkBadCs par connRoot reps (i + 1) bad rest
        else dcMarkBadCs par connRoot reps (i + 1) (bad.set! r true) rest

def dcMarkBadBis (bs : BusSemantics p) (facts : BusFacts p bs) (par : Array Nat) (connRoot : Nat)
    (reps : Array Nat) (i : Nat) (bad : Array Bool) :
    List (BusInteraction (DenseExpr p)) → Array Bool
  | [] => bad
  | bi :: rest =>
      let rep := reps.getD i 0
      if rep == 0 || bs.isStateful bi.busId then
        dcMarkBadBis bs facts par connRoot reps (i + 1) bad rest
      else
        let r := par.getD (rep - 1) connRoot
        if r == connRoot || facts.acceptsDec (denseBIEvalZero bi) then
          dcMarkBadBis bs facts par connRoot reps (i + 1) bad rest
        else dcMarkBadBis bs facts par connRoot reps (i + 1) (bad.set! r true) rest

/-- Is any item's component removable? A pure array scan over the item representatives, run before
    the per-variable table is built so a system with nothing to drop costs no further work. -/
def dcAnyRemovable (par : Array Nat) (connRoot : Nat) (bad : Array Bool) (reps : Array Nat)
    (i : Nat) : Bool :=
  if h : i < reps.size then
    let rep := reps.getD i 0
    if rep != 0 then
      let r := par.getD (rep - 1) connRoot
      if r != connRoot && !bad.getD r false then true
      else dcAnyRemovable par connRoot bad reps (i + 1)
    else dcAnyRemovable par connRoot bad reps (i + 1)
  else false
termination_by reps.size - i

/-- The per-variable removable flags: neither in the stateful component nor in a poisoned one. -/
def dcRemVars (par : Array Nat) (connRoot : Nat) (bad : Array Bool) (x : Nat) (out : Array Bool) :
    Array Bool :=
  if h : x < par.size then
    let r := par.getD x x
    dcRemVars par connRoot bad (x + 1) (out.set! x (r != connRoot && !bad.getD r false))
  else out
termination_by par.size - x
decreasing_by omega

/-- The removable variables, indexed by `VarId.index`; `#[]` when nothing is removable. Returned as
    data, not as a `VarId → Bool` predicate: a function-valued def is eta-expanded to maximal arity,
    which would rerun the whole search on every application (arity-expansion trap). The predicate is
    built once at the use site in `denseDisconnectedF`. Treated opaquely by the correctness proof. -/
def denseRemovableVars (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : Array Bool :=
  let (par, reps) := dcBuildCs #[] #[] d.algebraicConstraints
  let (par, reps, stRep) := dcBuildBis bs par reps 0 d.busInteractions
  let par := dcFlatten par 0
  let n := par.size
  let connRoot := if stRep == 0 then n else par.getD (stRep - 1) n
  let bad := dcMarkBadCs par connRoot reps 0 (Array.replicate n false) d.algebraicConstraints
  let bad := dcMarkBadBis bs facts par connRoot reps d.algebraicConstraints.length bad
    d.busInteractions
  if dcAnyRemovable par connRoot bad reps 0 then
    dcRemVars par connRoot bad 0 (Array.replicate n false)
  else #[]

/-! ## Keep predicates -/

/-- Keep a constraint unless *all* of its variables are removable (and it has at least one). -/
def denseKeepConWith (remV : VarId → Bool) (c : DenseExpr p) : Bool :=
  c.vars.isEmpty || !(c.vars.all remV)

/-- Keep an interaction if it is stateful or has a non-removable variable (or no variables). -/
def denseKeepBiWith (bs : BusSemantics p) (remV : VarId → Bool)
    (bi : BusInteraction (DenseExpr p)) : Bool :=
  bs.isStateful bi.busId || (denseBIVars bi).isEmpty || !((denseBIVars bi).all remV)

/-! ## The guarded drop -/

/-- The run-time re-check: the induced partition is a genuine drop, the all-zero witness satisfies
    every removed constraint and non-violates every removed interaction, and every kept item uses
    only non-removable variables. Stated for an arbitrary `remV`. -/
def denseDropCheck (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p)
    (remV : VarId → Bool) : Bool :=
  (d.algebraicConstraints.any (fun c => !denseKeepConWith remV c) ||
    d.busInteractions.any (fun bi => !denseKeepBiWith bs remV bi)) &&
  d.algebraicConstraints.all (fun c => denseKeepConWith remV c || decide (c.eval (fun _ => 0) = 0)) &&
  d.busInteractions.all (fun bi =>
    denseKeepBiWith bs remV bi ||
      facts.acceptsDec (denseBIEval bi (fun _ => 0))) &&
  d.algebraicConstraints.all (fun c =>
    !denseKeepConWith remV c || c.vars.all (fun x => !remV x)) &&
  d.busInteractions.all (fun bi =>
    !denseKeepBiWith bs remV bi || (denseBIVars bi).all (fun x => !remV x))

/-! ### The fused re-check

`denseDropCheck` and the filter below it read `DenseExpr.vars` five times per item, each read
allocating a cons per occurrence. Two allocation-free walks answer everything they ask, and
`dcAnyVar` alone settles the common case: an item with no removable variable is kept *and* its
kept-side obligation (`vars.all (!remV)`) is exactly the same walk's negation. -/

/-- `e.vars.any f`, without materialising `e.vars`. -/
def dcAnyVar (f : VarId → Bool) : DenseExpr p → Bool
  | .const _ => false
  | .var i => f i
  | .add a b => dcAnyVar f a || dcAnyVar f b
  | .mul a b => dcAnyVar f a || dcAnyVar f b

/-- `e.vars.all f`, without materialising `e.vars`. -/
def dcAllVar (f : VarId → Bool) : DenseExpr p → Bool
  | .const _ => true
  | .var i => f i
  | .add a b => dcAllVar f a && dcAllVar f b
  | .mul a b => dcAllVar f a && dcAllVar f b

def dcAnyVarBI (f : VarId → Bool) (bi : BusInteraction (DenseExpr p)) : Bool :=
  dcAnyVar f bi.multiplicity || bi.payload.any (dcAnyVar f)

def dcAllVarBI (f : VarId → Bool) (bi : BusInteraction (DenseExpr p)) : Bool :=
  dcAllVar f bi.multiplicity && bi.payload.all (dcAllVar f)

/-- The keep flags of the constraint list, or `none` if an obligation of `denseDropCheck` fails; the
    `Bool` reports whether anything is dropped. -/
def dcCheckCs (remV : VarId → Bool) (keep : Array Bool) (dropped : Bool) :
    List (DenseExpr p) → Option (Array Bool × Bool)
  | [] => some (keep, dropped)
  | c :: rest =>
      if dcAnyVar remV c then
        if dcAllVar remV c && zmodIsZero (denseEvalZero c) then
          dcCheckCs remV (keep.push false) true rest
        else none
      else dcCheckCs remV (keep.push true) dropped rest

def dcCheckBis (bs : BusSemantics p) (facts : BusFacts p bs) (remV : VarId → Bool)
    (keep : Array Bool) (dropped : Bool) :
    List (BusInteraction (DenseExpr p)) → Option (Array Bool × Bool)
  | [] => some (keep, dropped)
  | bi :: rest =>
      if dcAnyVarBI remV bi then
        if !bs.isStateful bi.busId && dcAllVarBI remV bi &&
            facts.acceptsDec (denseBIEvalZero bi) then
          dcCheckBis bs facts remV (keep.push false) true rest
        else none
      else dcCheckBis bs facts remV (keep.push true) dropped rest

def dcFilterIdx {α : Type} (keep : Array Bool) (i : Nat) : List α → List α
  | [] => []
  | a :: rest =>
      if keep.getD i true then a :: dcFilterIdx keep (i + 1) rest else dcFilterIdx keep (i + 1) rest

/-- `denseDropGuarded`'s runtime twin: the two sweeps decide the whole re-check and the keep flags
    they produce drive the filter. When an obligation fails this still walks the rest of the list
    where `denseDropCheck`'s `&&` short-circuits — the *value* is the same (`d` either way), which
    is what the equality below has to say. -/
def denseDropGuardedFast (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (remV : VarId → Bool) : DenseConstraintSystem p :=
  match dcCheckCs remV #[] false d.algebraicConstraints with
  | none => d
  | some (keepC, dropC) =>
    match dcCheckBis bs facts remV #[] false d.busInteractions with
    | none => d
    | some (keepB, dropB) =>
      if dropC || dropB then
        { algebraicConstraints := dcFilterIdx keepC 0 d.algebraicConstraints,
          busInteractions := dcFilterIdx keepB 0 d.busInteractions }
      else d

/-- Drop the removable component if the re-check passes; otherwise the identity. Stated for an
    arbitrary `remV` so the correctness proof is generic in the connectivity search. -/
def denseDropGuarded (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p)
    (remV : VarId → Bool) : DenseConstraintSystem p :=
  if denseDropCheck bs facts d remV then
    { algebraicConstraints := d.algebraicConstraints.filter (denseKeepConWith remV),
      busInteractions := d.busInteractions.filter (denseKeepBiWith bs remV) }
  else d

/-! ### The twin computes the same value

The walks and the all-zero witness are pointwise equalities; the sweeps are characterised against
`denseDropCheck`'s own conjuncts. The one gap the equality has to bridge is short-circuiting: a
failed obligation stops `denseDropCheck`'s `&&` early where `dcCheckCs` keeps walking. Both yield
`d`, which is all the equality claims. -/

theorem dcAnyVar_eq (f : VarId → Bool) (e : DenseExpr p) : dcAnyVar f e = e.vars.any f := by
  induction e with
  | const n => rfl
  | var i => simp [dcAnyVar, DenseExpr.vars]
  | add a b iha ihb => simp [dcAnyVar, DenseExpr.vars, iha, ihb]
  | mul a b iha ihb => simp [dcAnyVar, DenseExpr.vars, iha, ihb]

theorem dcAllVar_eq (f : VarId → Bool) (e : DenseExpr p) : dcAllVar f e = e.vars.all f := by
  induction e with
  | const n => rfl
  | var i => simp [dcAllVar, DenseExpr.vars]
  | add a b iha ihb => simp [dcAllVar, DenseExpr.vars, iha, ihb]
  | mul a b iha ihb => simp [dcAllVar, DenseExpr.vars, iha, ihb]

theorem dcAnyVarBI_eq (f : VarId → Bool) (bi : BusInteraction (DenseExpr p)) :
    dcAnyVarBI f bi = (denseBIVars bi).any f := by
  have hv : (dcAnyVar f : DenseExpr p → Bool) = fun e => e.vars.any f :=
    funext (dcAnyVar_eq f)
  simp [dcAnyVarBI, denseBIVars, hv]

theorem dcAllVarBI_eq (f : VarId → Bool) (bi : BusInteraction (DenseExpr p)) :
    dcAllVarBI f bi = (denseBIVars bi).all f := by
  have hv : (dcAllVar f : DenseExpr p → Bool) = fun e => e.vars.all f :=
    funext (dcAllVar_eq f)
  simp [dcAllVarBI, denseBIVars, hv]

theorem denseEvalZero_eq (e : DenseExpr p) : denseEvalZero e = e.eval (fun _ => 0) := by
  induction e with
  | const n => rfl
  | var i => simp [denseEvalZero, DenseExpr.eval]
  | add a b iha ihb => simp [denseEvalZero, DenseExpr.eval, iha, ihb]
  | mul a b iha ihb => simp [denseEvalZero, DenseExpr.eval, iha, ihb]

theorem denseBIEvalZero_eq (bi : BusInteraction (DenseExpr p)) :
    denseBIEvalZero bi = denseBIEval bi (fun _ => 0) := by
  have hv : (denseEvalZero : DenseExpr p → ZMod p) = fun e => e.eval (fun _ => 0) :=
    funext denseEvalZero_eq
  simp [denseBIEvalZero, denseBIEval, hv]

/-! The two walks decide the keep predicate and both of `denseDropCheck`'s per-item obligations: no
removable variable keeps the item *and* discharges its kept-side obligation, and a removable
variable leaves the item removable only when every variable is. -/

theorem dcAllNot (f : VarId → Bool) (l : List VarId) : l.all (fun x => !f x) = !l.any f := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [ih]

theorem dcKeepOfNotAny (f : VarId → Bool) (l : List VarId) (h : l.any f = false) :
    (l.isEmpty || !(l.all f)) = true := by
  cases l with
  | nil => rfl
  | cons a t =>
    rw [List.any_cons, Bool.or_eq_false_iff] at h
    simp [h.1]

/-- The one array fact the sweeps need: a push is an append of a singleton. -/
theorem dcPushAppend (a : Array Bool) (b : Bool) (l : List Bool) :
    a.push b ++ l.toArray = a ++ (b :: l).toArray := by
  apply Array.ext'; simp

theorem dcCheckCs_spec (remV : VarId → Bool) (L : List (DenseExpr p)) :
    ∀ (keep : Array Bool) (dropped : Bool),
    dcCheckCs remV keep dropped L =
      if L.all (fun c => denseKeepConWith remV c || decide (c.eval (fun _ => 0) = 0)) &&
         L.all (fun c => !denseKeepConWith remV c || c.vars.all (fun x => !remV x))
      then some (keep ++ (L.map (denseKeepConWith remV)).toArray,
                 dropped || L.any (fun c => !denseKeepConWith remV c))
      else none := by
  induction L with
  | nil => intro keep dropped; simp [dcCheckCs]
  | cons c rest ih =>
    intro keep dropped
    have hzc : zmodIsZero (denseEvalZero c) = decide (c.eval (fun _ => 0) = 0) := by
      rw [zmodIsZero_eq, denseEvalZero_eq]
    rw [dcCheckCs, dcAnyVar_eq, dcAllVar_eq, hzc]
    cases hany : c.vars.any remV with
    | false =>
      have hkeep : denseKeepConWith remV c = true := dcKeepOfNotAny remV c.vars hany
      have hobl : c.vars.all (fun x => !remV x) = true := by rw [dcAllNot, hany]; rfl
      rw [if_neg (by simp), ih]
      simp [hkeep, hobl]
    | true =>
      have hne : c.vars.isEmpty = false := by
        cases hc : c.vars with
        | nil => rw [hc] at hany; simp at hany
        | cons _ _ => rfl
      cases hall : c.vars.all remV with
      | false =>
        have hkeep : denseKeepConWith remV c = true := by simp [denseKeepConWith, hall]
        have hobl : c.vars.all (fun x => !remV x) = false := by rw [dcAllNot, hany]; rfl
        simp [hkeep, hobl]
      | true =>
        have hkeep : denseKeepConWith remV c = false := by
          simp [denseKeepConWith, hall, hne]
        cases hz : decide (c.eval (fun _ => 0) = 0) with
        | false => simp [hkeep, hz]
        | true =>
          rw [if_pos rfl, ih]
          simp [hkeep, hz]

theorem dcCheckBis_spec (bs : BusSemantics p) (facts : BusFacts p bs) (remV : VarId → Bool)
    (L : List (BusInteraction (DenseExpr p))) :
    ∀ (keep : Array Bool) (dropped : Bool),
    dcCheckBis bs facts remV keep dropped L =
      if L.all (fun bi => denseKeepBiWith bs remV bi ||
            facts.acceptsDec (denseBIEval bi (fun _ => 0))) &&
         L.all (fun bi => !denseKeepBiWith bs remV bi ||
            (denseBIVars bi).all (fun x => !remV x))
      then some (keep ++ (L.map (denseKeepBiWith bs remV)).toArray,
                 dropped || L.any (fun bi => !denseKeepBiWith bs remV bi))
      else none := by
  induction L with
  | nil => intro keep dropped; simp [dcCheckBis]
  | cons bi rest ih =>
    intro keep dropped
    rw [dcCheckBis, dcAnyVarBI_eq, dcAllVarBI_eq, denseBIEvalZero_eq]
    cases hany : (denseBIVars bi).any remV with
    | false =>
      have hkeep : denseKeepBiWith bs remV bi = true := by
        rw [denseKeepBiWith, Bool.or_assoc]
        exact Bool.or_eq_true_iff.2 (Or.inr (dcKeepOfNotAny remV (denseBIVars bi) hany))
      have hobl : (denseBIVars bi).all (fun x => !remV x) = true := by rw [dcAllNot, hany]; rfl
      rw [if_neg (by simp), ih]
      simp [hkeep, hobl]
    | true =>
      have hobl : (denseBIVars bi).all (fun x => !remV x) = false := by rw [dcAllNot, hany]; rfl
      have hne : (denseBIVars bi).isEmpty = false := by
        cases hc : denseBIVars bi with
        | nil => rw [hc] at hany; simp at hany
        | cons _ _ => rfl
      cases hst : bs.isStateful bi.busId with
      | true =>
        have hkeep : denseKeepBiWith bs remV bi = true := by simp [denseKeepBiWith, hst]
        simp [hkeep, hobl]
      | false =>
        cases hall : (denseBIVars bi).all remV with
        | false =>
          have hkeep : denseKeepBiWith bs remV bi = true := by simp [denseKeepBiWith, hall]
          simp [hkeep, hobl]
        | true =>
          have hkeep : denseKeepBiWith bs remV bi = false := by
            simp [denseKeepBiWith, hall, hne, hst]
          cases hz : facts.acceptsDec (denseBIEval bi (fun _ => 0)) with
          | false => simp [hkeep, hz]
          | true =>
            rw [if_pos rfl, ih]
            simp [hkeep, hz]

theorem dcFilterIdx_prefix {α : Type} (f : α → Bool) (L : List α) :
    ∀ (pre : Array Bool), dcFilterIdx (pre ++ (L.map f).toArray) pre.size L = L.filter f := by
  induction L with
  | nil => intro pre; rfl
  | cons a rest ih =>
    intro pre
    have hhd : (pre ++ ((a :: rest).map f).toArray).getD pre.size true = f a := by
      simp [Array.getD]
    rw [dcFilterIdx, hhd]
    have hsz : (pre.push (f a)).size = pre.size + 1 := by simp
    have hkeep : pre ++ ((a :: rest).map f).toArray
        = pre.push (f a) ++ (rest.map f).toArray := by
      rw [dcPushAppend]; rfl
    rw [hkeep, ← hsz, ih (pre.push (f a))]
    cases hfa : f a <;> simp [hfa]

theorem dcFilterIdx_eq {α : Type} (f : α → Bool) (L : List α) :
    dcFilterIdx (L.map f).toArray 0 L = L.filter f := by
  have h := dcFilterIdx_prefix f L #[]
  simpa using h

def denseDropCheckFast (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (remV : VarId → Bool) : Bool :=
  match dcCheckCs remV #[] false d.algebraicConstraints with
  | none => false
  | some (_, dropC) =>
    match dcCheckBis bs facts remV #[] false d.busInteractions with
    | none => false
    | some (_, dropB) => dropC || dropB
@[csimp] theorem denseDropCheck_eq_fast : @denseDropCheck = @denseDropCheckFast := by
  funext p bs facts d remV
  simp only [denseDropCheckFast, dcCheckCs_spec, dcCheckBis_spec]
  split_ifs <;> apply Bool.eq_iff_iff.mpr <;>
    simp_all only [denseDropCheck, Bool.and_eq_true, Bool.or_eq_true, Bool.false_or] <;> tauto

@[csimp] theorem denseDropGuarded_eq_fast : @denseDropGuarded = @denseDropGuardedFast := by
  funext q bs facts d remV
  rw [denseDropGuardedFast, dcCheckCs_spec, dcCheckBis_spec, denseDropGuarded, denseDropCheck]
  cases hB : d.algebraicConstraints.all
      (fun c => denseKeepConWith remV c || decide (c.eval (fun _ => 0) = 0)) with
  | false => simp
  | true =>
    cases hD : d.algebraicConstraints.all
        (fun c => !denseKeepConWith remV c || c.vars.all (fun x => !remV x)) with
    | false => simp
    | true =>
      cases hC : d.busInteractions.all (fun bi => denseKeepBiWith bs remV bi ||
          facts.acceptsDec (denseBIEval bi (fun _ => 0))) with
      | false => simp
      | true =>
        cases hE : d.busInteractions.all (fun bi => !denseKeepBiWith bs remV bi ||
            (denseBIVars bi).all (fun x => !remV x)) with
        | false => simp
        | true =>
          simp only [Bool.and_true, if_true, Bool.false_or]
          split_ifs with h
          · simp [dcFilterIdx_eq]
          · rfl

/-- `#[]` means nothing is removable, so the re-check is skipped entirely. -/
def denseDropWithTable (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p)
    (rem : Array Bool) : DenseConstraintSystem p :=
  if rem.isEmpty then d else denseDropGuarded bs facts d (fun x => rem.getD x.index false)

/-- Finds a set of constraints and stateless interactions whose variables never reach a stateful
    bus, and — if the all-zero witness satisfies them (re-checked at run time by `denseDropCheck`) —
    drops the whole component. For a system whose only link to a memory interaction is through `y`,
    a constraint `x * x = x` on an otherwise unused `x` is dropped with `x := 0`. -/
def denseDisconnectedF (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    DenseConstraintSystem p :=
  denseDropWithTable bs facts d (denseRemovableVars bs facts d)

def denseDropHints (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p)
    (remV : VarId → Bool) : RecoveryMap p :=
  if denseDropCheck bs facts d remV then
    .ofFn (fun i => if remV i then .const 0 else .var i)
  else .identity

def denseDisconnectedHints (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : RecoveryMap p :=
  let rem := denseRemovableVars bs facts d
  if rem.isEmpty then .identity
  else denseDropHints bs facts d (fun x => rem.getD x.index false)

def denseDisconnectedWithHints (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : DenseConstraintSystem p × RecoveryMap p :=
  let rem := denseRemovableVars bs facts d
  (denseDropWithTable bs facts d rem,
    if rem.isEmpty then .identity else denseDropHints bs facts d (fun x => rem.getD x.index false))

end ApcOptimizer.Dense
