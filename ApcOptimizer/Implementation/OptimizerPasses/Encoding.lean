import ApcOptimizer.Implementation.OptimizerPasses.Registry

set_option autoImplicit false

/-! # Dense data model and encode/decode

Implementation-only dense counterparts of the spec's circuit values, with `VarId` leaves. `decode`
resolves IDs through a registry; `encode` threads a registry left-to-right, registering each
variable occurrence in one traversal. The correspondence results (`decode ∘ encode = id`,
extension agreement, degree/eval/vars preservation) are what the pipeline's edge encode/decode and
`DensePassCorrect.lift` ride on. A single coverage invariant is threaded rather than a per-node
proof. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Dictionary-free field access

`p` is a runtime value, so `ZMod p`'s `CommRing` instance is never a closed term: a function that
merely *mentions* `0` or `1` rebuilds `ZMod.commRing p` plus 3–5 projections at its own entry, and
Lean floats that construction ahead of every branch test.

`ZMod.commRing` mirrors `ZMod`'s own `Nat.casesOn` split (`Mathlib/Data/ZMod/Defs.lean`), so every
operation *is* the corresponding `Int`/`Fin` primitive underneath — reaching it through the instance
is what costs. Casing on `p` directly, in the shape `ZMod.val` itself uses, gets the primitive with
no dictionary. Likewise `ZMod.val` is a bare `Fin.val` / `Int.natAbs` projection, so a test routed
through it builds nothing. -/

def zmodAddP : ∀ {p : ℕ}, ZMod p → ZMod p → ZMod p
  | 0 => Int.add
  | _ + 1 => Fin.add

def zmodMulP : ∀ {p : ℕ}, ZMod p → ZMod p → ZMod p
  | 0 => Int.mul
  | _ + 1 => Fin.mul

def zmodZeroP : ∀ (p : ℕ), ZMod p
  | 0 => (0 : ℤ)
  | n + 1 => (⟨0, Nat.succ_pos n⟩ : Fin (n + 1))

def zmodOneP : ∀ (p : ℕ), ZMod p
  | 0 => (1 : ℤ)
  | n + 1 => (⟨1 % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩ : Fin (n + 1))

/-- `-1`, i.e. `p - 1`; at `p = 1` that is `0`, which is correct in the trivial ring. -/
def zmodNegOneP : ∀ (p : ℕ), ZMod p
  | 0 => (-1 : ℤ)
  | n + 1 => (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1))

def zmodNegP : ∀ {p : ℕ}, ZMod p → ZMod p
  | 0 => Int.neg
  | n + 1 => fun a => (Neg.neg (α := Fin (n + 1)) a : Fin (n + 1))

/-- `c = 0`, dictionary-free: `val` sends `0` to `0` and nothing else, at every `p`
    (`ZMod.val_eq_zero`). -/
def zmodIsZero (c : ZMod p) : Bool := c.val == 0

/-- `c = 1` at `p = 0`, where `val = Int.natAbs` identifies `1` with `-1`. Kept in its own function
    so its dictionary stays off `zmodIsOne`'s entry; unreachable at runtime (`p` is a prime). -/
def zmodIsOneSlow (c : ZMod p) : Bool := decide (c = 1)

/-- `c = 1`, dictionary-free for `p ≠ 0`: `(1 : ZMod p).val = 1 % p` (`ZMod.val_one_eq_one_mod`). -/
def zmodIsOne (c : ZMod p) : Bool :=
  if p = 0 then zmodIsOneSlow c else c.val == 1 % p


/-- `a + b` behind a call, so a caller's constant/constant branch does not pull the `CommRing` chain
    to every entry to that caller. -/
def zmodAdd (a b : ZMod p) : ZMod p := zmodAddP a b

/-- `a * b` behind a call; see `zmodAdd`. -/
def zmodMul (a b : ZMod p) : ZMod p := zmodMulP a b

/-! ### Bridge lemmas

These are the whole proof surface of the change: each primitive is `@[simp]`-normalized back to the
`ZMod` operation it implements, so proofs that reason about the definitions never see the primitive.
The `…P` value lemmas are the same five obligations as `denseZModOps`' `_eq` fields. -/

@[simp] theorem zmodIsZero_eq (c : ZMod p) : zmodIsZero c = decide (c = 0) := by
  unfold zmodIsZero
  by_cases h : c = 0
  · simp [h]
  · simp [h, (ZMod.val_eq_zero c).not.2 h]

/-- `ZMod.commRing`'s operations are the `Int`/`Fin` ones by definition, so each primitive matches
    its ring operation by cases on `p`. -/
@[simp] theorem zmodAddP_eq (a b : ZMod p) : zmodAddP a b = a + b := by
  cases p with | zero => rfl | succ n => rfl

@[simp] theorem zmodMulP_eq (a b : ZMod p) : zmodMulP a b = a * b := by
  cases p with | zero => rfl | succ n => rfl

@[simp] theorem zmodZeroP_eq : zmodZeroP p = 0 := by
  cases p with | zero => rfl | succ n => rfl

@[simp] theorem zmodOneP_eq : zmodOneP p = 1 := by
  cases p with | zero => rfl | succ n => rfl

@[simp] theorem zmodNegP_eq (a : ZMod p) : zmodNegP a = -a := by
  cases p with | zero => rfl | succ n => rfl

@[simp] theorem zmodNegOneP_eq : zmodNegOneP p = -1 := by
  cases p with
  | zero => rfl
  | succ n =>
    refine ZMod.val_injective (n + 1) ?_
    rw [ZMod.val_neg_one]
    rfl

@[simp] theorem zmodAdd_eq (a b : ZMod p) : zmodAdd a b = a + b := zmodAddP_eq a b
@[simp] theorem zmodMul_eq (a b : ZMod p) : zmodMul a b = a * b := zmodMulP_eq a b

/-- `val` is injective for `p ≠ 0`, which is what makes the `= 1` / `= -1` tests sound; at `p = 0`
    (`val = Int.natAbs`, which merges `1` and `-1`) the slow path is taken instead. -/
@[simp] theorem zmodIsOne_eq (c : ZMod p) : zmodIsOne c = decide (c = 1) := by
  unfold zmodIsOne
  cases p with
  | zero => simp [zmodIsOneSlow]
  | succ n =>
    have hone : (1 : ZMod (n + 1)).val = 1 % (n + 1) := ZMod.val_one_eq_one_mod (n + 1)
    simp only [Nat.succ_ne_zero, if_false]
    by_cases h : c = 1
    · simp [h, hone]
    · simpa [h] using fun hv => h (ZMod.val_injective (n + 1) (by rw [hv, hone]))

/-! ## Dense types -/

/-- A dense arithmetic expression: the spec `OutputExpression` with `VarId` leaves. -/
inductive DenseExpr (p : ℕ) where
  | const (n : ZMod p)
  | var (i : VarId)
  | add (a b : DenseExpr p)
  | mul (a b : DenseExpr p)
deriving Repr, DecidableEq

/-- A dense computation method: the spec `ComputationMethod` over `DenseExpr`. -/
inductive DenseComputationMethod (p : ℕ) where
  | const (c : ZMod p)
  | quotientOrZero (num den : DenseExpr p)
  | ifEqZero (cond : DenseExpr p) (thenM elseM : DenseComputationMethod p)

/-- A dense derivation list: `VarId`-keyed computation methods, in order (last-entry-wins on decode,
    mirroring `Derivations.methodFor`). -/
abbrev DenseDerivations (p : ℕ) := List (VarId × DenseComputationMethod p)

/-- A dense constraint system: algebraic constraints and bus interactions over `DenseExpr`. -/
structure DenseConstraintSystem (p : ℕ) where
  algebraicConstraints : List (DenseExpr p)
  busInteractions : List (BusInteraction (DenseExpr p))

/-- Boxed field operations and constants, built once outside hot recursive traversals. -/
structure DenseZModOps (p : ℕ) where
  add : ZMod p → ZMod p → ZMod p
  mul : ZMod p → ZMod p → ZMod p
  zero : ZMod p
  one : ZMod p
  negOne : ZMod p
  add_eq : ∀ a b, add a b = a + b
  mul_eq : ∀ a b, mul a b = a * b
  zero_eq : zero = 0
  one_eq : one = 1
  negOne_eq : negOne = -1

/-- Every field is a primitive, so constructing the record builds no `CommRing (ZMod p)` dictionary
    — which is what makes each `…With ops` twin cheap. -/
def denseZModOps : DenseZModOps p where
  add := zmodAddP
  mul := zmodMulP
  zero := zmodZeroP p
  one := zmodOneP p
  negOne := zmodNegOneP p
  add_eq := zmodAddP_eq
  mul_eq := zmodMulP_eq
  zero_eq := zmodZeroP_eq
  one_eq := zmodOneP_eq
  negOne_eq := zmodNegOneP_eq

/-! ## Dense expression operations (runtime; specified against decode below) -/

/-- Multiplicative degree, mirroring `ExpressionG.degree`. -/
def DenseExpr.degree : DenseExpr p → Nat
  | .const _ => 0
  | .var _ => 1
  | .add a b => max a.degree b.degree
  | .mul a b => a.degree + b.degree

/-! Mentioning `DenseExpr.const 0`/`1` anywhere in a function puts a `ZMod.commRing` chain at that
function's *entry*, ahead of every branch test that would have rejected the input, so recognizers
test literals through these instead. The `_eq_decide` bridges are their whole proof surface. -/

/-- Is the dense expression the literal constant `0`? -/
def DenseExpr.isConstZero : DenseExpr p → Bool
  | .const n => zmodIsZero n
  | _ => false

/-- Is the dense expression the literal constant `1`? -/
def DenseExpr.isConstOne : DenseExpr p → Bool
  | .const n => zmodIsOne n
  | _ => false

theorem DenseExpr.isConstZero_eq_decide (e : DenseExpr p) :
    e.isConstZero = decide (e = DenseExpr.const 0) := by
  cases e <;> simp [DenseExpr.isConstZero]

theorem DenseExpr.isConstOne_eq_decide (e : DenseExpr p) :
    e.isConstOne = decide (e = DenseExpr.const 1) := by
  cases e <;> simp [DenseExpr.isConstOne]

/-- `eval` mentions `+`/`*`, so it derived the whole `CommRing` chain at *every node*. This twin
    routes both through the primitives; the `@[csimp]` below lives here, in the earliest dense
    module, so it fires for every pass. -/

def DenseExpr.evalImpl (e : DenseExpr p) (denv : VarId → ZMod p) : ZMod p :=
  match e with
  | .const n => n
  | .var i => denv i
  | .add a b => zmodAddP (a.evalImpl denv) (b.evalImpl denv)
  | .mul a b => zmodMulP (a.evalImpl denv) (b.evalImpl denv)

def DenseExpr.eval (e : DenseExpr p) (denv : VarId → ZMod p) : ZMod p :=
  match e with
  | .const n => n
  | .var i => denv i
  | .add a b => a.eval denv + b.eval denv
  | .mul a b => a.eval denv * b.eval denv

theorem DenseExpr.evalImpl_eq (e : DenseExpr p) (denv : VarId → ZMod p) :
    e.evalImpl denv = e.eval denv := by
  induction e with
  | const n => rfl
  | var i => rfl
  | add a b iha ihb => rw [DenseExpr.evalImpl, DenseExpr.eval, zmodAddP_eq, iha, ihb]
  | mul a b iha ihb => rw [DenseExpr.evalImpl, DenseExpr.eval, zmodMulP_eq, iha, ihb]

@[csimp] theorem DenseExpr.eval_eq_evalImpl : @DenseExpr.eval = @DenseExpr.evalImpl := by
  funext q e denv; exact (DenseExpr.evalImpl_eq e denv).symm

/-- The `VarId`s occurring in a dense expression, in left-to-right order. -/
def DenseExpr.vars : DenseExpr p → List VarId
  | .const _ => []
  | .var i => [i]
  | .add a b => a.vars ++ b.vars
  | .mul a b => a.vars ++ b.vars

/-! `vars` appends its children's lists, so every enclosing node recopies the left subtree's
result — quadratic in the depth of the left-associated chains affine reconstruction produces, and
one of the biggest allocation sources in the whole optimizer (`vars` is recomputed per item per
pass). The accumulator twin below walks the right subtree into the suffix, allocating one cons per
occurrence and preserving the left-to-right order exactly. -/

def DenseExpr.varsAcc : DenseExpr p → List VarId → List VarId
  | .const _, acc => acc
  | .var i, acc => i :: acc
  | .add a b, acc => a.varsAcc (b.varsAcc acc)
  | .mul a b, acc => a.varsAcc (b.varsAcc acc)

theorem DenseExpr.varsAcc_eq (e : DenseExpr p) (acc : List VarId) :
    e.varsAcc acc = e.vars ++ acc := by
  induction e generalizing acc with
  | const n => rfl
  | var i => rfl
  | add a b iha ihb => simp [DenseExpr.varsAcc, DenseExpr.vars, iha, ihb]
  | mul a b iha ihb => simp [DenseExpr.varsAcc, DenseExpr.vars, iha, ihb]

def DenseExpr.varsFast (e : DenseExpr p) : List VarId := e.varsAcc []

@[csimp] theorem DenseExpr.vars_eq_fast : @DenseExpr.vars = @DenseExpr.varsFast := by
  funext p e
  show e.vars = e.varsAcc []
  rw [DenseExpr.varsAcc_eq, List.append_nil]

/-- All `VarId`s of a dense bus interaction (multiplicity then payload). -/
def denseBIVars (bi : BusInteraction (DenseExpr p)) : List VarId :=
  bi.multiplicity.vars ++ bi.payload.flatMap DenseExpr.vars

/-! ## Coverage: every leaf ID is valid in the registry -/

/-- Every `VarId` leaf of `e` is valid in `r`. Threaded as a single invariant; local validity of a
    particular leaf is derived from it. -/
def DenseExpr.CoveredBy (r : VarRegistry) (e : DenseExpr p) : Prop :=
  ∀ i ∈ e.vars, r.Valid i

theorem DenseExpr.coveredBy_const (r : VarRegistry) (n : ZMod p) :
    (DenseExpr.const n).CoveredBy r := by intro i hi; simp [DenseExpr.vars] at hi

theorem DenseExpr.coveredBy_var {r : VarRegistry} {i : VarId} (h : r.Valid i) :
    (DenseExpr.var i : DenseExpr p).CoveredBy r := by
  intro j hj; simp [DenseExpr.vars] at hj; exact hj ▸ h

theorem DenseExpr.coveredBy_add {r : VarRegistry} {a b : DenseExpr p} :
    (a.add b).CoveredBy r ↔ a.CoveredBy r ∧ b.CoveredBy r := by
  simp only [CoveredBy, DenseExpr.vars, List.mem_append]
  constructor
  · exact fun h => ⟨fun i hi => h i (Or.inl hi), fun i hi => h i (Or.inr hi)⟩
  · exact fun ⟨ha, hb⟩ i hi => hi.elim (ha i) (hb i)

theorem DenseExpr.coveredBy_mul {r : VarRegistry} {a b : DenseExpr p} :
    (a.mul b).CoveredBy r ↔ a.CoveredBy r ∧ b.CoveredBy r := by
  simp only [CoveredBy, DenseExpr.vars, List.mem_append]
  constructor
  · exact fun h => ⟨fun i hi => h i (Or.inl hi), fun i hi => h i (Or.inr hi)⟩
  · exact fun ⟨ha, hb⟩ i hi => hi.elim (ha i) (hb i)

/-! ## Decoding -/

/-- Decode a dense expression: resolve each `VarId` leaf through the registry. -/
def VarRegistry.decodeExpr (r : VarRegistry) : DenseExpr p → OutputExpression p
  | .const n => .const n
  | .var i => .var (r.resolve i)
  | .add a b => .add (r.decodeExpr a) (r.decodeExpr b)
  | .mul a b => .mul (r.decodeExpr a) (r.decodeExpr b)

def VarRegistry.decodeCM (r : VarRegistry) : DenseComputationMethod p → ComputationMethod p
  | .const c => .const c
  | .quotientOrZero num den => .quotientOrZero (r.decodeExpr num) (r.decodeExpr den)
  | .ifEqZero cond thenM elseM => .ifEqZero (r.decodeExpr cond) (r.decodeCM thenM) (r.decodeCM elseM)

def VarRegistry.decodeBI (r : VarRegistry) (bi : BusInteraction (DenseExpr p)) :
    BusInteraction (OutputExpression p) :=
  { busId := bi.busId,
    multiplicity := r.decodeExpr bi.multiplicity,
    payload := bi.payload.map r.decodeExpr }

def VarRegistry.decodeCS (r : VarRegistry) (d : DenseConstraintSystem p) : Circuit p :=
  { algebraicConstraints := d.algebraicConstraints.map r.decodeExpr,
    busInteractions := d.busInteractions.map r.decodeBI }

def VarRegistry.decodeDerivs (r : VarRegistry) (dd : DenseDerivations p) : Derivations p :=
  dd.map (fun d => (r.resolve d.1, r.decodeCM d.2))

/-! ## Decode correspondence: degree, eval, vars -/

/-- Decoding preserves multiplicative degree. -/
theorem VarRegistry.decodeExpr_degree (r : VarRegistry) (e : DenseExpr p) :
    (r.decodeExpr e).degree = e.degree := by
  induction e with
  | const n => rfl
  | var i => rfl
  | add a b iha ihb => simp [decodeExpr, ExpressionG.degree, DenseExpr.degree, iha, ihb]
  | mul a b iha ihb => simp [decodeExpr, ExpressionG.degree, DenseExpr.degree, iha, ihb]

/-- Decoding commutes with evaluation: evaluating the decoded expression under `env` equals
    evaluating the dense expression under `env ∘ resolve`. -/
theorem VarRegistry.decodeExpr_eval (r : VarRegistry) (e : DenseExpr p) (env : Variable → ZMod p) :
    (r.decodeExpr e).eval env = e.eval (fun i => env (r.resolve i)) := by
  induction e with
  | const n => rfl
  | var i => rfl
  | add a b iha ihb => simp [decodeExpr, ExpressionG.eval, DenseExpr.eval, iha, ihb]
  | mul a b iha ihb => simp [decodeExpr, ExpressionG.eval, DenseExpr.eval, iha, ihb]

/-- The variables of a decoded expression are the resolved dense variables, in order. -/
theorem VarRegistry.decodeExpr_vars (r : VarRegistry) (e : DenseExpr p) :
    (r.decodeExpr e).vars = e.vars.map r.resolve := by
  induction e with
  | const n => rfl
  | var i => rfl
  | add a b iha ihb => simp [decodeExpr, ExpressionG.vars, DenseExpr.vars, iha, ihb]
  | mul a b iha ihb => simp [decodeExpr, ExpressionG.vars, DenseExpr.vars, iha, ihb]

/-! ## Decode stability under registry extension -/

/-- Decoding a covered dense expression is unchanged by extending the registry. -/
theorem VarRegistry.Extends.decodeExpr_eq {r r' : VarRegistry} (h : r.Extends r') {e : DenseExpr p}
    (hc : e.CoveredBy r) : r'.decodeExpr e = r.decodeExpr e := by
  induction e with
  | const n => rfl
  | var i =>
      have : r.Valid i := hc i (by simp [DenseExpr.vars])
      simp [decodeExpr, h.resolve_eq this]
  | add a b iha ihb =>
      obtain ⟨ha, hb⟩ := DenseExpr.coveredBy_add.mp hc
      simp [decodeExpr, iha ha, ihb hb]
  | mul a b iha ihb =>
      obtain ⟨ha, hb⟩ := DenseExpr.coveredBy_mul.mp hc
      simp [decodeExpr, iha ha, ihb hb]

theorem DenseExpr.CoveredBy.mono {r r' : VarRegistry} (h : r.Extends r') {e : DenseExpr p}
    (hc : e.CoveredBy r) : e.CoveredBy r' := fun i hi => h.valid (hc i hi)

/-! ## Encoding (state-threaded registration + dense emission) -/

/-- Encode a spec expression into a dense one, threading the registry and registering each variable
    occurrence. -/
def VarRegistry.encodeExpr (r : VarRegistry) : OutputExpression p → VarRegistry × DenseExpr p
  | .const n => (r, .const n)
  | .var x => let (r', i) := r.register x; (r', .var i)
  | .add a b =>
      let (r1, a') := r.encodeExpr a
      let (r2, b') := r1.encodeExpr b
      (r2, .add a' b')
  | .mul a b =>
      let (r1, a') := r.encodeExpr a
      let (r2, b') := r1.encodeExpr b
      (r2, .mul a' b')

def VarRegistry.encodeExprs (r : VarRegistry) :
    List (OutputExpression p) → VarRegistry × List (DenseExpr p)
  | [] => (r, [])
  | e :: rest =>
      let (r1, e') := r.encodeExpr e
      let (r2, rest') := r1.encodeExprs rest
      (r2, e' :: rest')

def VarRegistry.encodeBI (r : VarRegistry) (bi : BusInteraction (OutputExpression p)) :
    VarRegistry × BusInteraction (DenseExpr p) :=
  let (r1, m) := r.encodeExpr bi.multiplicity
  let (r2, ps) := r1.encodeExprs bi.payload
  (r2, { busId := bi.busId, multiplicity := m, payload := ps })

def VarRegistry.encodeBIs (r : VarRegistry) :
    List (BusInteraction (OutputExpression p)) → VarRegistry × List (BusInteraction (DenseExpr p))
  | [] => (r, [])
  | bi :: rest =>
      let (r1, bi') := r.encodeBI bi
      let (r2, rest') := r1.encodeBIs rest
      (r2, bi' :: rest')

/-- Encode a spec constraint system; the registry it returns covers the dense system it returns. -/
def VarRegistry.encodeCS (r : VarRegistry) (cs : Circuit p) :
    VarRegistry × DenseConstraintSystem p :=
  let (r1, acs) := r.encodeExprs cs.algebraicConstraints
  let (r2, bis) := r1.encodeBIs cs.busInteractions
  (r2, { algebraicConstraints := acs, busInteractions := bis })

/-! ## Encode: extension, coverage, round trip (expression level) -/

theorem VarRegistry.encodeExpr_extends (r : VarRegistry) (e : OutputExpression p) :
    r.Extends (r.encodeExpr e).1 := by
  induction e generalizing r with
  | const n => exact VarRegistry.Extends.refl r
  | var x => exact r.register_extends x
  | add a b iha ihb =>
      exact (iha r).trans (ihb (r.encodeExpr a).1)
  | mul a b iha ihb =>
      exact (iha r).trans (ihb (r.encodeExpr a).1)

theorem VarRegistry.encodeExpr_covered (r : VarRegistry) (e : OutputExpression p) :
    (r.encodeExpr e).2.CoveredBy (r.encodeExpr e).1 := by
  induction e generalizing r with
  | const n => exact DenseExpr.coveredBy_const _ n
  | var x => exact DenseExpr.coveredBy_var (r.register_valid x)
  | add a b iha ihb =>
      show (DenseExpr.add (r.encodeExpr a).2 ((r.encodeExpr a).1.encodeExpr b).2).CoveredBy _
      rw [DenseExpr.coveredBy_add]
      refine ⟨?_, ihb (r.encodeExpr a).1⟩
      exact (iha r).mono ((r.encodeExpr a).1.encodeExpr_extends b)
  | mul a b iha ihb =>
      show (DenseExpr.mul (r.encodeExpr a).2 ((r.encodeExpr a).1.encodeExpr b).2).CoveredBy _
      rw [DenseExpr.coveredBy_mul]
      refine ⟨?_, ihb (r.encodeExpr a).1⟩
      exact (iha r).mono ((r.encodeExpr a).1.encodeExpr_extends b)

/-- Round trip: decoding an encoded expression is the identity. -/
theorem VarRegistry.decodeExpr_encodeExpr (r : VarRegistry) (e : OutputExpression p) :
    (r.encodeExpr e).1.decodeExpr (r.encodeExpr e).2 = e := by
  induction e generalizing r with
  | const n => rfl
  | var x =>
      show (r.register x).1.decodeExpr (.var (r.register x).2) = .var x
      simp [decodeExpr, r.register_resolve x]
  | add a b iha ihb =>
      show ((r.encodeExpr a).1.encodeExpr b).1.decodeExpr
        (.add (r.encodeExpr a).2 ((r.encodeExpr a).1.encodeExpr b).2) = .add a b
      rw [decodeExpr]
      congr 1
      · rw [((r.encodeExpr a).1.encodeExpr_extends b).decodeExpr_eq (r.encodeExpr_covered a)]
        exact iha r
      · exact ihb (r.encodeExpr a).1
  | mul a b iha ihb =>
      show ((r.encodeExpr a).1.encodeExpr b).1.decodeExpr
        (.mul (r.encodeExpr a).2 ((r.encodeExpr a).1.encodeExpr b).2) = .mul a b
      rw [decodeExpr]
      congr 1
      · rw [((r.encodeExpr a).1.encodeExpr_extends b).decodeExpr_eq (r.encodeExpr_covered a)]
        exact iha r
      · exact ihb (r.encodeExpr a).1

/-! ## Encode: extension, coverage, round trip (list / bus-interaction / system levels) -/

/-- Structural unfolding of `encodeExprs` on a cons (holds by `rfl` via `Prod` eta). -/
theorem VarRegistry.encodeExprs_cons (r : VarRegistry) (e : OutputExpression p)
    (rest : List (OutputExpression p)) :
    r.encodeExprs (e :: rest) =
      (((r.encodeExpr e).1.encodeExprs rest).1,
        (r.encodeExpr e).2 :: ((r.encodeExpr e).1.encodeExprs rest).2) := rfl

theorem VarRegistry.encodeBIs_cons (r : VarRegistry) (bi : BusInteraction (OutputExpression p))
    (rest : List (BusInteraction (OutputExpression p))) :
    r.encodeBIs (bi :: rest) =
      (((r.encodeBI bi).1.encodeBIs rest).1,
        (r.encodeBI bi).2 :: ((r.encodeBI bi).1.encodeBIs rest).2) := rfl

theorem VarRegistry.Extends.decodeExprs_eq {r r' : VarRegistry} (h : r.Extends r')
    {es : List (DenseExpr p)} (hc : ∀ e ∈ es, e.CoveredBy r) :
    es.map r'.decodeExpr = es.map r.decodeExpr :=
  List.map_congr_left (fun e he => h.decodeExpr_eq (hc e he))

theorem VarRegistry.encodeExprs_extends (r : VarRegistry) (es : List (OutputExpression p)) :
    r.Extends (r.encodeExprs es).1 := by
  induction es generalizing r with
  | nil => exact Extends.refl r
  | cons e rest ih =>
      rw [encodeExprs_cons]
      exact (r.encodeExpr_extends e).trans (ih (r.encodeExpr e).1)

theorem VarRegistry.encodeExprs_covered (r : VarRegistry) (es : List (OutputExpression p)) :
    ∀ e ∈ (r.encodeExprs es).2, e.CoveredBy (r.encodeExprs es).1 := by
  induction es generalizing r with
  | nil => intro e he; simp [encodeExprs] at he
  | cons e rest ih =>
      rw [encodeExprs_cons]
      intro e' he'
      rcases List.mem_cons.mp he' with heq | hmem
      · subst heq
        exact (r.encodeExpr_covered e).mono ((r.encodeExpr e).1.encodeExprs_extends rest)
      · exact ih (r.encodeExpr e).1 e' hmem

theorem VarRegistry.decodeExprs_encodeExprs (r : VarRegistry) (es : List (OutputExpression p)) :
    ((r.encodeExprs es).2).map (r.encodeExprs es).1.decodeExpr = es := by
  induction es generalizing r with
  | nil => rfl
  | cons e rest ih =>
      rw [encodeExprs_cons]
      simp only [List.map_cons]
      congr 1
      · rw [((r.encodeExpr e).1.encodeExprs_extends rest).decodeExpr_eq (r.encodeExpr_covered e)]
        exact r.decodeExpr_encodeExpr e
      · exact ih (r.encodeExpr e).1

/-- Coverage of a dense bus interaction: multiplicity and every payload expression are covered. -/
def denseBICovered (r : VarRegistry) (bi : BusInteraction (DenseExpr p)) : Prop :=
  bi.multiplicity.CoveredBy r ∧ ∀ e ∈ bi.payload, e.CoveredBy r

/-- Structural projections of `encodeBI` (each holds by `rfl` via `Prod` eta). -/
theorem VarRegistry.encodeBI_fst (r : VarRegistry) (bi : BusInteraction (OutputExpression p)) :
    (r.encodeBI bi).1 = ((r.encodeExpr bi.multiplicity).1.encodeExprs bi.payload).1 := rfl

theorem VarRegistry.encodeBI_mult (r : VarRegistry) (bi : BusInteraction (OutputExpression p)) :
    (r.encodeBI bi).2.multiplicity = (r.encodeExpr bi.multiplicity).2 := rfl

theorem VarRegistry.encodeBI_payload (r : VarRegistry) (bi : BusInteraction (OutputExpression p)) :
    (r.encodeBI bi).2.payload = ((r.encodeExpr bi.multiplicity).1.encodeExprs bi.payload).2 := rfl

theorem VarRegistry.Extends.decodeBI_eq {r r' : VarRegistry} (h : r.Extends r')
    {bi : BusInteraction (DenseExpr p)} (hc : denseBICovered r bi) :
    r'.decodeBI bi = r.decodeBI bi := by
  obtain ⟨hm, hp⟩ := hc
  simp only [VarRegistry.decodeBI, h.decodeExpr_eq hm, h.decodeExprs_eq hp]

theorem VarRegistry.encodeBI_extends (r : VarRegistry) (bi : BusInteraction (OutputExpression p)) :
    r.Extends (r.encodeBI bi).1 :=
  (r.encodeExpr_extends bi.multiplicity).trans
    ((r.encodeExpr bi.multiplicity).1.encodeExprs_extends bi.payload)

theorem VarRegistry.encodeBI_covered (r : VarRegistry) (bi : BusInteraction (OutputExpression p)) :
    denseBICovered (r.encodeBI bi).1 (r.encodeBI bi).2 := by
  rw [denseBICovered, encodeBI_mult, encodeBI_payload, encodeBI_fst]
  refine ⟨?_, ?_⟩
  · exact (r.encodeExpr_covered bi.multiplicity).mono
      ((r.encodeExpr bi.multiplicity).1.encodeExprs_extends bi.payload)
  · exact (r.encodeExpr bi.multiplicity).1.encodeExprs_covered bi.payload

theorem VarRegistry.decodeBI_encodeBI (r : VarRegistry) (bi : BusInteraction (OutputExpression p)) :
    (r.encodeBI bi).1.decodeBI (r.encodeBI bi).2 = bi := by
  simp only [VarRegistry.decodeBI, encodeBI_fst, encodeBI_mult, encodeBI_payload]
  obtain ⟨busId, mult, payload⟩ := bi
  congr 1
  · rw [((r.encodeExpr mult).1.encodeExprs_extends payload).decodeExpr_eq
        (r.encodeExpr_covered mult)]
    exact r.decodeExpr_encodeExpr mult
  · exact (r.encodeExpr mult).1.decodeExprs_encodeExprs payload

theorem VarRegistry.encodeBIs_extends (r : VarRegistry)
    (bis : List (BusInteraction (OutputExpression p))) : r.Extends (r.encodeBIs bis).1 := by
  induction bis generalizing r with
  | nil => exact Extends.refl r
  | cons bi rest ih =>
      rw [encodeBIs_cons]
      exact (r.encodeBI_extends bi).trans (ih (r.encodeBI bi).1)

theorem VarRegistry.decodeBIs_encodeBIs (r : VarRegistry)
    (bis : List (BusInteraction (OutputExpression p))) :
    ((r.encodeBIs bis).2).map (r.encodeBIs bis).1.decodeBI = bis := by
  induction bis generalizing r with
  | nil => rfl
  | cons bi rest ih =>
      rw [encodeBIs_cons]
      simp only [List.map_cons]
      congr 1
      · rw [((r.encodeBI bi).1.encodeBIs_extends rest).decodeBI_eq (r.encodeBI_covered bi)]
        exact r.decodeBI_encodeBI bi
      · exact ih (r.encodeBI bi).1

/-- Structural projections of `encodeCS` (each holds by `rfl` via `Prod` eta). -/
theorem VarRegistry.encodeCS_fst (r : VarRegistry) (cs : Circuit p) :
    (r.encodeCS cs).1
      = ((r.encodeExprs cs.algebraicConstraints).1.encodeBIs cs.busInteractions).1 := rfl

theorem VarRegistry.encodeCS_acs (r : VarRegistry) (cs : Circuit p) :
    (r.encodeCS cs).2.algebraicConstraints = (r.encodeExprs cs.algebraicConstraints).2 := rfl

theorem VarRegistry.encodeCS_bis (r : VarRegistry) (cs : Circuit p) :
    (r.encodeCS cs).2.busInteractions
      = ((r.encodeExprs cs.algebraicConstraints).1.encodeBIs cs.busInteractions).2 := rfl

/-- Round trip at the system level: decoding an encoded constraint system recovers the original —
    the identity the pipeline's edge encode/decode rides on. -/
theorem VarRegistry.decodeCS_encodeCS (r : VarRegistry) (cs : Circuit p) :
    (r.encodeCS cs).1.decodeCS (r.encodeCS cs).2 = cs := by
  obtain ⟨acs, bis⟩ := cs
  simp only [VarRegistry.decodeCS, encodeCS_fst, encodeCS_acs, encodeCS_bis]
  congr 1
  · rw [((r.encodeExprs acs).1.encodeBIs_extends bis).decodeExprs_eq
        (r.encodeExprs_covered acs)]
    exact r.decodeExprs_encodeExprs acs
  · exact (r.encodeExprs acs).1.decodeBIs_encodeBIs bis

end ApcOptimizer.Dense
