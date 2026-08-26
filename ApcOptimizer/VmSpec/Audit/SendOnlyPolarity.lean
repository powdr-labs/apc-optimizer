import ApcOptimizer.VmSpec.Legal
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-! **A decidable, syntactic check for `Circuit.statelessSendOnly`/`Circuit.statefulPolarity`.**

    This is neither spec (it proves a theorem about the two *existing* legality clauses, adding no
    new claim) nor `Implementation/` (nothing in the VM-level soundness argument calls it — it is a
    tool an optimizer, or a human, runs *on a candidate circuit* to check those two clauses hold,
    the translation-validation way: run the checker, get a `Bool`, and `checkMultiplicities_sound`
    turns a `true` into the actual `Prop`s `Circuit.legalGuest` needs).

    The check is a single pass over `c.busInteractions`: fold each multiplicity expression to a
    literal field constant (`Expression.foldConst`), and ask whether that constant is already in
    the legal set for its bus's statefulness — `{0, 1}` for a stateless send, `{0, 1, -1}` for a
    stateful one. It is sound but incomplete by construction: `Circuit.statelessSendOnly` quantifies
    over every algebraically-satisfying assignment, and folding a multiplicity that is a bare
    variable (e.g. a boolean flag range-checked elsewhere to `{0, 1}`) always returns `none`, so the
    checker rejects a chip that legitimately gates a lookup on such a flag. Recognizing that case —
    matching the multiplicity against a booleanity constraint elsewhere in `algebraicConstraints` —
    is a natural next tier this file does not attempt.

    **Two tiers.** `checkMultiplicities` folds multiplicities to literals and never looks at
    `algebraicConstraints`; it suffices for an *optimized* APC, whose multiplicities are field
    literals. `checkMultiplicitiesWith` adds a constant-propagation tier: it reads
    `Expression`-to-constant *pin rules* off the constraints (`pinRuleOf`) and folds with them,
    which is what an *unoptimized* APC needs — there a multiplicity is a sum of opcode flags, legal
    only because a constraint pins that sum to `1`. The added tier is still sound for free: both
    legality clauses quantify over `Circuit.satisfiesAlgebraic` assignments, so the constraints are
    available to use.

    Neither tier recognizes a multiplicity that is a bare *boolean* variable — a fresh `is_valid`
    gate carrying only `is_valid * (is_valid - 1) = 0`, which is what powdr's final pass introduces
    (`Audit/RealApcLegality.lean`). That constraint is not linear, so no pin rule comes off it; a
    booleanity tier is the natural next one and is not attempted here.

    The third clause of `Circuit.legalGuest`, `stepLayout`, is not covered. Part of it would yield
    to a pass of this kind — the arcs are readable off the bridge interactions, and `ordered` is
    already a numeric check — but `placed` needs the lt gadget recognized in both the shapes powdr
    leaves it in, and `sendsOk` is a claim about payload *values* (byte discipline) that depends on
    how a chip computes what it sends. `Audit/RealApcLegality.lean` proves it by hand for one
    circuit instead. -/

variable {p : ℕ}

/-- Fold an expression to a literal field constant when every leaf is a `.const` — the simplest
    sufficient witness that its value is fixed independent of the assignment. `none` on any `.var`,
    since no such witness exists for a value that can vary. -/
def Expression.foldConst : Expression p → Option (ZMod p)
  | .const n => some n
  | .var _ => none
  | .add e1 e2 => match e1.foldConst, e2.foldConst with
    | some v1, some v2 => some (v1 + v2)
    | _, _ => none
  | .mul e1 e2 => match e1.foldConst, e2.foldConst with
    | some v1, some v2 => some (v1 * v2)
    | _, _ => none

/-- What `Expression.foldConst` promises: the folded constant is the expression's value under
    *every* assignment. -/
theorem Expression.foldConst_eq {e : Expression p} {v : ZMod p} (h : e.foldConst = some v)
    (asg : Variable → ZMod p) : e.eval asg = v := by
  induction e generalizing v with
  | const n => cases h; rfl
  | var x => cases h
  | add e1 e2 ih1 ih2 =>
    simp only [Expression.foldConst] at h
    cases h1 : e1.foldConst with
    | none => rw [h1] at h; cases h
    | some v1 =>
      cases h2 : e2.foldConst with
      | none => rw [h1, h2] at h; cases h
      | some v2 =>
        rw [h1, h2] at h
        cases h
        exact congrArg₂ (· + ·) (ih1 h1) (ih2 h2)
  | mul e1 e2 ih1 ih2 =>
    simp only [Expression.foldConst] at h
    cases h1 : e1.foldConst with
    | none => rw [h1] at h; cases h
    | some v1 =>
      cases h2 : e2.foldConst with
      | none => rw [h1, h2] at h; cases h
      | some v2 =>
        rw [h1, h2] at h
        cases h
        exact congrArg₂ (· * ·) (ih1 h1) (ih2 h2)

/-- The multiplicities `Circuit.statelessSendOnly`/`Circuit.statefulPolarity` allow, keyed by
    whether the bus is stateful — `{0, 1, -1}` for a stateful send, `{0, 1}` for a stateless one.
    Matches the target sets those two definitions state directly. -/
def legalMultiplicity (stateful : Bool) (v : ZMod p) : Prop :=
  if stateful then v = 0 ∨ v = 1 ∨ v = -1 else v = 0 ∨ v = 1

instance {stateful : Bool} {v : ZMod p} : Decidable (legalMultiplicity stateful v) := by
  unfold legalMultiplicity; cases stateful <;> infer_instance

/-- **The static check.** For every bus interaction, its multiplicity folds to a literal constant
    already legal for its bus's statefulness (per `isStateful`, meant to be a
    `GuestBusRules.isStateful`). Decidable, and syntactic only — it never inspects
    `algebraicConstraints`. -/
def checkMultiplicities (isStateful : Nat → Bool) (c : Circuit p) : Bool :=
  c.busInteractions.all fun bi =>
    match bi.multiplicity.foldConst with
    | some v => decide (legalMultiplicity (isStateful bi.busId) v)
    | none => false

/-- **Soundness of the static check.** A `true` result gives both `Circuit.statelessSendOnly` and
    `Circuit.statefulPolarity`, for any `r` whose `isStateful` is the one the check ran against —
    the check needs nothing else about `r` (not `accepts`, not `payloadOk`), so it applies uniformly
    across every VM's `GuestBusRules`. -/
theorem checkMultiplicities_sound {isStateful : Nat → Bool} {c : Circuit p}
    (h : checkMultiplicities isStateful c = true) {r : GuestBusRules p}
    (hr : r.isStateful = isStateful) :
    c.statelessSendOnly r ∧ c.statefulPolarity r := by
  have hall : ∀ bi ∈ c.busInteractions, ∃ v : ZMod p, bi.multiplicity.foldConst = some v ∧
      legalMultiplicity (isStateful bi.busId) v := by
    intro bi hbi
    have hbi' := List.all_eq_true.mp h bi hbi
    cases hfold : bi.multiplicity.foldConst with
    | none => rw [hfold] at hbi'; simp at hbi'
    | some v => exact ⟨v, rfl, by rw [hfold] at hbi'; simpa using hbi'⟩
  constructor
  · intro asg _ bi hbi hst
    obtain ⟨v, hfold, hleg⟩ := hall bi hbi
    have hval : (bi.eval asg).multiplicity = v := Expression.foldConst_eq hfold asg
    rw [hr] at hst
    rw [hst] at hleg
    unfold legalMultiplicity at hleg
    simpa [hval] using hleg
  · intro asg _ bi hbi hst
    obtain ⟨v, hfold, hleg⟩ := hall bi hbi
    have hval : (bi.eval asg).multiplicity = v := Expression.foldConst_eq hfold asg
    rw [hr] at hst
    rw [hst] at hleg
    unfold legalMultiplicity at hleg
    simpa [hval] using hleg

--------- Tier two: constant propagation from the algebraic constraints ---------

deriving instance DecidableEq for Expression

/-- An expression the circuit's algebraic constraints pin to a field constant. -/
abbrev PinRule (p : ℕ) := Expression p × ZMod p

/-- Read `α * e` off an expression, with `α` restricted to `1`/`-1`. Restricting to units that are
    their own inverse is what lets `pinRuleOf` recover `e`'s value by multiplying rather than
    dividing, so nothing here needs `p` to be prime. Total: anything else is its own `1 *`. -/
def Expression.signedPart : Expression p → ZMod p × Expression p
  | .mul (.const a) e => if a = 1 then (1, e) else if a = -1 then (-1, e) else (1, .mul (.const a) e)
  | e => (1, e)

theorem Expression.signedPart_sq (e : Expression p) :
    (e.signedPart).1 * (e.signedPart).1 = 1 := by
  unfold Expression.signedPart
  split
  · split_ifs <;> simp
  · simp

theorem Expression.signedPart_eval (e : Expression p) (asg : Variable → ZMod p) :
    (e.signedPart).1 * (e.signedPart).2.eval asg = e.eval asg := by
  unfold Expression.signedPart
  split
  · rename_i a e'
    split_ifs <;> simp_all [Expression.eval]
  · simp

/-- **Read a pin rule off one algebraic constraint.** A constraint of the shape `α * e + b` (either
    operand order, `α ∈ {1, -1}`, `b` a foldable constant) forces `e = -(b * α)` wherever the
    constraint holds. -/
def pinRuleOf : Expression p → Option (PinRule p)
  | .add l r =>
      match l.foldConst, r.foldConst with
      | none, some b => let s := l.signedPart; some (s.2, -(b * s.1))
      | some b, none => let s := r.signedPart; some (s.2, -(b * s.1))
      | _, _ => none
  | _ => none

/-- What `pinRuleOf` promises. -/
theorem pinRuleOf_eval {con : Expression p} {e : Expression p} {v : ZMod p}
    (h : pinRuleOf con = some (e, v)) {asg : Variable → ZMod p} (hcon : con.eval asg = 0) :
    e.eval asg = v := by
  unfold pinRuleOf at h
  cases con with
  | const n => cases h
  | var x => cases h
  | mul a b => cases h
  | add l r =>
    simp only at h
    have hev : l.eval asg + r.eval asg = 0 := hcon
    cases hl : l.foldConst with
    | none =>
      cases hr : r.foldConst with
      | none => rw [hl, hr] at h; cases h
      | some b =>
        rw [hl, hr] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨he, hv⟩ := h
        have hrv : r.eval asg = b := Expression.foldConst_eq hr asg
        have hlb : l.eval asg = -b := by rw [hrv] at hev; linear_combination hev
        have hlv : (l.signedPart).1 * (l.signedPart).2.eval asg = l.eval asg :=
          l.signedPart_eval asg
        subst he; subst hv
        have key : (l.signedPart).1 * ((l.signedPart).1 * (l.signedPart).2.eval asg)
            = (l.signedPart).1 * (-b) := by rw [hlv, hlb]
        rw [← mul_assoc, l.signedPart_sq, one_mul] at key
        rw [key]; ring
    | some b =>
      rw [hl] at h
      cases hr : r.foldConst with
      | none =>
        rw [hr] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨he, hv⟩ := h
        have hlv : l.eval asg = b := Expression.foldConst_eq hl asg
        have hrb : r.eval asg = -b := by rw [hlv] at hev; linear_combination hev
        have hrv : (r.signedPart).1 * (r.signedPart).2.eval asg = r.eval asg :=
          r.signedPart_eval asg
        subst he; subst hv
        have key : (r.signedPart).1 * ((r.signedPart).1 * (r.signedPart).2.eval asg)
            = (r.signedPart).1 * (-b) := by rw [hrv, hrb]
        rw [← mul_assoc, r.signedPart_sq, one_mul] at key
        rw [key]; ring
      | some b' => rw [hr] at h; cases h

/-- Look one expression up among the pin rules, by syntactic equality. -/
def lookupPin (rules : List (PinRule p)) (e : Expression p) : Option (ZMod p) :=
  (rules.find? (fun r => decide (r.1 = e))).map Prod.snd

theorem lookupPin_mem {rules : List (PinRule p)} {e : Expression p} {v : ZMod p}
    (h : lookupPin rules e = some v) : (e, v) ∈ rules := by
  unfold lookupPin at h
  cases hf : rules.find? (fun r => decide (r.1 = e)) with
  | none => rw [hf] at h; cases h
  | some r =>
    rw [hf] at h
    simp only [Option.map_some, Option.some.injEq] at h
    have hmem := List.mem_of_find?_eq_some hf
    have hp : decide (r.1 = e) = true := List.find?_some (p := fun q : PinRule p =>
      decide (q.1 = e)) hf
    rw [← of_decide_eq_true hp, ← h]
    exact hmem

/-- `Expression.foldConst`, plus the pin rules: a subexpression the constraints pin to a constant
    folds to it even when it mentions variables. -/
def Expression.foldConstWith (rules : List (PinRule p)) : Expression p → Option (ZMod p)
  | .const n => some n
  | .var x => lookupPin rules (.var x)
  | .add a b =>
      match lookupPin rules (.add a b) with
      | some v => some v
      | none => match a.foldConstWith rules, b.foldConstWith rules with
        | some v1, some v2 => some (v1 + v2)
        | _, _ => none
  | .mul a b =>
      match lookupPin rules (.mul a b) with
      | some v => some v
      | none => match a.foldConstWith rules, b.foldConstWith rules with
        | some v1, some v2 => some (v1 * v2)
        | _, _ => none

/-- What `Expression.foldConstWith` promises, given that every rule holds under `asg`. -/
theorem Expression.foldConstWith_eq {rules : List (PinRule p)} {asg : Variable → ZMod p}
    (hrules : ∀ r ∈ rules, r.1.eval asg = r.2) :
    ∀ {e : Expression p} {v : ZMod p}, e.foldConstWith rules = some v → e.eval asg = v := by
  intro e
  induction e with
  | const n => intro v h; cases h; rfl
  | var x => intro v h; exact hrules _ (lookupPin_mem h)
  | add a b iha ihb =>
    intro v h
    simp only [Expression.foldConstWith] at h
    cases hp : lookupPin rules (.add a b) with
    | some w => rw [hp] at h; cases h; exact hrules _ (lookupPin_mem hp)
    | none =>
      rw [hp] at h
      cases h1 : a.foldConstWith rules with
      | none => rw [h1] at h; cases h
      | some v1 =>
        cases h2 : b.foldConstWith rules with
        | none => rw [h1, h2] at h; cases h
        | some v2 =>
          rw [h1, h2] at h; cases h
          exact congrArg₂ (· + ·) (iha h1) (ihb h2)
  | mul a b iha ihb =>
    intro v h
    simp only [Expression.foldConstWith] at h
    cases hp : lookupPin rules (.mul a b) with
    | some w => rw [hp] at h; cases h; exact hrules _ (lookupPin_mem hp)
    | none =>
      rw [hp] at h
      cases h1 : a.foldConstWith rules with
      | none => rw [h1] at h; cases h
      | some v1 =>
        cases h2 : b.foldConstWith rules with
        | none => rw [h1, h2] at h; cases h
        | some v2 =>
          rw [h1, h2] at h; cases h
          exact congrArg₂ (· * ·) (iha h1) (ihb h2)

/-- **The static check, with constant propagation.** Same shape as `checkMultiplicities`, but each
    multiplicity is folded against the pin rules the circuit's own constraints supply. -/
def checkMultiplicitiesWith (isStateful : Nat → Bool) (c : Circuit p) : Bool :=
  let rules := c.algebraicConstraints.filterMap pinRuleOf
  c.busInteractions.all fun bi =>
    match bi.multiplicity.foldConstWith rules with
    | some v => decide (legalMultiplicity (isStateful bi.busId) v)
    | none => false

/-- **Soundness of the strengthened check.** As `checkMultiplicities_sound`, and by the same
    reading: a `true` gives both clauses. The rules are legitimate because both clauses quantify
    over assignments that satisfy the constraints the rules were read off. -/
theorem checkMultiplicitiesWith_sound {isStateful : Nat → Bool} {c : Circuit p}
    (h : checkMultiplicitiesWith isStateful c = true) {r : GuestBusRules p}
    (hr : r.isStateful = isStateful) :
    c.statelessSendOnly r ∧ c.statefulPolarity r := by
  set rules := c.algebraicConstraints.filterMap pinRuleOf with hrulesdef
  have hrules : ∀ asg : ChipAssignment p, c.satisfiesAlgebraic asg →
      ∀ q ∈ rules, q.1.eval asg = q.2 := by
    intro asg halg q hq
    obtain ⟨con, hcon, hpin⟩ := List.mem_filterMap.mp hq
    exact pinRuleOf_eval (by rw [hpin]) (halg con hcon)
  have hall : ∀ asg : ChipAssignment p, c.satisfiesAlgebraic asg →
      ∀ bi ∈ c.busInteractions,
        legalMultiplicity (isStateful bi.busId) ((bi.eval asg).multiplicity) := by
    intro asg halg bi hbi
    have hbi' := List.all_eq_true.mp h bi hbi
    cases hfold : bi.multiplicity.foldConstWith rules with
    | none => rw [hfold] at hbi'; simp at hbi'
    | some v =>
      have hval : (bi.eval asg).multiplicity = v :=
        Expression.foldConstWith_eq (hrules asg halg) hfold
      rw [hfold] at hbi'
      rw [hval]
      simpa using hbi'
  refine ⟨?_, ?_⟩ <;> intro asg halg bi hbi hst <;>
    · have hleg := hall asg halg bi hbi
      rw [hr] at hst
      rw [hst] at hleg
      unfold legalMultiplicity at hleg
      simpa using hleg
