import ApcOptimizer.VmSpec.Audit.Apcs.Common

set_option autoImplicit false

/-! # A decidable check for the order-free legality clauses

    `Audit/Apcs/Common.lean`'s `hasStepLayout_of_checks` reduces `Circuit.hasStepLayout` to
    seven per-interaction facts. Discharging them by case-splitting on the interaction index works
    for a ten-interaction APC and no further: `fin_cases` over a twenty- or thirty-interaction
    circuit re-`whnf`s the whole of `opt` once per case, and `opt` is a very large term.

    This file replaces the case split with the repository's own idiom — the one
    `Audit/PlaceCheck.lean`'s `placeCheckAll` and `Audit/ByteCheck.lean`'s `byteCheckAll` already
    use. `legalityCheckAll` is a `Bool` computed from the interaction list, the recipe list and a
    *pairing list* `prt`, and `hasStepLayout_of_legalityCheck` turns one `legalityCheckAll … = true` — settled
    by a single kernel `decide` — into all of `Circuit.hasStepLayout`.

    What the check reads, and what each clause needs of it:

    | clause | check |
    | --- | --- |
    | `negOffsetOnlyMemRecv` | a stateful interaction is either a memory `getPrevious` or has a non-negative recipe |
    | `sendInWindow` | a possible memory send has a `.fixed` recipe inside `[0, d)` |
    | `memPartner_invol` | `prt` is a fixed-point-free involution on the memory bus |
    | `memPartner_mult` | the two halves' multiplicities fold to opposite constants, and their address slots linearize the same way |
    | `memPartner_time` | a `getPrevious`'s recipe lies strictly below its partner's |
    | `sendTimesDistinct` | two possible sends carry distinct ticks, or provably distinct addresses |
    | `x0Zero` | a possible send provably does not address `(1, 0)`, or writes zero data |

    "Possible send" is the checker's one piece of care: it cannot see which interactions are sends,
    so it treats every memory interaction whose multiplicity does not fold to `-1` as one. That is
    conservative in the right direction — a real send is never mistaken for a receive — and it is
    what lets a single `decide` cover a circuit the elaborator cannot case-split. -/

namespace ApcOptimizer.OpenVM.LegalityCheck

open ApcOptimizer.OpenVM

/-- The default a `getD` falls back on; never reached at an in-range index. -/
def dfltBi : BusInteraction (Expression babyBear) := ⟨0, .const 0, []⟩

theorem getD_get {α : Type} (L : List α) (d : α) (i : Fin L.length) : L.getD i.val d = L.get i := by
  rw [List.getD_eq_getElem?_getD, List.get_eq_getElem, List.getElem?_eq_getElem i.isLt]
  rfl

--------- Reading an interaction ---------

/-- What an interaction's multiplicity folds to, if anything. -/
def multConst (rules : List (PinRule babyBear)) (bi : BusInteraction (Expression babyBear)) :
    Option (ZMod babyBear) := bi.multiplicity.foldConstWith rules

/-- What payload slot `k` folds to, if anything. -/
def constSlot (rules : List (PinRule babyBear)) (bi : BusInteraction (Expression babyBear))
    (k : ℕ) : Option (ZMod babyBear) := bi.payload[k]?.bind (fun e => e.foldConstWith rules)

/-- …and how it linearizes, which is the comparison two halves of one access need: their pointer
    is often a variable, so folding to a constant is too much to ask. -/
def linSlot (vs : List Variable) (rules : List (PinRule babyBear))
    (bi : BusInteraction (Expression babyBear)) (k : ℕ) : Option (LinForm babyBear) :=
  bi.payload[k]?.bind (fun e => e.toLin vs rules)

--------- Small decidable comparisons on `Option` ---------

def optIs (x : Option (ZMod babyBear)) (v : ZMod babyBear) : Bool := x == some v

def optIsNot (x : Option (ZMod babyBear)) (v : ZMod babyBear) : Bool :=
  match x with | some a => a != v | none => false

def optSumZero (x y : Option (ZMod babyBear)) : Bool :=
  match x, y with | some a, some b => a + b == 0 | _, _ => false

def optNe (x y : Option (ZMod babyBear)) : Bool :=
  match x, y with | some a, some b => a != b | _, _ => false

def optLinEq (x y : Option (LinForm babyBear)) : Bool :=
  match x, y with | some a, some b => a == b | _, _ => false

theorem optIs_sound {x : Option (ZMod babyBear)} {v : ZMod babyBear} (h : optIs x v = true) :
    x = some v := by simpa [optIs] using h

theorem optIsNot_sound {x : Option (ZMod babyBear)} {v : ZMod babyBear}
    (h : optIsNot x v = true) : ∃ a, x = some a ∧ a ≠ v := by
  cases x <;> simp_all [optIsNot]

theorem optSumZero_sound {x y : Option (ZMod babyBear)} (h : optSumZero x y = true) :
    ∃ a b, x = some a ∧ y = some b ∧ a + b = 0 := by
  cases x <;> cases y <;> simp_all [optSumZero]

theorem optNe_sound {x y : Option (ZMod babyBear)} (h : optNe x y = true) :
    ∃ a b, x = some a ∧ y = some b ∧ a ≠ b := by
  cases x <;> cases y <;> simp_all [optNe]

theorem optLinEq_sound {x y : Option (LinForm babyBear)} (h : optLinEq x y = true) :
    ∃ f, x = some f ∧ y = some f := by
  cases x <;> cases y <;> simp_all [optLinEq]

--------- The readings ---------

/-- Whether an interaction's multiplicity folds to the constant `v`. -/
def multIs (rules : List (PinRule babyBear)) (bi : BusInteraction (Expression babyBear))
    (v : ZMod babyBear) : Bool := optIs (multConst rules bi) v

/-- Whether the interaction could be a memory *send*: on the memory bus, and its multiplicity does
    not fold to `-1`. Conservative — an interaction whose multiplicity does not fold at all counts
    as a possible send. -/
def maybeSend (rules : List (PinRule babyBear)) (memBusId : ℕ)
    (bi : BusInteraction (Expression babyBear)) : Bool :=
  (bi.busId == memBusId) && !(multIs rules bi (-1))

/-- Whether a recipe is a fixed tick — the shape every memory send has. -/
def Recipe.isFixed : Recipe babyBear → Bool
  | .fixed _ => true
  | .lookback _ _ _ _ => false

theorem Recipe.place_of_isFixed {rc : Recipe babyBear} (h : Recipe.isFixed rc = true)
    (asg : ChipAssignment babyBear) : rc.place asg = rc.ub := by
  cases rc with
  | fixed k => rfl
  | lookback k radix loE hiE => exact absurd h (by simp [Recipe.isFixed])

/-- Structural equality of expressions — the fallback when an address slot does not linearize.
    A computed pointer mentions variables outside the layout's own list, and powdr emits the very
    same subterm in both halves of an access, so syntactic agreement is what settles those. -/
def exprBEq : Expression babyBear → Expression babyBear → Bool
  | .const a, .const b => a == b
  | .var a, .var b => a == b
  | .add a b, .add c d => exprBEq a c && exprBEq b d
  | .mul a b, .mul c d => exprBEq a c && exprBEq b d
  | _, _ => false

theorem exprBEq_eq : ∀ {a b : Expression babyBear}, exprBEq a b = true → a = b := by
  intro a
  induction a with
  | const x =>
    intro b h
    cases b with
    | const y => exact congrArg Expression.const (by simpa [exprBEq] using h)
    | var _ => exact absurd h (by simp [exprBEq])
    | add _ _ => exact absurd h (by simp [exprBEq])
    | mul _ _ => exact absurd h (by simp [exprBEq])
  | var x =>
    intro b h
    cases b with
    | const _ => exact absurd h (by simp [exprBEq])
    | var y => exact congrArg Expression.var (by simpa [exprBEq] using h)
    | add _ _ => exact absurd h (by simp [exprBEq])
    | mul _ _ => exact absurd h (by simp [exprBEq])
  | add x y ihx ihy =>
    intro b h
    cases b with
    | const _ => exact absurd h (by simp [exprBEq])
    | var _ => exact absurd h (by simp [exprBEq])
    | add c d =>
      simp only [exprBEq, Bool.and_eq_true] at h
      exact congrArg₂ Expression.add (ihx h.1) (ihy h.2)
    | mul _ _ => exact absurd h (by simp [exprBEq])
  | mul x y ihx ihy =>
    intro b h
    cases b with
    | const _ => exact absurd h (by simp [exprBEq])
    | var _ => exact absurd h (by simp [exprBEq])
    | add _ _ => exact absurd h (by simp [exprBEq])
    | mul c d =>
      simp only [exprBEq, Bool.and_eq_true] at h
      exact congrArg₂ Expression.mul (ihx h.1) (ihy h.2)

def optExprEq (x y : Option (Expression babyBear)) : Bool :=
  match x, y with | some a, some b => exprBEq a b | _, _ => false

theorem optExprEq_sound {x y : Option (Expression babyBear)} (h : optExprEq x y = true) :
    x = y := by
  cases x with
  | none => cases y <;> exact absurd h (by simp [optExprEq])
  | some a =>
    cases y with
    | none => exact absurd h (by simp [optExprEq])
    | some b => exact congrArg some (exprBEq_eq h)

/-- Whether two interactions provably agree at address slot `k`: the slots linearize to the same
    form, or are literally the same expression. -/
def slotAgree (vs : List Variable) (rules : List (PinRule babyBear))
    (bi bj : BusInteraction (Expression babyBear)) (k : ℕ) : Bool :=
  optLinEq (linSlot vs rules bi k) (linSlot vs rules bj k)
    || optExprEq bi.payload[k]? bj.payload[k]?

/-- Whether two interactions provably address the same memory cell. -/
def sameAddr (vs : List Variable) (rules : List (PinRule babyBear))
    (bi bj : BusInteraction (Expression babyBear)) : Bool :=
  slotAgree vs rules bi bj 0 && slotAgree vs rules bi bj 1

/-- Whether two interactions provably address *different* cells. -/
def diffAddr (rules : List (PinRule babyBear))
    (bi bj : BusInteraction (Expression babyBear)) : Bool :=
  optNe (constSlot rules bi 0) (constSlot rules bj 0)
    || optNe (constSlot rules bi 1) (constSlot rules bj 1)

/-- Whether the two halves of an access carry opposite multiplicities. -/
def oppMult (rules : List (PinRule babyBear)) (bi bj : BusInteraction (Expression babyBear)) :
    Bool := optSumZero (multConst rules bi) (multConst rules bj)

/-- Whether the interaction provably respects `x0`: it carries no address at all, or does not
    address register `0`, or the four data limbs it writes there fold to zero. -/
def x0Ok (rules : List (PinRule babyBear)) (bi : BusInteraction (Expression babyBear)) : Bool :=
  bi.payload[0]?.isNone || bi.payload[1]?.isNone
    || optIsNot (constSlot rules bi 0) 1 || optIsNot (constSlot rules bi 1) 0
    || [2, 3, 4, 5].all (fun k => optIs (constSlot rules bi k) 0)

--------- What those readings mean under an assignment ---------

/-- The `(address space, pointer)` an interaction names, as `openVmMemAddress` reads it. -/
def addrOf (asg : ChipAssignment babyBear) (bi : BusInteraction (Expression babyBear)) :
    List (Option (ZMod babyBear)) :=
  [bi.payload[0]?.map (fun e => e.eval asg), bi.payload[1]?.map (fun e => e.eval asg)]

theorem memAddress_eq (c : Circuit babyBear) (asg : ChipAssignment babyBear)
    (i : Fin c.busInteractions.length) :
    openVmMemAddress (c.msgAt asg i) = addrOf asg (c.busInteractions.get i) := by
  simp [openVmMemAddress, addrOf, Circuit.msgAt, BusInteraction.eval, List.getElem?_map]

theorem multIs_sound {rules : List (PinRule babyBear)} {asg : ChipAssignment babyBear}
    (hrules : ∀ q ∈ rules, q.1.eval asg = q.2) {bi : BusInteraction (Expression babyBear)}
    {v : ZMod babyBear} (h : multIs rules bi v = true) : (bi.eval asg).multiplicity = v :=
  Expression.foldConstWith_eq hrules (optIs_sound h)

theorem constSlot_sound {rules : List (PinRule babyBear)} {asg : ChipAssignment babyBear}
    (hrules : ∀ q ∈ rules, q.1.eval asg = q.2) {bi : BusInteraction (Expression babyBear)}
    {k : ℕ} {v : ZMod babyBear} (h : constSlot rules bi k = some v) :
    bi.payload[k]?.map (fun e => e.eval asg) = some v := by
  simp only [constSlot] at h
  cases hb : bi.payload[k]? with
  | none => rw [hb] at h; exact absurd h (by simp)
  | some e =>
    rw [hb] at h
    simp only [Option.bind_some] at h
    rw [Option.map_some, Expression.foldConstWith_eq hrules h]

theorem linSlot_sound {vs : List Variable} {rules : List (PinRule babyBear)}
    {asg : ChipAssignment babyBear} (hrules : ∀ q ∈ rules, q.1.eval asg = q.2)
    {bi : BusInteraction (Expression babyBear)} {k : ℕ} {f : LinForm babyBear}
    (h : linSlot vs rules bi k = some f) :
    bi.payload[k]?.map (fun e => e.eval asg) = some (f.eval vs asg) := by
  simp only [linSlot] at h
  cases hb : bi.payload[k]? with
  | none => rw [hb] at h; exact absurd h (by simp)
  | some e =>
    rw [hb] at h
    simp only [Option.bind_some] at h
    rw [Option.map_some, Expression.toLin_eval hrules h]

theorem slotAgree_sound {vs : List Variable} {rules : List (PinRule babyBear)}
    {asg : ChipAssignment babyBear} (hrules : ∀ q ∈ rules, q.1.eval asg = q.2)
    {bi bj : BusInteraction (Expression babyBear)} {k : ℕ} (h : slotAgree vs rules bi bj k = true) :
    bi.payload[k]?.map (fun e => e.eval asg) = bj.payload[k]?.map (fun e => e.eval asg) := by
  simp only [slotAgree, Bool.or_eq_true] at h
  rcases h with h | h
  · obtain ⟨f, hi, hj⟩ := optLinEq_sound h
    exact (linSlot_sound hrules hi).trans (linSlot_sound hrules hj).symm
  · rw [optExprEq_sound h]

theorem sameAddr_sound {vs : List Variable} {rules : List (PinRule babyBear)}
    {asg : ChipAssignment babyBear} (hrules : ∀ q ∈ rules, q.1.eval asg = q.2)
    {bi bj : BusInteraction (Expression babyBear)} (h : sameAddr vs rules bi bj = true) :
    addrOf asg bi = addrOf asg bj := by
  simp only [sameAddr, Bool.and_eq_true] at h
  simp only [addrOf, List.cons.injEq, and_true]
  exact ⟨slotAgree_sound hrules h.1, slotAgree_sound hrules h.2⟩

theorem diffAddr_sound {rules : List (PinRule babyBear)} {asg : ChipAssignment babyBear}
    (hrules : ∀ q ∈ rules, q.1.eval asg = q.2)
    {bi bj : BusInteraction (Expression babyBear)} (h : diffAddr rules bi bj = true) :
    addrOf asg bi ≠ addrOf asg bj := by
  simp only [diffAddr, Bool.or_eq_true] at h
  intro hc
  simp only [addrOf, List.cons.injEq, and_true] at hc
  rcases h with h | h
  · obtain ⟨x, y, hx, hy, hne⟩ := optNe_sound h
    exact hne (Option.some_inj.mp
      ((constSlot_sound hrules hx).symm.trans (hc.1.trans (constSlot_sound hrules hy))))
  · obtain ⟨x, y, hx, hy, hne⟩ := optNe_sound h
    exact hne (Option.some_inj.mp
      ((constSlot_sound hrules hx).symm.trans (hc.2.trans (constSlot_sound hrules hy))))

theorem oppMult_sound {rules : List (PinRule babyBear)} {asg : ChipAssignment babyBear}
    (hrules : ∀ q ∈ rules, q.1.eval asg = q.2)
    {bi bj : BusInteraction (Expression babyBear)} (h : oppMult rules bi bj = true) :
    (bj.eval asg).multiplicity = -(bi.eval asg).multiplicity := by
  obtain ⟨a, b, ha, hb, hab⟩ := optSumZero_sound h
  have ea : (bi.eval asg).multiplicity = a := Expression.foldConstWith_eq hrules ha
  have eb : (bj.eval asg).multiplicity = b := Expression.foldConstWith_eq hrules hb
  rw [ea, eb]
  linear_combination hab

--------- The check ---------

/-- **(2b)** A stateful interaction either reaches forward, or is a memory `getPrevious`. -/
def negOffsetOk (rules : List (PinRule babyBear)) (memBusId maxLookback : ℕ)
    (bi : BusInteraction (Expression babyBear)) (rc : Recipe babyBear) : Bool :=
  !(apcRules.isStateful bi.busId) || decide (0 ≤ rc.lb maxLookback)
    || ((bi.busId == memBusId) && multIs rules bi (-1))

/-- **(2)** A possible memory send commits at a fixed tick inside `[0, d)`. -/
def windowOk (rules : List (PinRule babyBear)) (memBusId d : ℕ)
    (bi : BusInteraction (Expression babyBear)) (rc : Recipe babyBear) : Bool :=
  !(maybeSend rules memBusId bi) || (Recipe.isFixed rc && decide (0 ≤ rc.ub ∧ rc.ub < (d : ℤ)))

/-- **(3)** The pairing: a fixed-point-free involution on the memory bus, with opposite
    multiplicities, one cell, and the `getPrevious` strictly earlier. -/
def partnerOk (vs : List Variable) (rules : List (PinRule babyBear)) (memBusId maxLookback : ℕ)
    (len i q qq : ℕ) (bi bq : BusInteraction (Expression babyBear))
    (rc rq : Recipe babyBear) : Bool :=
  (bi.busId != memBusId)
    || (decide (q < len) && (qq == i) && (q != i) && (bq.busId == memBusId)
        && (multIs rules bi 1 || multIs rules bi (-1))
        && oppMult rules bi bq && sameAddr vs rules bi bq
        && (!(multIs rules bi (-1)) || Recipe.below maxLookback rc rq))

/-- A possible memory send respects `x0`. -/
def x0ZeroOk (rules : List (PinRule babyBear)) (memBusId : ℕ)
    (bi : BusInteraction (Expression babyBear)) : Bool :=
  !(maybeSend rules memBusId bi) || x0Ok rules bi

/-- The per-interaction check, with everything it reads passed in by value. -/
def legalityCheckAt (vs : List Variable) (rules : List (PinRule babyBear)) (memBusId maxLookback d : ℕ)
    (len i q qq : ℕ) (bi bq : BusInteraction (Expression babyBear))
    (rc rq : Recipe babyBear) : Bool :=
  negOffsetOk rules memBusId maxLookback bi rc && windowOk rules memBusId d bi rc
    && partnerOk vs rules memBusId maxLookback len i q qq bi bq rc rq
    && x0ZeroOk rules memBusId bi

def legalityCheckOne (vs : List Variable) (rules : List (PinRule babyBear))
    (memBusId maxLookback d : ℕ) (L : List (BusInteraction (Expression babyBear)))
    (R : List (Recipe babyBear)) (prt : List ℕ) (i : ℕ) : Bool :=
  legalityCheckAt vs rules memBusId maxLookback d L.length i (prt.getD i 0)
    (prt.getD (prt.getD i 0) 0) (L.getD i dfltBi) (L.getD (prt.getD i 0) dfltBi)
    (R.getD i (.fixed 0)) (R.getD (prt.getD i 0) (.fixed 0))

/-- Two possible memory sends carry distinct ticks, or provably distinct addresses. -/
def legalityCheckPair (rules : List (PinRule babyBear)) (memBusId : ℕ)
    (L : List (BusInteraction (Expression babyBear))) (R : List (Recipe babyBear))
    (i j : ℕ) : Bool :=
  !(maybeSend rules memBusId (L.getD i dfltBi)) || !(maybeSend rules memBusId (L.getD j dfltBi))
    || decide ((R.getD i (.fixed 0)).ub ≠ (R.getD j (.fixed 0)).ub)
    || diffAddr rules (L.getD i dfltBi) (L.getD j dfltBi)

/-- **The whole order-free discipline, as one `Bool`.** -/
def legalityCheckAll (vs : List Variable) (rules : List (PinRule babyBear))
    (memBusId maxLookback d : ℕ) (L : List (BusInteraction (Expression babyBear)))
    (R : List (Recipe babyBear)) (prt : List ℕ) : Bool :=
  (List.range L.length).all (legalityCheckOne vs rules memBusId maxLookback d L R prt)
    && (List.range L.length).all fun i =>
        (List.range i).all fun j => legalityCheckPair rules memBusId L R j i

theorem legalityCheckAll_one {vs : List Variable} {rules : List (PinRule babyBear)}
    {memBusId maxLookback d : ℕ} {L : List (BusInteraction (Expression babyBear))}
    {R : List (Recipe babyBear)} {prt : List ℕ}
    (h : legalityCheckAll vs rules memBusId maxLookback d L R prt = true) (i : Fin L.length) :
    legalityCheckOne vs rules memBusId maxLookback d L R prt i.val = true := by
  simp only [legalityCheckAll, Bool.and_eq_true] at h
  exact List.all_eq_true.mp h.1 i.val (List.mem_range.mpr i.isLt)

theorem legalityCheckAll_pair {vs : List Variable} {rules : List (PinRule babyBear)}
    {memBusId maxLookback d : ℕ} {L : List (BusInteraction (Expression babyBear))}
    {R : List (Recipe babyBear)} {prt : List ℕ}
    (h : legalityCheckAll vs rules memBusId maxLookback d L R prt = true)
    {i : ℕ} (hi : i < L.length) {j : ℕ} (hj : j < i) :
    legalityCheckPair rules memBusId L R j i = true := by
  simp only [legalityCheckAll, Bool.and_eq_true] at h
  exact List.all_eq_true.mp (List.all_eq_true.mp h.2 i (List.mem_range.mpr hi)) j
    (List.mem_range.mpr hj)

--------- Soundness, one clause at a time ---------

theorem negOffsetOk_sound {rules : List (PinRule babyBear)} {asg : ChipAssignment babyBear}
    (hrules : ∀ q ∈ rules, q.1.eval asg = q.2) {memBusId maxLookback : ℕ}
    {bi : BusInteraction (Expression babyBear)} {rc : Recipe babyBear}
    (h : negOffsetOk rules memBusId maxLookback bi rc = true)
    (hst : apcRules.isStateful bi.busId = true) (hback : rc.back asg < maxLookback)
    (hlt : rc.place asg < 0) : bi.busId = memBusId ∧ (bi.eval asg).multiplicity = -1 := by
  simp only [negOffsetOk, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  rcases h with (h | h) | ⟨hb, hm⟩
  · exact absurd hst (by rw [h]; simp)
  · exact absurd hlt (by have := (Recipe.place_mem rc hback).1; omega)
  · exact ⟨hb, multIs_sound hrules hm⟩

theorem windowOk_sound {rules : List (PinRule babyBear)} {memBusId d : ℕ}
    {bi : BusInteraction (Expression babyBear)} {rc : Recipe babyBear}
    (h : windowOk rules memBusId d bi rc = true)
    (hms : maybeSend rules memBusId bi = true) (asg : ChipAssignment babyBear) :
    rc.place asg = rc.ub ∧ 0 ≤ rc.ub ∧ rc.ub < (d : ℤ) := by
  simp only [windowOk, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true,
    decide_eq_true_eq] at h
  rcases h with h | ⟨hfix, hrange⟩
  · exact absurd hms (by rw [h]; simp)
  · exact ⟨Recipe.place_of_isFixed hfix asg, hrange⟩

theorem partnerOk_sound {vs : List Variable} {rules : List (PinRule babyBear)}
    {memBusId maxLookback len i q qq : ℕ} {bi bq : BusInteraction (Expression babyBear)}
    {rc rq : Recipe babyBear}
    (h : partnerOk vs rules memBusId maxLookback len i q qq bi bq rc rq = true)
    (hbus : bi.busId = memBusId) :
    q < len ∧ qq = i ∧ q ≠ i ∧ bq.busId = memBusId
      ∧ (multIs rules bi 1 = true ∨ multIs rules bi (-1) = true)
      ∧ oppMult rules bi bq = true ∧ sameAddr vs rules bi bq = true
      ∧ (multIs rules bi (-1) = true → Recipe.below maxLookback rc rq = true) := by
  simp only [partnerOk, Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq, Bool.not_eq_true'] at h
  rcases h with h | ⟨⟨⟨⟨⟨⟨⟨hq, hqq⟩, hqi⟩, hbq⟩, hpol⟩, hopp⟩, hsame⟩, hbel⟩
  · exact absurd hbus h
  · refine ⟨hq, hqq, hqi, hbq, hpol, hopp, hsame, fun hneg => ?_⟩
    rcases hbel with hb | hb
    · exact absurd hneg (by rw [hb]; simp)
    · exact hb

theorem x0ZeroOk_sound {rules : List (PinRule babyBear)} {memBusId : ℕ}
    {bi : BusInteraction (Expression babyBear)} (h : x0ZeroOk rules memBusId bi = true)
    (hms : maybeSend rules memBusId bi = true) : x0Ok rules bi = true := by
  simp only [x0ZeroOk, Bool.or_eq_true, Bool.not_eq_true'] at h
  rcases h with h | h
  · exact absurd hms (by rw [h]; simp)
  · exact h

--------- One `decide` gives the whole layout ---------

/-- **`Circuit.hasStepLayout` from a single `decide`.** Same arguments as
    `hasStepLayout_of_checks`, with its six per-interaction clauses replaced by a pairing list
    `prt` and one `legalityCheckAll … = true`. -/
theorem hasStepLayout_of_legalityCheck {c : Circuit babyBear}
    {vs vsB : List Variable} {rules : List (PinRule babyBear)}
    {baseE pcFromE pcToE : Expression babyBear} {baseF : LinForm babyBear}
    {R : List (Recipe babyBear)} {W : List ByteWitness} {prt : List ℕ}
    {maxWindow d : ℕ} (hd : 0 < d) (hw : d < maxWindow)
    (hrules : ∀ asg : ChipAssignment babyBear, c.satisfiesAlgebraic asg →
      ∀ q ∈ rules, q.1.eval asg = q.2)
    (hbase : Expression.toLin vs rules baseE = some baseF)
    (hbridge : ∀ asg : ChipAssignment babyBear, c.satisfiesAlgebraic asg →
      c.allEffects asg (0, [pcFromE.eval asg, baseE.eval asg]) = -1 ∧
      c.allEffects asg (0, [pcToE.eval asg, baseE.eval asg + ((d : ℕ) : ZMod babyBear)]) = 1 ∧
      ∀ m : BusMessage babyBear, m.1 = 0 →
        m ≠ (0, [pcFromE.eval asg, baseE.eval asg]) →
        m ≠ (0, [pcToE.eval asg, baseE.eval asg + ((d : ℕ) : ZMod babyBear)]) →
        c.allEffects asg m = 0)
    (hplace :
      placeCheckAll vs rules apcRules.isStateful openVmTsPos baseF c.busInteractions R = true)
    (horder :
      memOrderCheck rules openVmMemBusId openVmTimestampBound c.busInteractions R = true)
    (hfits : (List.range c.busInteractions.length).all
      (fun i => (R.getD i (.fixed 0)).fits openVmTimestampBound d) = true)
    (hbyte : byteCheckAll vsB rules c.busInteractions W = true)
    (hlook : ∀ asg : ChipAssignment babyBear, c.satisfiesAlgebraic asg →
      c.satisfiesStateless apcRules asg →
      ∀ i : Fin c.busInteractions.length, ∀ (k : ℤ) (radix : ℕ) (loE hiE : Expression babyBear),
        R.getD i.val (.fixed 0) = .lookback k radix loE hiE →
        (R.getD i.val (.fixed 0)).back asg < openVmTimestampBound ∧
          apcRules.getTimestamp (c.msgAt asg i)
            = baseE.eval asg + (((R.getD i.val (.fixed 0)).place asg : ℤ) : ZMod babyBear))
    (hext : ∀ asg : ChipAssignment babyBear, c.satisfiesAlgebraic asg →
      c.satisfiesStateless apcRules asg →
      ∀ i : Fin c.busInteractions.length, W.getD i.val .notSend = .external →
        c.statefulSend apcRules asg i →
        (∀ j : Fin c.busInteractions.length, j < i → c.activeStateful apcRules asg j →
          apcRules.payloadOk (c.msgAt asg j)) →
        apcRules.payloadOk (c.msgAt asg i))
    (hof : legalityCheckAll vs rules openVmMemBusId openVmTimestampBound d c.busInteractions R prt
      = true) :
    c.hasStepLayout apcRules openVmMemAddress maxWindow openVmTimestampBound := by
  have hne1 : ¬ ((1 : ZMod babyBear) = -1) := by decide
  have hAt : ∀ i : Fin c.busInteractions.length,
      negOffsetOk rules openVmMemBusId openVmTimestampBound (c.busInteractions.get i)
          (R.getD i.val (.fixed 0)) = true
      ∧ windowOk rules openVmMemBusId d (c.busInteractions.get i)
          (R.getD i.val (.fixed 0)) = true
      ∧ partnerOk vs rules openVmMemBusId openVmTimestampBound c.busInteractions.length i.val
          (prt.getD i.val 0) (prt.getD (prt.getD i.val 0) 0) (c.busInteractions.get i)
          (c.busInteractions.getD (prt.getD i.val 0) dfltBi) (R.getD i.val (.fixed 0))
          (R.getD (prt.getD i.val 0) (.fixed 0)) = true
      ∧ x0ZeroOk rules openVmMemBusId (c.busInteractions.get i) = true := by
    intro i
    have h := legalityCheckAll_one hof i
    simp only [legalityCheckOne, legalityCheckAt, getD_get, Bool.and_eq_true] at h
    exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩
  have hback : ∀ asg : ChipAssignment babyBear, c.satisfiesAlgebraic asg →
      c.satisfiesStateless apcRules asg → ∀ i : Fin c.busInteractions.length,
      (R.getD i.val (.fixed 0)).back asg < openVmTimestampBound := by
    intro asg halg hacc i
    cases hrc : R.getD i.val (.fixed 0) with
    | fixed k => simp [Recipe.back, openVmTimestampBound, openVmTimestampBits]
    | lookback k radix loE hiE =>
      rw [← hrc]
      exact (hlook asg halg hacc i k radix loE hiE hrc).1
  have hmaybe : ∀ (asg : ChipAssignment babyBear), c.satisfiesAlgebraic asg →
      ∀ i : Fin c.busInteractions.length, c.memSend apcRules asg i →
      maybeSend rules openVmMemBusId (c.busInteractions.get i) = true := by
    intro asg halg i hs
    simp only [maybeSend, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true']
    refine ⟨hs.2, ?_⟩
    by_contra hc
    simp only [Bool.not_eq_false] at hc
    have hval : ((c.busInteractions.get i).eval asg).multiplicity = -1 :=
      multIs_sound (hrules asg halg) hc
    exact hne1 (hs.1.2.symm.trans hval)
  refine hasStepLayout_of_checks hd hw hrules hbase hbridge hplace horder hfits hbyte hlook hext
    ?_ (fun i => if h : prt.getD i.val 0 < c.busInteractions.length then ⟨_, h⟩ else i)
    ?_ ?_ ?_ ?_ ?_
  · -- `negOffsetOnlyMemRecv`
    intro asg halg hacc i hact hlt
    exact negOffsetOk_sound (hrules asg halg) (hAt i).1 hact.1 (hback asg halg hacc i) hlt
  · -- `memPartner_invol`
    intro i hi
    obtain ⟨hq, hqq, hqi, hbq, -, -, -, -⟩ := partnerOk_sound (hAt i).2.2.1 hi
    dsimp only
    rw [dif_pos hq]
    refine ⟨?_, fun hc => hqi (congrArg Fin.val hc), ?_⟩
    · rw [dif_pos (show prt.getD (prt.getD i.val 0) 0 < c.busInteractions.length by
        rw [hqq]; exact i.isLt)]
      exact Fin.ext hqq
    · rw [← getD_get c.busInteractions dfltBi ⟨_, hq⟩]
      exact hbq
  · -- `memPartner_mult`
    intro asg halg hacc i hi
    obtain ⟨hq, -, -, -, -, hopp, hsame, -⟩ := partnerOk_sound (hAt i).2.2.1 hi
    dsimp only
    rw [dif_pos hq]
    refine ⟨?_, ?_⟩
    · rw [Circuit.multAt, Circuit.multAt, ← getD_get c.busInteractions dfltBi ⟨_, hq⟩]
      exact oppMult_sound (hrules asg halg) hopp
    · rw [memAddress_eq, memAddress_eq, ← getD_get c.busInteractions dfltBi ⟨_, hq⟩]
      exact sameAddr_sound (hrules asg halg) hsame
  · -- `memPartner_time`
    intro asg halg hacc i hi hr
    obtain ⟨hq, -, -, -, hpol, -, -, hbel⟩ := partnerOk_sound (hAt i).2.2.1 hi
    have hneg1 : multIs rules (c.busInteractions.get i) (-1) = true := by
      rcases hpol with h1 | h1
      · have hval : ((c.busInteractions.get i).eval asg).multiplicity = 1 :=
          multIs_sound (hrules asg halg) h1
        exact absurd (hval.symm.trans hr) hne1
      · exact h1
    have h3 : (R.getD i.val (.fixed 0)).ub
        < (R.getD (prt.getD i.val 0) (.fixed 0)).lb openVmTimestampBound := by
      simpa [Recipe.below] using hbel hneg1
    dsimp only
    rw [dif_pos hq]
    show (R.getD i.val (.fixed 0)).place asg
      < (R.getD (prt.getD i.val 0) (.fixed 0)).place asg
    have h1 := (Recipe.place_mem (R.getD i.val (.fixed 0)) (hback asg halg hacc i)).2
    have h2 := (Recipe.place_mem (R.getD (prt.getD i.val 0) (.fixed 0))
      (hback asg halg hacc ⟨_, hq⟩)).1
    omega
  · -- `sendTimesDistinct`
    intro asg halg hacc i j hsi hsj haddr hplc
    by_contra hne
    have hfix : ∀ k : Fin c.busInteractions.length, c.memSend apcRules asg k →
        (R.getD k.val (.fixed 0)).place asg = (R.getD k.val (.fixed 0)).ub :=
      fun k hk => (windowOk_sound (hAt k).2.1 (hmaybe asg halg k hk) asg).1
    have hpair : ∀ a b : Fin c.busInteractions.length, b.val < a.val →
        c.memSend apcRules asg a → c.memSend apcRules asg b →
        openVmMemAddress (c.msgAt asg a) = openVmMemAddress (c.msgAt asg b) →
        (R.getD a.val (.fixed 0)).place asg = (R.getD b.val (.fixed 0)).place asg → False := by
      intro a b hba ha hb hadr hpl
      have h := legalityCheckAll_pair hof a.isLt hba
      simp only [legalityCheckPair, Bool.or_eq_true, getD_get, decide_eq_true_eq,
        Bool.not_eq_true'] at h
      rcases h with ((h | h) | h) | h
      · exact absurd (hmaybe asg halg b hb) (by rw [h]; simp)
      · exact absurd (hmaybe asg halg a ha) (by rw [h]; simp)
      · exact h (by rw [← hfix b hb, ← hfix a ha, hpl])
      · refine diffAddr_sound (hrules asg halg) h ?_
        rw [← memAddress_eq, ← memAddress_eq]
        exact hadr.symm
    rcases Nat.lt_or_ge i.val j.val with hlt | hge
    · exact hpair j i hlt hsj hsi haddr.symm hplc.symm
    · exact hpair i j (by omega) hsi hsj haddr hplc
  · -- `sendInWindow`
    intro asg halg hacc i hs
    obtain ⟨hpl, h0, h1⟩ := windowOk_sound (hAt i).2.1 (hmaybe asg halg i hs) asg
    rw [hpl]
    exact ⟨h0, h1⟩

/-- **`x0Zero`, from the same check.** -/
theorem x0Zero_of_legalityCheck {c : Circuit babyBear}
    {vs : List Variable} {rules : List (PinRule babyBear)} {R : List (Recipe babyBear)}
    {prt : List ℕ} {d : ℕ}
    (hrules : ∀ asg : ChipAssignment babyBear, c.satisfiesAlgebraic asg →
      ∀ q ∈ rules, q.1.eval asg = q.2)
    (hof : legalityCheckAll vs rules openVmMemBusId openVmTimestampBound d c.busInteractions R prt
      = true) :
    ∀ asg : ChipAssignment babyBear, c.satisfiesAlgebraic asg →
      c.satisfiesStateless apcRules asg →
      ∀ i : Fin c.busInteractions.length, c.memSend apcRules asg i →
        (c.msgAt asg i).2[0]? = some 1 → (c.msgAt asg i).2[1]? = some 0 →
          (c.msgAt asg i).2[2]? = some 0 ∧ (c.msgAt asg i).2[3]? = some 0 ∧
            (c.msgAt asg i).2[4]? = some 0 ∧ (c.msgAt asg i).2[5]? = some 0 := by
  intro asg halg hacc i hs h0 h1
  have hne1 : ¬ ((1 : ZMod babyBear) = -1) := by decide
  have hmaybe : maybeSend rules openVmMemBusId (c.busInteractions.get i) = true := by
    simp only [maybeSend, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true']
    refine ⟨hs.2, ?_⟩
    by_contra hc
    simp only [Bool.not_eq_false] at hc
    have hval : ((c.busInteractions.get i).eval asg).multiplicity = -1 :=
      multIs_sound (hrules asg halg) hc
    exact hne1 (hs.1.2.symm.trans hval)
  have hslot : ∀ k : ℕ, (c.msgAt asg i).2[k]?
      = (c.busInteractions.get i).payload[k]?.map (fun e => e.eval asg) := by
    intro k
    simp [Circuit.msgAt, BusInteraction.eval, List.getElem?_map]
  have hx := x0ZeroOk_sound (by
    have h := legalityCheckAll_one hof i
    simp only [legalityCheckOne, legalityCheckAt, getD_get, Bool.and_eq_true] at h
    exact h.2) hmaybe
  simp only [x0Ok, Bool.or_eq_true] at hx
  rcases hx with (((hn0 | hn1) | hxa) | hxb) | hdata
  · have hnone : (c.busInteractions.get i).payload[0]? = none := by
      cases hp : (c.busInteractions.get i).payload[0]? with
      | none => rfl
      | some e => rw [hp] at hn0; exact absurd hn0 (by simp)
    rw [hslot 0, hnone] at h0
    exact absurd h0 (by simp)
  · have hnone : (c.busInteractions.get i).payload[1]? = none := by
      cases hp : (c.busInteractions.get i).payload[1]? with
      | none => rfl
      | some e => rw [hp] at hn1; exact absurd hn1 (by simp)
    rw [hslot 1, hnone] at h1
    exact absurd h1 (by simp)
  · obtain ⟨a, ha, hane⟩ := optIsNot_sound hxa
    rw [hslot 0, constSlot_sound (hrules asg halg) ha] at h0
    exact absurd (Option.some_inj.mp h0) hane
  · obtain ⟨a, ha, hane⟩ := optIsNot_sound hxb
    rw [hslot 1, constSlot_sound (hrules asg halg) ha] at h1
    exact absurd (Option.some_inj.mp h1) hane
  · simp only [List.all_eq_true, List.mem_cons, List.not_mem_nil, or_false] at hdata
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hslot 2, constSlot_sound (hrules asg halg) (optIs_sound (hdata 2 (by simp)))]
    · rw [hslot 3, constSlot_sound (hrules asg halg) (optIs_sound (hdata 3 (by simp)))]
    · rw [hslot 4, constSlot_sound (hrules asg halg) (optIs_sound (hdata 4 (by simp)))]
    · rw [hslot 5, constSlot_sound (hrules asg halg) (optIs_sound (hdata 5 (by simp)))]

end ApcOptimizer.OpenVM.LegalityCheck
