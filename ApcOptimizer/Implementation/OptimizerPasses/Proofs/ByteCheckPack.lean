import ApcOptimizer.Implementation.OptimizerPasses.ByteCheckPack
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.BusPairCancelCheck
import ApcOptimizer.Implementation.OptimizerPasses.BridgeSteps

set_option autoImplicit false

/-! # Soundness of the dense `bytePack` recognizer and builders

`DensePassCorrect` proofs for the recognizer and pair builder of the byte-check packing pass
(`ByteCheckPack.lean`), over dense environments `VarId → ZMod p`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Emitted pair byte checks (`denseMkBytePair_*`) -/

/-- The evaluation of an emitted pair byte check. -/
theorem denseMkBytePair_eval (spec : ByteXorSpec p) (busId : Nat) (e₁ e₂ : DenseExpr p)
    (denv : VarId → ZMod p) :
    denseBIEval (denseMkBytePair spec busId e₁ e₂) denv
      = { busId := busId, multiplicity := 1,
          payload := spec.encode spec.pairOp (e₁.eval denv) (e₂.eval denv) 0 } := by
  simp only [denseMkBytePair, denseBIEval, spec.encode_map, DenseExpr.eval]

/-- An emitted pair byte check breaks no invariant. -/
theorem denseMkBytePair_breaks (bs : BusSemantics p) (facts : BusFacts p bs)
    (spec : ByteXorSpec p) (busId : Nat) (hspec : facts.byteXorSpec busId = some spec)
    (e₁ e₂ : DenseExpr p) (denv : VarId → ZMod p) :
    bs.maintainsInvariants (denseBIEval (denseMkBytePair spec busId e₁ e₂) denv) := by
  obtain ⟨_, hbreak, _⟩ := facts.byteXorSpec_sound busId spec hspec
  rw [denseMkBytePair_eval]; exact hbreak _

/-- A pair byte check is accepted exactly when both operands are bytes. -/
theorem denseMkBytePair_accepted (bs : BusSemantics p) (facts : BusFacts p bs)
    (spec : ByteXorSpec p) (busId : Nat) (hspec : facts.byteXorSpec busId = some spec)
    (e₁ e₂ : DenseExpr p) (denv : VarId → ZMod p) :
    bs.accepts (denseBIEval (denseMkBytePair spec busId e₁ e₂) denv)
      ↔ (e₁.eval denv).val < spec.bound ∧ (e₂.eval denv).val < spec.bound := by
  obtain ⟨_, _, hsound⟩ := facts.byteXorSpec_sound busId spec hspec
  rw [denseMkBytePair_eval]
  have hdec : spec.decode (spec.encode spec.pairOp (e₁.eval denv) (e₂.eval denv) 0)
      = some (spec.pairOp, e₁.eval denv, e₂.eval denv, (0 : ZMod p)) := spec.decode_encode _ _ _ _
  rw [(hsound _ spec.pairOp _ _ 0 1 hdec).2 rfl]; simp

/-- A pair byte check is accepted exactly when both single-value checks are — the pack/split law. -/
theorem denseMkBytePair_iff_singles (bs : BusSemantics p) (facts : BusFacts p bs)
    (spec : ByteXorSpec p) (busId : Nat) (hspec : facts.byteXorSpec busId = some spec)
    (e₁ e₂ : DenseExpr p) (denv : VarId → ZMod p) :
    bs.accepts (denseBIEval (denseMkBytePair spec busId e₁ e₂) denv)
      ↔ bs.accepts (denseBIEval (denseMkByteCheck spec busId e₁) denv)
        ∧ bs.accepts (denseBIEval (denseMkByteCheck spec busId e₂) denv) := by
  rw [denseMkBytePair_accepted bs facts spec busId hspec,
      denseMkByteCheck_accepted bs facts spec busId hspec,
      denseMkByteCheck_accepted bs facts spec busId hspec]

/-- The two operands of an emitted pair check are payload entries. -/
theorem denseMkBytePair_operand_mem (spec : ByteXorSpec p) (busId : Nat) (e₁ e₂ : DenseExpr p) :
    e₁ ∈ (denseMkBytePair spec busId e₁ e₂).payload
      ∧ e₂ ∈ (denseMkBytePair spec busId e₁ e₂).payload := by
  have h := spec.decode_mem (denseMkBytePair spec busId e₁ e₂).payload
    (.const spec.pairOp) e₁ e₂ (.const 0) (spec.decode_encode _ _ _ _)
  exact ⟨h.1, h.2.1⟩

/-- An emitted pair check introduces no variable beyond its operands'. -/
theorem denseMkBytePair_payload_vars (spec : ByteXorSpec p) (busId : Nat) (e₁ e₂ : DenseExpr p)
    {x : VarId} (pe : DenseExpr p) (hpe : pe ∈ (denseMkBytePair spec busId e₁ e₂).payload)
    (hx : x ∈ pe.vars) : x ∈ e₁.vars ∨ x ∈ e₂.vars := by
  grind [denseMkBytePair, ByteXorSpec.encode_mem, DenseExpr.vars]

/-- An emitted pair check's variables are its two operands'. -/
theorem denseMkBytePair_vars (spec : ByteXorSpec p) (busId : Nat) (e₁ e₂ : DenseExpr p)
    {x : VarId} (hx : x ∈ denseBIVars (denseMkBytePair spec busId e₁ e₂)) :
    x ∈ e₁.vars ∨ x ∈ e₂.vars := by
  rw [denseBIVars, List.mem_append] at hx
  rcases hx with hm | hpp
  · simp only [denseMkBytePair, DenseExpr.vars, List.not_mem_nil] at hm
  · rw [List.mem_flatMap] at hpp
    obtain ⟨pe, hpe, hxe⟩ := hpp
    exact denseMkBytePair_payload_vars spec busId e₁ e₂ pe hpe hxe

/-! ## Decoded-field acceptance characterizations -/

/-- Lift `byteXorSpec_sound` to a *symbolic* dense interaction whose payload decodes to
    `(op, o₁, o₂, r)`: acceptance of `denseBIEval bi denv` is characterized by the decoded fields'
    evaluations. -/
theorem denseByteXorSpec_decode_iff (bs : BusSemantics p) (facts : BusFacts p bs)
    (spec : ByteXorSpec p) (bi : BusInteraction (DenseExpr p))
    (hspec : facts.byteXorSpec bi.busId = some spec)
    (op o1 o2 r : DenseExpr p) (hdec : spec.decode bi.payload = some (op, o1, o2, r))
    (denv : VarId → ZMod p) :
    (op.eval denv = spec.xorOp →
        (bs.accepts (denseBIEval bi denv) ↔
          (o1.eval denv).val < spec.bound ∧ (o2.eval denv).val < spec.bound
            ∧ (r.eval denv).val = Nat.xor (o1.eval denv).val (o2.eval denv).val)) ∧
    (op.eval denv = spec.pairOp →
        (bs.accepts (denseBIEval bi denv) ↔
          (o1.eval denv).val < spec.bound ∧ (o2.eval denv).val < spec.bound ∧ r.eval denv = 0)) := by
  obtain ⟨_, _, hsound⟩ := facts.byteXorSpec_sound bi.busId spec hspec
  have hdecEv : spec.decode (denseBIEval bi denv).payload
      = some (op.eval denv, o1.eval denv, o2.eval denv, r.eval denv) := by
    show spec.decode (bi.payload.map (fun e => e.eval denv)) = _
    rw [spec.decode_map, hdec]; rfl
  exact hsound (denseBIEval bi denv).payload (op.eval denv) (o1.eval denv) (o2.eval denv)
    (r.eval denv) (denseBIEval bi denv).multiplicity hdecEv

/-- The `byteBoolSound` analog of `denseByteXorSpec_decode_iff`. -/
theorem denseByteBoolSound_decode_iff (bs : BusSemantics p) (facts : BusFacts p bs)
    (spec : ByteXorSpec p) (bi : BusInteraction (DenseExpr p))
    (hspec : facts.byteXorSpec bi.busId = some spec)
    (op o1 o2 r : DenseExpr p) (hdec : spec.decode bi.payload = some (op, o1, o2, r))
    (denv : VarId → ZMod p) :
    (∀ oop, spec.orOp = some oop → op.eval denv = oop →
        (bs.accepts (denseBIEval bi denv) ↔
          (o1.eval denv).val < spec.bound ∧ (o2.eval denv).val < spec.bound
            ∧ (r.eval denv).val = Nat.lor (o1.eval denv).val (o2.eval denv).val)) ∧
    (∀ aop, spec.andOp = some aop → op.eval denv = aop →
        (bs.accepts (denseBIEval bi denv) ↔
          (o1.eval denv).val < spec.bound ∧ (o2.eval denv).val < spec.bound
            ∧ (r.eval denv).val = Nat.land (o1.eval denv).val (o2.eval denv).val)) := by
  have hdecEv : spec.decode (denseBIEval bi denv).payload
      = some (op.eval denv, o1.eval denv, o2.eval denv, r.eval denv) := by
    show spec.decode (bi.payload.map (fun e => e.eval denv)) = _
    rw [spec.decode_map, hdec]; rfl
  exact facts.byteBoolSound bi.busId spec hspec (denseBIEval bi denv).payload (op.eval denv)
    (o1.eval denv) (o2.eval denv) (r.eval denv) (denseBIEval bi denv).multiplicity hdecEv

/-! ## The NOT-form complement recognizer -/

/-- `255 − a` with no wraparound is the byte complement, hence `a`'s XOR with `255`. -/
theorem val_255_sub (hp : 256 ≤ p) (a : ZMod p) (ha : a.val < 256) :
    (255 - a).val = Nat.xor a.val 255 := by
  haveI : NeZero p := ⟨by omega⟩
  have hle : a.val ≤ 255 := by omega
  have ha' : a = ((a.val : ℕ) : ZMod p) := (ZMod.natCast_rightInverse a).symm
  have hcast : ((255 : ℕ) : ZMod p) = (255 : ZMod p) := by norm_cast
  have hval : (255 - a).val = 255 - a.val := by
    calc (255 - a).val
        = ((255 : ZMod p) - ((a.val : ℕ) : ZMod p)).val := by rw [← ha']
      _ = (((255 - a.val : ℕ) : ZMod p)).val := by rw [Nat.cast_sub hle, hcast]
      _ = 255 - a.val := ZMod.val_natCast_of_lt (by omega)
  rw [hval]; exact (nat_xor_255 _ ha).symm

/-- `(255 : ZMod p).val = 255` when `256 ≤ p`. -/
theorem val_255 (hp : 256 ≤ p) : (255 : ZMod p).val = 255 := by
  have hc : ((255 : ℕ) : ZMod p) = (255 : ZMod p) := by norm_cast
  rw [← hc, ZMod.val_natCast_of_lt (by omega)]

/-- Does `b` evaluate to the byte complement `255 − a` under every assignment. -/
theorem denseIsByteCompl_sound (a b : DenseExpr p) (h : denseIsByteCompl a b = true)
    (denv : VarId → ZMod p) : b.eval denv = 255 - a.eval denv := by
  unfold denseIsByteCompl at h
  have hc : (DenseExpr.add b (.mul (.const (-1)) (denseComplExpr a))).normalize.constValue?
      = some 0 := by simpa using h
  have h0 : (DenseExpr.add b (.mul (.const (-1)) (denseComplExpr a))).eval denv = 0 := by
    have := DenseExpr.constValue?_sound _ (0 : ZMod p) hc denv
    rwa [DenseExpr.normalize_eval] at this
  simp only [denseComplExpr, DenseExpr.eval] at h0
  linear_combination h0

/-! ## Membership helper -/

/-- A variable of a payload expression is a variable of the dense interaction. -/
theorem denseMem_biVars_of_payload (bi : BusInteraction (DenseExpr p)) (e : DenseExpr p)
    (he : e ∈ bi.payload) {v : VarId} (hv : v ∈ e.vars) : v ∈ denseBIVars bi := by
  rw [denseBIVars, List.mem_append]
  exact Or.inr (List.mem_flatMap.2 ⟨e, he, hv⟩)

/-! ## The shape classifier is sound -/

/-- `denseCmpStructural` hits pin evaluation. -/
theorem denseCmpStructural_sound (e : DenseExpr p) (c : ZMod p) (denv : VarId → ZMod p)
    (h : denseCmpStructural e c = true) : e.eval denv = c := by
  obtain rfl : e = DenseExpr.const c := by simpa [denseCmpStructural] using h
  rfl

/-- `denseCmpFolded` hits pin evaluation. -/
theorem denseCmpFolded_sound (e : DenseExpr p) (c : ZMod p) (denv : VarId → ZMod p)
    (h : denseCmpFolded e c = true) : e.eval denv = c :=
  e.constValue?_sound c (by simpa [denseCmpFolded] using h) denv

/-- A classifier hit is a stateless byte check on its shape's operands: they are payload entries,
    and acceptance is exactly "every operand is a byte" — for any `cmp` whose hits pin evaluation
    (`denseCmpStructural_sound` / `denseCmpFolded_sound`). One branch per shape. -/
theorem denseByteShape?_sound (bs : BusSemantics p) (facts : BusFacts p bs)
    {cmp : DenseExpr p → ZMod p → Bool}
    (hcmp : ∀ (e : DenseExpr p) (c : ZMod p) (denv : VarId → ZMod p),
      cmp e c = true → e.eval denv = c)
    (bi : BusInteraction (DenseExpr p)) (sh : DenseByteShape) (spec : ByteXorSpec p)
    (o1 o2 : DenseExpr p) (h : denseByteShape? cmp bs facts bi = some (sh, spec, o1, o2)) :
    bs.isStateful bi.busId = false ∧ (∀ e ∈ sh.operands o1 o2, e ∈ bi.payload) ∧
      ∀ denv, bs.accepts (denseBIEval bi denv) ↔
        ∀ e ∈ sh.operands o1 o2, (e.eval denv).val < 256 := by
  unfold denseByteShape? at h
  split at h
  · exact absurd h (by simp)
  · rename_i spec' hspec
    unfold denseByteShapeWith? at h
    split at h
    · rename_i hb
      have hbound : spec'.bound = 256 := of_decide_eq_true hb
      split at h
      · exact absurd h (by simp)
      · rename_i op o1' o2' r hdec
        have hstateless := (facts.byteXorSpec_sound bi.busId spec' hspec).1
        obtain ⟨hmemO1, hmemO2, -⟩ := spec'.decode_mem bi.payload op o1' o2' r hdec
        have key := denseByteXorSpec_decode_iff bs facts spec' bi hspec op o1' o2' r hdec
        split_ifs at h with hxor hA hB hC hD hE hor hOA hOB hpair <;>
            simp only [Option.some.injEq, Prod.mk.injEq] at h <;>
            obtain ⟨rfl, rfl, rfl, rfl⟩ := h <;>
            simp only [DenseByteShape.operands, List.forall_mem_cons, List.not_mem_nil,
              false_implies, forall_true_iff, and_true]
        · -- self-check: o₁ = o₂, r = 0
          obtain ⟨rfl, hr0⟩ : o1' = o2' ∧ cmp r 0 = true := by simpa using hA
          refine ⟨hstateless, hmemO1, fun denv => ?_⟩
          rw [(key denv).1 (hcmp op _ denv hxor), hbound, hcmp r 0 denv hr0, ZMod.val_zero]
          exact ⟨fun hh => hh.1, fun hh => ⟨hh, hh, (Nat.xor_self _).symm⟩⟩
        · -- XOR-with-zero: o₂ = 0, o₁ = r
          obtain ⟨hz, rfl⟩ : cmp o2' 0 = true ∧ o1' = r := by simpa using hB
          refine ⟨hstateless, hmemO1, fun denv => ?_⟩
          rw [(key denv).1 (hcmp op _ denv hxor), hbound, hcmp o2' 0 denv hz, ZMod.val_zero]
          exact ⟨fun hh => hh.1, fun hh => ⟨hh, by omega, (Nat.xor_zero _).symm⟩⟩
        · -- mirror XOR-with-zero: o₁ = 0, o₂ = r
          obtain ⟨hz, rfl⟩ : cmp o1' 0 = true ∧ o2' = r := by simpa using hC
          refine ⟨hstateless, hmemO2, fun denv => ?_⟩
          rw [(key denv).1 (hcmp op _ denv hxor), hbound, hcmp o1' 0 denv hz, ZMod.val_zero]
          exact ⟨fun hh => hh.2.1, fun hh => ⟨by omega, hh, (Nat.zero_xor _).symm⟩⟩
        · -- NOT-form: o₂ = 255, r = 255 − o₁
          obtain ⟨⟨hple, h255⟩, hcompl⟩ :
              (256 ≤ p ∧ cmp o2' 255 = true) ∧ denseIsByteCompl o1' r = true := by simpa using hD
          refine ⟨hstateless, hmemO1, fun denv => ?_⟩
          rw [(key denv).1 (hcmp op _ denv hxor), hbound, hcmp o2' 255 denv h255,
            denseIsByteCompl_sound o1' r hcompl denv, val_255 hple]
          exact ⟨fun hh => hh.1, fun hh => ⟨hh, by omega, val_255_sub hple _ hh⟩⟩
        · -- mirror NOT-form: o₁ = 255, r = 255 − o₂
          obtain ⟨⟨hple, h255⟩, hcompl⟩ :
              (256 ≤ p ∧ cmp o1' 255 = true) ∧ denseIsByteCompl o2' r = true := by simpa using hE
          refine ⟨hstateless, hmemO2, fun denv => ?_⟩
          rw [(key denv).1 (hcmp op _ denv hxor), hbound, hcmp o1' 255 denv h255,
            denseIsByteCompl_sound o2' r hcompl denv, val_255 hple]
          exact ⟨fun hh => hh.2.1, fun hh =>
            ⟨by omega, hh, by rw [val_255_sub hple _ hh]; exact Nat.xor_comm _ _⟩⟩
        · -- OR identity: o₂ = 0, o₁ = r
          obtain ⟨hz, rfl⟩ : cmp o2' 0 = true ∧ o1' = r := by simpa using hOA
          cases hoo : spec'.orOp with
          | none => rw [hoo] at hor; simp [Option.any] at hor
          | some oop =>
            rw [hoo] at hor; simp only [Option.any] at hor
            refine ⟨hstateless, hmemO1, fun denv => ?_⟩
            rw [(denseByteBoolSound_decode_iff bs facts spec' bi hspec op o1' o2' o1' hdec denv).1
                oop hoo (hcmp op oop denv hor), hbound, hcmp o2' 0 denv hz, ZMod.val_zero]
            exact ⟨fun hh => hh.1, fun hh => ⟨hh, by omega, by simp⟩⟩
        · -- mirror OR identity: o₁ = 0, o₂ = r
          obtain ⟨hz, rfl⟩ : cmp o1' 0 = true ∧ o2' = r := by simpa using hOB
          cases hoo : spec'.orOp with
          | none => rw [hoo] at hor; simp [Option.any] at hor
          | some oop =>
            rw [hoo] at hor; simp only [Option.any] at hor
            refine ⟨hstateless, hmemO2, fun denv => ?_⟩
            rw [(denseByteBoolSound_decode_iff bs facts spec' bi hspec op o1' o2' o2' hdec denv).1
                oop hoo (hcmp op oop denv hor), hbound, hcmp o1' 0 denv hz, ZMod.val_zero]
            exact ⟨fun hh => hh.2.1, fun hh => ⟨by omega, hh, by simp⟩⟩
        · -- packed pair: r = 0
          obtain ⟨hpc, hr0⟩ : cmp op spec'.pairOp = true ∧ cmp r 0 = true := by simpa using hpair
          refine ⟨hstateless, ⟨hmemO1, hmemO2⟩, fun denv => ?_⟩
          rw [(key denv).2 (hcmp op _ denv hpc), hbound]
          exact ⟨fun hh => ⟨hh.1, hh.2.1⟩, fun hh => ⟨hh.1, hh.2, hcmp r 0 denv hr0⟩⟩
    · exact absurd h (by simp)

/-! ## The single-value byte-check recognizer is sound -/

/-- A recognized single-value byte check is stateless, has multiplicity 1, its value is a payload
    entry, and its acceptance is exactly "the value is a byte". -/
theorem denseSvCheck?_sound (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (e : DenseExpr p)
    (h : denseSvCheck? bs facts bi = some e) :
    bs.isStateful bi.busId = false ∧ bi.multiplicity = DenseExpr.const 1 ∧ e ∈ bi.payload ∧
      (∀ denv, bs.accepts (denseBIEval bi denv) ↔ (e.eval denv).val < 256) := by
  unfold denseSvCheck? at h
  split at h
  · exact absurd h (by simp)
  · rename_i spec₀ hspec₀
    have hbs : denseByteShape? denseCmpStructural bs facts bi
        = denseByteShapeWith? denseCmpStructural spec₀ bi := by
      simp only [denseByteShape?, hspec₀]
    unfold denseSvCheckWith? at h
    split_ifs at h with hm
    cases hc : denseByteShapeWith? denseCmpStructural spec₀ bi with
    | none => rw [hc] at h; exact absurd h (by simp)
    | some t =>
      obtain ⟨sh, spec, o1, o2⟩ := t
      simp only [hc] at h
      obtain ⟨hst, hmem, hacc⟩ :=
        denseByteShape?_sound bs facts denseCmpStructural_sound bi sh spec o1 o2 (hbs.trans hc)
      cases hops : sh.operands o1 o2 with
      | nil => rw [hops] at h; exact absurd h (by simp)
      | cons a tl =>
        cases tl with
        | nil =>
          rw [hops] at h
          obtain rfl : a = e := by simpa using h
          exact ⟨hst, hm, hmem a (by simp [hops]), fun denv => by rw [hacc denv, hops]; simp⟩
        | cons b tl' => rw [hops] at h; exact absurd h (by simp)

/-! ## Correctness of one stateless two-for-one pack -/

/-- Replacing two stateless multiplicity-1 interactions `D₁`, `D₂` by one stateless multiplicity-1
    interaction `C` whose obligation is exactly their conjunction is `DensePassCorrect`; all three
    stateless, so the filtered side-effect/admissibility lists coincide (`ofEnvEq`). -/
theorem denseMergeStateless2_correct (isInput : VarId → Bool) (d : DenseConstraintSystem p)
    (bs : BusSemantics p) (hp1 : (1 : ZMod p) ≠ 0)
    (D₁ D₂ C : BusInteraction (DenseExpr p))
    (hst1 : bs.isStateful D₁.busId = false) (hst2 : bs.isStateful D₂.busId = false)
    (hstC : bs.isStateful C.busId = false)
    (hm1 : D₁.multiplicity = DenseExpr.const 1) (hm2 : D₂.multiplicity = DenseExpr.const 1)
    (hmC : C.multiplicity = DenseExpr.const 1)
    (hkey : ∀ denv, bs.accepts (denseBIEval C denv) ↔
        bs.accepts (denseBIEval D₁ denv) ∧
          bs.accepts (denseBIEval D₂ denv))
    (hbrk : ∀ denv, bs.maintainsInvariants (denseBIEval C denv))
    (hvars : ∀ v ∈ denseBIVars C, v ∈ denseBIVars D₁ ∨ v ∈ denseBIVars D₂)
    (pre mid post : List (BusInteraction (DenseExpr p)))
    (hsplit : d.busInteractions = pre ++ D₁ :: mid ++ D₂ :: post) :
    DensePassCorrect isInput d { d with busInteractions := pre ++ C :: mid ++ post } [] bs := by
  set out : DenseConstraintSystem p := { d with busInteractions := pre ++ C :: mid ++ post }
    with hout
  have houtb : out.busInteractions = pre ++ C :: mid ++ post := rfl
  set P : (VarId → ZMod p) → BusInteraction (DenseExpr p) → Prop :=
    fun denv bi => (denseBIEval bi denv).multiplicity ≠ 0 → bs.accepts (denseBIEval bi denv)
    with hP
  have hme1 : ∀ denv, (denseBIEval D₁ denv).multiplicity = 1 := fun denv => by
    show D₁.multiplicity.eval denv = 1; rw [hm1]; rfl
  have hme2 : ∀ denv, (denseBIEval D₂ denv).multiplicity = 1 := fun denv => by
    show D₂.multiplicity.eval denv = 1; rw [hm2]; rfl
  have hmeC : ∀ denv, (denseBIEval C denv).multiplicity = 1 := fun denv => by
    show C.multiplicity.eval denv = 1; rw [hmC]; rfl
  have hP1 : ∀ denv, (P denv D₁ ↔ bs.accepts (denseBIEval D₁ denv)) := fun denv =>
    ⟨fun h => h (by rw [hme1 denv]; exact hp1), fun h _ => h⟩
  have hP2 : ∀ denv, (P denv D₂ ↔ bs.accepts (denseBIEval D₂ denv)) := fun denv =>
    ⟨fun h => h (by rw [hme2 denv]; exact hp1), fun h _ => h⟩
  have hPC : ∀ denv, (P denv C ↔ bs.accepts (denseBIEval C denv)) := fun denv =>
    ⟨fun h => h (by rw [hmeC denv]; exact hp1), fun h _ => h⟩
  have hsatiff : ∀ denv, d.satisfies bs denv ↔ out.satisfies bs denv := by
    intro denv
    have hbus : (∀ bi ∈ d.busInteractions, P denv bi) ↔ (∀ bi ∈ out.busInteractions, P denv bi) := by
      rw [hsplit, houtb]
      simp only [List.forall_mem_append, List.forall_mem_cons]
      have hc := hPC denv; have h1 := hP1 denv; have h2 := hP2 denv; have hk := hkey denv
      tauto
    exact ⟨fun ⟨hcons, hb⟩ => ⟨hcons, hbus.1 hb⟩, fun ⟨hcons, hb⟩ => ⟨hcons, hbus.2 hb⟩⟩
  -- the stateful-filtered interaction lists coincide (all three are stateless)
  have hfilt : d.busInteractions.filter (fun bi => bs.isStateful bi.busId)
      = out.busInteractions.filter (fun bi => bs.isStateful bi.busId) := by
    rw [hsplit, houtb]
    simp only [List.filter_append, List.filter_cons, hst1, hst2, hstC, Bool.false_eq_true, if_false]
  have hside : ∀ denv, d.sideEffects bs denv = out.sideEffects bs denv := by
    intro denv
    refine funext (fun message => congrArg (multiplicitySum message) ?_)
    simp only [hfilt]
  have hstE1 : ∀ denv, bs.isStateful (denseBIEval D₁ denv).busId = false := fun _ => hst1
  have hstE2 : ∀ denv, bs.isStateful (denseBIEval D₂ denv).busId = false := fun _ => hst2
  have hstEC : ∀ denv, bs.isStateful (denseBIEval C denv).busId = false := fun _ => hstC
  have hadmarg : ∀ denv,
      (d.busInteractions.map (fun bi => denseBIEval bi denv)).filter
        (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId)
      = (out.busInteractions.map (fun bi => denseBIEval bi denv)).filter
        (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId) := by
    intro denv
    rw [hsplit, houtb]
    simp only [List.map_append, List.map_cons, List.filter_append, List.filter_cons,
      hstE1 denv, hstE2 denv, hstEC denv, Bool.and_false, Bool.false_eq_true, if_false]
  have hadm : ∀ denv, d.admissible bs denv ↔ out.admissible bs denv := by
    intro denv
    simp only [DenseConstraintSystem.admissible, hadmarg]
  have hmemD1 : D₁ ∈ d.busInteractions := by
    rw [hsplit]; simp only [List.mem_append, List.mem_cons]; tauto
  have hmemD2 : D₂ ∈ d.busInteractions := by
    rw [hsplit]; simp only [List.mem_append, List.mem_cons]; tauto
  have hmem : ∀ x, x ∈ pre ∨ x ∈ mid ∨ x ∈ post → x ∈ d.busInteractions := by
    intro x hx; rw [hsplit]; simp only [List.mem_append, List.mem_cons]; tauto
  have hsub : ∀ i ∈ out.occ, i ∈ d.occ := by
    intro i hi
    simp only [DenseConstraintSystem.occ, List.mem_append, List.mem_flatMap] at hi ⊢
    rcases hi with hi | ⟨bi, hbi, hibi⟩
    · exact Or.inl hi
    · rw [houtb] at hbi
      simp only [List.mem_append, List.mem_cons] at hbi
      rcases hbi with (h | rfl | h) | h
      · exact Or.inr ⟨bi, hmem bi (Or.inl h), hibi⟩
      · rcases hvars i hibi with h | h
        · exact Or.inr ⟨D₁, hmemD1, h⟩
        · exact Or.inr ⟨D₂, hmemD2, h⟩
      · exact Or.inr ⟨bi, hmem bi (Or.inr (Or.inl h)), hibi⟩
      · exact Or.inr ⟨bi, hmem bi (Or.inr (Or.inr h)), hibi⟩
  refine DensePassCorrect.ofEnvEq
    (fun denv hsat => ⟨(hsatiff denv).mpr hsat,
      (hside denv).symm⟩)
    (fun hgi denv hsat bi hbi => ?_)
    hsub
    (fun denv hadmE hsat => ⟨(hsatiff denv).mp hsat, (hadm denv).mp hadmE,
      by rw [hside denv]⟩)
  -- invariant preservation: `bi` is in `pre`/`mid`/`post` (defer to `d`) or is `C` (`hbrk`).
  rw [houtb] at hbi
  simp only [List.mem_append, List.mem_cons] at hbi
  rcases hbi with (h | rfl | h) | h
  · exact hgi denv ((hsatiff denv).mpr hsat) bi (hmem bi (Or.inl h))
  · exact fun _ => hbrk denv
  · exact hgi denv ((hsatiff denv).mpr hsat) bi (hmem bi (Or.inr (Or.inl h)))
  · exact hgi denv ((hsatiff denv).mpr hsat) bi (hmem bi (Or.inr (Or.inr h)))

/-! ## The re-checking recognizer -/

/-- `denseBpSv?` carries everything a pack needs: the bus's spec, the byte bound, statelessness,
    unit multiplicity, that the value is a payload entry, and the acceptance characterization. -/
theorem denseBpSv?_sound (bs : BusSemantics p) (facts : BusFacts p bs)
    {bi : BusInteraction (DenseExpr p)} {spec : ByteXorSpec p} {e : DenseExpr p}
    (h : denseBpSv? bs facts bi = some (spec, e)) :
    facts.byteXorSpec bi.busId = some spec ∧ spec.bound = 256 ∧
      bs.isStateful bi.busId = false ∧ bi.multiplicity = DenseExpr.const 1 ∧ e ∈ bi.payload ∧
      ∀ denv, bs.accepts (denseBIEval bi denv) ↔ (e.eval denv).val < 256 := by
  have key : facts.byteXorSpec bi.busId = some spec ∧ denseSvCheckWith? spec bi = some e := by
    unfold denseBpSv? at h
    split at h
    · exact absurd h (by simp)
    · rename_i spec' hspec
      cases hsv : denseSvCheckWith? spec' bi with
      | none => rw [hsv] at h; exact absurd h (by simp)
      | some e0 =>
        rw [hsv] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        exact ⟨by rw [hspec, h.1], by rw [← h.1, hsv, h.2]⟩
  obtain ⟨hspec, hsv⟩ := key
  have hsc : denseSvCheck? bs facts bi = some e := by
    unfold denseSvCheck?; rw [hspec]; exact hsv
  obtain ⟨hst, hm, hmem, hacc⟩ := denseSvCheck?_sound bs facts bi e hsc
  refine ⟨hspec, ?_, hst, hm, hmem, hacc⟩
  -- the shape recognizer only fires on the byte bound
  by_cases hb : spec.bound = 256
  · exact hb
  · exfalso; unfold denseSvCheckWith? denseByteShapeWith? at hsv; simp [hb] at hsv

/-! ## The obligation of one interaction -/

/-- The per-interaction obligation of `DenseConstraintSystem.satisfies`: a fired message is
    accepted. -/
def denseBIFires (bs : BusSemantics p) (denv : VarId → ZMod p)
    (bi : BusInteraction (DenseExpr p)) : Prop :=
  (denseBIEval bi denv).multiplicity ≠ 0 → bs.accepts (denseBIEval bi denv)

/-- A recognized single-value check fires exactly when its value is a byte. -/
theorem denseBIFires_sv (bs : BusSemantics p) (facts : BusFacts p bs) (hp1 : (1 : ZMod p) ≠ 0)
    {bi : BusInteraction (DenseExpr p)} {spec : ByteXorSpec p} {e : DenseExpr p}
    (h : denseBpSv? bs facts bi = some (spec, e)) (denv : VarId → ZMod p) :
    denseBIFires bs denv bi ↔ (e.eval denv).val < 256 := by
  obtain ⟨-, -, -, hm, -, hacc⟩ := denseBpSv?_sound bs facts h
  have hmul : (denseBIEval bi denv).multiplicity = 1 := by
    show bi.multiplicity.eval denv = 1; rw [hm]; rfl
  exact ⟨fun hh => (hacc denv).1 (hh (by rw [hmul]; exact hp1)),
    fun hh _ => (hacc denv).2 hh⟩

/-- An emitted pair check fires exactly when both its operands are bytes. -/
theorem denseBIFires_pair (bs : BusSemantics p) (facts : BusFacts p bs) (hp1 : (1 : ZMod p) ≠ 0)
    {spec : ByteXorSpec p} {busId : Nat} (hspec : facts.byteXorSpec busId = some spec)
    (hbound : spec.bound = 256) (e₁ e₂ : DenseExpr p) (denv : VarId → ZMod p) :
    denseBIFires bs denv (denseMkBytePair spec busId e₁ e₂)
      ↔ ((e₁.eval denv).val < 256 ∧ (e₂.eval denv).val < 256) := by
  have hacc := denseMkBytePair_accepted bs facts spec busId hspec e₁ e₂ denv
  rw [hbound] at hacc
  have hmul : (denseBIEval (denseMkBytePair spec busId e₁ e₂) denv).multiplicity = 1 := rfl
  exact ⟨fun hh => hacc.1 (hh (by rw [hmul]; exact hp1)), fun hh _ => hacc.2 hh⟩

/-! ## The applier's held drops -/

/-- `denseBpTake` removes exactly one entry, keyed by the bus it was asked for. -/
theorem denseBpTake_perm (busId : Nat) :
    ∀ (dropped : List (DenseBpDrop p)) (e : DenseExpr p) (b : BusInteraction (DenseExpr p))
      (dropped' : List (DenseBpDrop p)),
      denseBpTake busId dropped = some (e, b, dropped') →
      dropped.Perm ((busId, e, b) :: dropped') := by
  intro dropped
  induction dropped with
  | nil => intro _ _ _ h; exact absurd h (by simp [denseBpTake])
  | cons q rest ih =>
    obtain ⟨k, ev, bv⟩ := q
    intro e b dropped' h
    rw [denseBpTake] at h
    split_ifs at h with hk
    · subst hk
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact List.Perm.refl _
    · cases ht : denseBpTake busId rest with
      | none => rw [ht] at h; exact absurd h (by simp)
      | some r =>
        obtain ⟨e0, b0, rest0⟩ := r
        rw [ht] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨h1, h2, h3⟩ := h
        subst h3
        rw [← h1, ← h2]
        exact ((ih e0 b0 rest0 ht).cons (k, ev, bv)).trans (List.Perm.swap _ _ _)

/-- A drop's membership predicate, transported along `denseBpTake`. -/
theorem denseBpTake_forall {busId : Nat} {dropped dropped' : List (DenseBpDrop p)}
    {ev : DenseExpr p} {bv : BusInteraction (DenseExpr p)} {F : DenseBpDrop p → Prop}
    (h : denseBpTake busId dropped = some (ev, bv, dropped')) :
    (∀ q ∈ dropped, F q) ↔ (F (busId, ev, bv) ∧ ∀ q ∈ dropped', F q) := by
  have hperm := denseBpTake_perm busId dropped ev bv dropped' h
  constructor
  · intro hh
    exact ⟨hh _ (hperm.mem_iff.2 List.mem_cons_self),
      fun q hq => hh q (hperm.mem_iff.2 (List.mem_cons_of_mem _ hq))⟩
  · rintro ⟨h1, h2⟩ q hq
    rcases List.mem_cons.1 (hperm.mem_iff.1 hq) with rfl | hq'
    · exact h1
    · exact h2 q hq'

/-! ## The applier preserves the obligations, the stateful trace, and the variables -/

/-- The output's obligations plus the held drops' are exactly the input's plus the incoming
    accumulator's and drops'. This is the pack/split law, threaded through the whole sweep. -/
theorem denseBpBack_fires (bs : BusSemantics p) (facts : BusFacts p bs) (hp1 : (1 : ZMod p) ≠ 0)
    (denv : VarId → ZMod p) :
    ∀ (L : List (BusInteraction (DenseExpr p))) (plan : List DenseBpAction)
      (dropped : List (DenseBpDrop p)) (out : List (BusInteraction (DenseExpr p))),
      ((∀ x ∈ (denseBpBack bs facts L plan dropped out).2, denseBIFires bs denv x) ∧
          ∀ q ∈ (denseBpBack bs facts L plan dropped out).1, (q.2.1.eval denv).val < 256)
        ↔ ((∀ x ∈ L, denseBIFires bs denv x) ∧ (∀ x ∈ out, denseBIFires bs denv x) ∧
            ∀ q ∈ dropped, (q.2.1.eval denv).val < 256) := by
  intro L
  induction L with
  | nil => intro plan dropped out; rw [denseBpBack]; simp
  | cons b rest ih =>
    intro plan dropped out
    rw [denseBpBack]
    split
    · rw [ih]; simp only [List.forall_mem_cons]; tauto
    · split
      · rename_i spec e hsv
        have hb := denseBIFires_sv bs facts hp1 hsv denv
        rw [ih]; simp only [List.forall_mem_cons]; tauto
      · rw [ih]; simp only [List.forall_mem_cons]; tauto
    · split
      · rename_i spec e hsv
        have hb := denseBIFires_sv bs facts hp1 hsv denv
        obtain ⟨hspec, hbound, -, -, -, -⟩ := denseBpSv?_sound bs facts hsv
        split
        · rename_i e' b' dropped' ht
          have hdrop := denseBpTake_forall (F := fun q => (q.2.1.eval denv).val < 256) ht
          have hpair := denseBIFires_pair bs facts hp1 hspec hbound e e' denv
          rw [ih, hdrop]; simp only [List.forall_mem_cons]; tauto
        · rw [ih]; simp only [List.forall_mem_cons]; tauto
      · rw [ih]; simp only [List.forall_mem_cons]; tauto

/-- The stateful interactions come through the sweep untouched, in order. -/
theorem denseBpBack_filter (bs : BusSemantics p) (facts : BusFacts p bs) :
    ∀ (L : List (BusInteraction (DenseExpr p))) (plan : List DenseBpAction)
      (dropped : List (DenseBpDrop p)) (out : List (BusInteraction (DenseExpr p))),
      (denseBpBack bs facts L plan dropped out).2.filter (fun bi => bs.isStateful bi.busId)
        = L.reverse.filter (fun bi => bs.isStateful bi.busId)
          ++ out.filter (fun bi => bs.isStateful bi.busId) := by
  intro L
  induction L with
  | nil => intro plan dropped out; rw [denseBpBack]; simp
  | cons b rest ih =>
    intro plan dropped out
    rw [denseBpBack]
    have hkeep : ∀ (l : List (BusInteraction (DenseExpr p))),
        rest.reverse.filter (fun bi => bs.isStateful bi.busId) ++
            (b :: l).filter (fun bi => bs.isStateful bi.busId)
          = (b :: rest).reverse.filter (fun bi => bs.isStateful bi.busId) ++
            l.filter (fun bi => bs.isStateful bi.busId) := by
      intro l
      simp only [List.reverse_cons, List.filter_append, List.filter_cons, List.filter_nil,
        List.append_assoc]
      split <;> rfl
    have hdropped : ∀ (l : List (BusInteraction (DenseExpr p))),
        bs.isStateful b.busId = false →
        rest.reverse.filter (fun bi => bs.isStateful bi.busId) ++
            l.filter (fun bi => bs.isStateful bi.busId)
          = (b :: rest).reverse.filter (fun bi => bs.isStateful bi.busId) ++
            l.filter (fun bi => bs.isStateful bi.busId) := by
      intro l hst
      simp only [List.reverse_cons, List.filter_append, List.filter_cons, hst,
        Bool.false_eq_true, if_false, List.filter_nil, List.append_nil]
    split
    · rw [ih]; exact hkeep out
    · split
      · rename_i spec e hsv
        obtain ⟨-, -, hst, -, -, -⟩ := denseBpSv?_sound bs facts hsv
        rw [ih]; exact hdropped out hst
      · rw [ih]; exact hkeep out
    · split
      · rename_i spec e hsv
        obtain ⟨-, -, hst, -, -, -⟩ := denseBpSv?_sound bs facts hsv
        split
        · rename_i e' b' dropped' ht
          rw [ih]
          have hstP : bs.isStateful (denseMkBytePair spec b.busId e e').busId = false := hst
          rw [List.filter_cons, if_neg (by rw [hstP]; simp)]
          exact hdropped out hst
        · rw [ih]; exact hkeep out
      · rw [ih]; exact hkeep out

/-- Every variable the sweep emits already occurs in the input, the incoming accumulator, or a
    held drop's source interaction. -/
theorem denseBpBack_vars (bs : BusSemantics p) (facts : BusFacts p bs) :
    ∀ (L : List (BusInteraction (DenseExpr p))) (plan : List DenseBpAction)
      (dropped : List (DenseBpDrop p)) (out : List (BusInteraction (DenseExpr p))),
      (∀ q ∈ dropped, q.2.1 ∈ q.2.2.payload) →
      ∀ x ∈ (denseBpBack bs facts L plan dropped out).2, ∀ v ∈ denseBIVars x,
        (∃ y ∈ L, v ∈ denseBIVars y) ∨ (∃ y ∈ out, v ∈ denseBIVars y) ∨
          ∃ q ∈ dropped, v ∈ denseBIVars q.2.2 := by
  intro L
  induction L with
  | nil =>
    intro plan dropped out _ x hx v hv
    rw [denseBpBack] at hx; exact Or.inr (Or.inl ⟨x, hx, hv⟩)
  | cons b rest ih =>
    intro plan dropped out hpay x hx v hv
    have hkeep : x ∈ (denseBpBack bs facts rest plan.tail dropped (b :: out)).2 →
        (∃ y ∈ b :: rest, v ∈ denseBIVars y) ∨ (∃ y ∈ out, v ∈ denseBIVars y) ∨
          ∃ q ∈ dropped, v ∈ denseBIVars q.2.2 := by
      intro hxo
      rcases ih plan.tail dropped (b :: out) hpay x hxo v hv with h | h | h
      · obtain ⟨y, hy, hvy⟩ := h; exact Or.inl ⟨y, List.mem_cons_of_mem _ hy, hvy⟩
      · obtain ⟨y, hy, hvy⟩ := h
        rcases List.mem_cons.1 hy with rfl | hy'
        · exact Or.inl ⟨y, List.mem_cons_self, hvy⟩
        · exact Or.inr (Or.inl ⟨y, hy', hvy⟩)
      · exact Or.inr (Or.inr h)
    rw [denseBpBack] at hx
    split at hx
    · exact hkeep hx
    · split at hx
      · rename_i spec e hsv
        obtain ⟨-, -, -, -, hmem, -⟩ := denseBpSv?_sound bs facts hsv
        have hpay' : ∀ q ∈ ((b.busId, e, b) :: dropped), q.2.1 ∈ q.2.2.payload := by
          intro q hq; rcases List.mem_cons.1 hq with rfl | hq'
          · exact hmem
          · exact hpay q hq'
        rcases ih plan.tail ((b.busId, e, b) :: dropped) out hpay' x hx v hv with h | h | h
        · obtain ⟨y, hy, hvy⟩ := h; exact Or.inl ⟨y, List.mem_cons_of_mem _ hy, hvy⟩
        · exact Or.inr (Or.inl h)
        · obtain ⟨q, hq, hvq⟩ := h
          rcases List.mem_cons.1 hq with rfl | hq'
          · exact Or.inl ⟨b, List.mem_cons_self, hvq⟩
          · exact Or.inr (Or.inr ⟨q, hq', hvq⟩)
      · exact hkeep hx
    · split at hx
      · rename_i spec e hsv
        obtain ⟨-, -, -, -, hmem, -⟩ := denseBpSv?_sound bs facts hsv
        split at hx
        · rename_i e' b' dropped' ht
          have hperm := denseBpTake_perm b.busId dropped e' b' dropped' ht
          have hmem' : (b.busId, e', b') ∈ dropped := hperm.mem_iff.2 List.mem_cons_self
          have hpay'' : ∀ q ∈ dropped', q.2.1 ∈ q.2.2.payload := fun q hq =>
            hpay q (hperm.mem_iff.2 (List.mem_cons_of_mem _ hq))
          rcases ih plan.tail dropped' (denseMkBytePair spec b.busId e e' :: out) hpay''
            x hx v hv with h | h | h
          · obtain ⟨y, hy, hvy⟩ := h; exact Or.inl ⟨y, List.mem_cons_of_mem _ hy, hvy⟩
          · obtain ⟨y, hy, hvy⟩ := h
            rcases List.mem_cons.1 hy with rfl | hy'
            · rcases denseMkBytePair_vars spec b.busId e e' hvy with hve | hve
              · exact Or.inl ⟨b, List.mem_cons_self, denseMem_biVars_of_payload b e hmem hve⟩
              · exact Or.inr (Or.inr ⟨(b.busId, e', b'), hmem',
                  denseMem_biVars_of_payload b' e' (hpay _ hmem') hve⟩)
            · exact Or.inr (Or.inl ⟨y, hy', hvy⟩)
          · obtain ⟨q, hq, hvq⟩ := h
            exact Or.inr (Or.inr ⟨q, hperm.mem_iff.2 (List.mem_cons_of_mem _ hq), hvq⟩)
        · exact hkeep hx
      · exact hkeep hx

/-- Every interaction the sweep emits either comes from the input or the incoming accumulator, or
    is a pair check, which breaks no invariant. -/
theorem denseBpBack_src (bs : BusSemantics p) (facts : BusFacts p bs) :
    ∀ (L : List (BusInteraction (DenseExpr p))) (plan : List DenseBpAction)
      (dropped : List (DenseBpDrop p)) (out : List (BusInteraction (DenseExpr p))),
      ∀ x ∈ (denseBpBack bs facts L plan dropped out).2,
        (∀ denv, bs.maintainsInvariants (denseBIEval x denv)) ∨ x ∈ L ∨ x ∈ out := by
  intro L
  induction L with
  | nil =>
    intro plan dropped out x hx; rw [denseBpBack] at hx; exact Or.inr (Or.inr hx)
  | cons b rest ih =>
    intro plan dropped out x hx
    have hkeep : ∀ dd : List (DenseBpDrop p),
        x ∈ (denseBpBack bs facts rest plan.tail dd (b :: out)).2 →
        (∀ denv, bs.maintainsInvariants (denseBIEval x denv)) ∨ x ∈ b :: rest ∨ x ∈ out := by
      intro dd hxo
      rcases ih plan.tail dd (b :: out) x hxo with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (List.mem_cons_of_mem _ h))
      · rcases List.mem_cons.1 h with rfl | h'
        · exact Or.inr (Or.inl List.mem_cons_self)
        · exact Or.inr (Or.inr h')
    rw [denseBpBack] at hx
    split at hx
    · exact hkeep dropped hx
    · split at hx
      · rename_i spec e hsv
        rcases ih plan.tail ((b.busId, e, b) :: dropped) out x hx with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl (List.mem_cons_of_mem _ h))
        · exact Or.inr (Or.inr h)
      · exact hkeep dropped hx
    · split at hx
      · rename_i spec e hsv
        obtain ⟨hspec, -, -, -, -, -⟩ := denseBpSv?_sound bs facts hsv
        split at hx
        · rename_i e' b' dropped' ht
          rcases ih plan.tail dropped' (denseMkBytePair spec b.busId e e' :: out) x hx with
            h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl (List.mem_cons_of_mem _ h))
          · rcases List.mem_cons.1 h with rfl | h'
            · exact Or.inl fun denv =>
                denseMkBytePair_breaks bs facts spec b.busId hspec e e' denv
            · exact Or.inr (Or.inr h')
        · exact hkeep dropped hx
      · exact hkeep dropped hx

/-! ## The whole sweep, and the bulk refinement it justifies -/

/-- The sweep either returns its input or is one complete `denseBpBack` run with no drop left. -/
theorem denseBytePackBis_run (bs : BusSemantics p) (facts : BusFacts p bs)
    (bis : List (BusInteraction (DenseExpr p))) :
    denseBytePackBis bs facts bis = bis ∨
      ∃ plan, denseBpBack bs facts bis.reverse plan [] []
        = ([], denseBytePackBis bs facts bis) := by
  unfold denseBytePackBis
  split
  · exact Or.inl rfl
  · rename_i revPlan _
    split
    · rename_i out hback; exact Or.inr ⟨revPlan, hback⟩
    · exact Or.inl rfl

/-- The four facts the sweep's output enjoys against its input. -/
theorem denseBytePackBis_facts (bs : BusSemantics p) (facts : BusFacts p bs)
    (hp1 : (1 : ZMod p) ≠ 0) (bis : List (BusInteraction (DenseExpr p))) :
    (∀ denv, (∀ x ∈ bis, denseBIFires bs denv x)
        ↔ ∀ x ∈ denseBytePackBis bs facts bis, denseBIFires bs denv x) ∧
      bis.filter (fun bi => bs.isStateful bi.busId)
        = (denseBytePackBis bs facts bis).filter (fun bi => bs.isStateful bi.busId) ∧
      (∀ x ∈ denseBytePackBis bs facts bis, ∀ v ∈ denseBIVars x, ∃ y ∈ bis, v ∈ denseBIVars y) ∧
      ∀ x ∈ denseBytePackBis bs facts bis,
        (∀ denv, bs.maintainsInvariants (denseBIEval x denv)) ∨ x ∈ bis := by
  rcases denseBytePackBis_run bs facts bis with hid | ⟨plan, hrun⟩
  · rw [hid]
    exact ⟨fun _ => Iff.rfl, rfl, fun x hx v hv => ⟨x, hx, hv⟩, fun x hx => Or.inr hx⟩
  · refine ⟨fun denv => ?_, ?_, fun x hx v hv => ?_, fun x hx => ?_⟩
    · have h := denseBpBack_fires bs facts hp1 denv bis.reverse plan [] []
      rw [hrun] at h
      simp only [List.not_mem_nil, false_implies, implies_true, and_true,
        List.mem_reverse] at h
      exact h.symm
    · have h := denseBpBack_filter bs facts bis.reverse plan [] []
      rw [hrun] at h
      simpa using h.symm
    · have h := denseBpBack_vars bs facts bis.reverse plan [] [] (by simp)
      rw [hrun] at h
      rcases h x hx v hv with hy | hy | hy
      · obtain ⟨y, hy, hvy⟩ := hy; exact ⟨y, List.mem_reverse.1 hy, hvy⟩
      · obtain ⟨y, hy, -⟩ := hy; exact absurd hy (by simp)
      · obtain ⟨q, hq, -⟩ := hy; exact absurd hq (by simp)
    · have h := denseBpBack_src bs facts bis.reverse plan [] []
      rw [hrun] at h
      rcases h x hx with hy | hy | hy
      · exact Or.inl hy
      · exact Or.inr (List.mem_reverse.1 hy)
      · exact absurd hy (by simp)

/-- Replacing the bus interactions by a list carrying the same per-interaction obligations, the
    same stateful trace and no new variable is `DensePassCorrect` — the bulk form of a stateless
    swap, generalizing `denseMergeStateless2_correct` to a whole rebuilt list. -/
theorem denseBulkStateless_correct (isInput : VarId → Bool) (d : DenseConstraintSystem p)
    (bs : BusSemantics p) (newBis : List (BusInteraction (DenseExpr p)))
    (hfires : ∀ denv, (∀ x ∈ d.busInteractions, denseBIFires bs denv x)
      ↔ ∀ x ∈ newBis, denseBIFires bs denv x)
    (hfilt : d.busInteractions.filter (fun bi => bs.isStateful bi.busId)
      = newBis.filter (fun bi => bs.isStateful bi.busId))
    (hvars : ∀ x ∈ newBis, ∀ v ∈ denseBIVars x, ∃ y ∈ d.busInteractions, v ∈ denseBIVars y)
    (hbrk : ∀ x ∈ newBis, (∀ denv, bs.maintainsInvariants (denseBIEval x denv))
      ∨ x ∈ d.busInteractions) :
    DensePassCorrect isInput d { d with busInteractions := newBis } [] bs := by
  set out : DenseConstraintSystem p := { d with busInteractions := newBis } with hout
  have houtb : out.busInteractions = newBis := rfl
  have hsatiff : ∀ denv, d.satisfies bs denv ↔ out.satisfies bs denv := fun denv =>
    ⟨fun h => ⟨h.1, (hfires denv).1 h.2⟩, fun h => ⟨h.1, (hfires denv).2 h.2⟩⟩
  have hside : ∀ denv, d.sideEffects bs denv = out.sideEffects bs denv := by
    intro denv
    refine funext (fun message => congrArg (multiplicitySum message) ?_)
    rw [houtb, hfilt]
  have hfiltEval : ∀ (L : List (BusInteraction (DenseExpr p))) (denv : VarId → ZMod p),
      (L.map (fun bi => denseBIEval bi denv)).filter
          (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId)
        = ((L.filter (fun bi => bs.isStateful bi.busId)).map (fun bi => denseBIEval bi denv)).filter
          (fun m => decide (m.multiplicity ≠ 0)) := by
    intro L denv
    induction L with
    | nil => rfl
    | cons a t ih =>
      have hbus : (denseBIEval a denv).busId = a.busId := rfl
      by_cases hst : bs.isStateful a.busId = true
      · simp only [List.map_cons, List.filter_cons, hbus, hst, Bool.and_true, if_true, ih]
      · simp only [Bool.not_eq_true] at hst
        simp only [List.map_cons, List.filter_cons, hbus, hst, Bool.and_false,
          Bool.false_eq_true, if_false, ih]
  have hadm : ∀ denv, d.admissible bs denv ↔ out.admissible bs denv := by
    intro denv
    simp only [DenseConstraintSystem.admissible, hfiltEval, houtb, hfilt]
  have hsub : ∀ i ∈ out.occ, i ∈ d.occ := by
    intro i hi
    simp only [DenseConstraintSystem.occ, List.mem_append, List.mem_flatMap] at hi ⊢
    rcases hi with hi | ⟨bi, hbi, hibi⟩
    · exact Or.inl hi
    · obtain ⟨y, hy, hvy⟩ := hvars bi hbi i hibi
      exact Or.inr ⟨y, hy, hvy⟩
  refine DensePassCorrect.ofEnvEq
    (fun denv hsat => ⟨(hsatiff denv).mpr hsat, (hside denv).symm⟩)
    (fun hgi denv hsat bi hbi => ?_)
    hsub
    (fun denv hadmE hsat => ⟨(hsatiff denv).mp hsat, (hadm denv).mp hadmE, by rw [hside denv]⟩)
  rcases hbrk bi hbi with hmi | hmem
  · exact fun _ => hmi denv
  · exact hgi denv ((hsatiff denv).mpr hsat) bi hmem

/-! ## The dense `bytePack` pass: one certified sweep -/

/-- Coverage is variable containment: a bus interaction is covered exactly when all its variables
    are valid. -/
theorem denseBICovered_iff (reg : VarRegistry) (bi : BusInteraction (DenseExpr p)) :
    denseBICovered reg bi ↔ ∀ v ∈ denseBIVars bi, reg.Valid v := by
  simp only [denseBICovered, denseBIVars, DenseExpr.CoveredBy, List.forall_mem_append,
    List.forall_mem_flatMap]

/-- The sweep emits no variable the input did not have, so it stays covered. -/
theorem denseBytePackBis_covered (reg : VarRegistry) (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg)
    (hp1 : (1 : ZMod p) ≠ 0) :
    ({ d with busInteractions := denseBytePackBis bs facts d.busInteractions } :
      DenseConstraintSystem p).CoveredBy reg := by
  obtain ⟨hac, hbi⟩ := hcov
  refine ⟨hac, fun x hx => (denseBICovered_iff reg x).2 (fun v hv => ?_)⟩
  obtain ⟨y, hy, hvy⟩ := (denseBytePackBis_facts bs facts hp1 d.busInteractions).2.2.1 x hx v hv
  exact (denseBICovered_iff reg y).1 (hbi y hy) v hvy

/-- The sweep is a refinement: the pair check it emits carries exactly the two single-value
    checks' obligations, every interaction is stateless, and no variable is new. -/
theorem denseBytePackBis_correct (isInput : VarId → Bool) (bs : BusSemantics p)
    (facts : BusFacts p bs) (hp1 : (1 : ZMod p) ≠ 0) (d : DenseConstraintSystem p) :
    DensePassCorrect isInput d
      { d with busInteractions := denseBytePackBis bs facts d.busInteractions } [] bs := by
  obtain ⟨hfires, hfilt, hvars, hbrk⟩ := denseBytePackBis_facts bs facts hp1 d.busInteractions
  exact denseBulkStateless_correct isInput d bs _ hfires hfilt hvars hbrk

/-- The dense single-value byte-check packing pass (see `denseBytePackBis`,
    `ByteCheckPack.lean`). -/
def denseByteCheckPackPass : DenseVerifiedPassW p :=
  DenseVerifiedPassW.ofDenseStep (fun reg bs facts d hcov =>
    if hp1 : (1 : ZMod p) ≠ 0 then
      DenseNativeStep.ofSame bs (denseBytePackBis_covered reg bs facts d hcov hp1)
        (denseBytePackBis_correct reg.isInput bs facts hp1 d)
    else DenseNativeStep.refl bs hcov)

end ApcOptimizer.Dense
