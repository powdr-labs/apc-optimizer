import ApcOptimizer.Implementation.OptimizerPasses.BusPairCancelCheck
import ApcOptimizer.Implementation.OptimizerPasses.BusPairCancelCore
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.BusPairCancelIndex

set_option autoImplicit false

/-! # Soundness of the dense emit slice for `busPairCancel`

Soundness for the receive scan + emitted checks defined in `BusPairCancelCheck.lean`, over
`VarId → ZMod p`. The capstone `denseCheckCancel_sound` discharges the full hypothesis list of
`denseDropPair_correct`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- A match at `j` is strictly after `i` and live, recovered from the search's own guard. -/
theorem denseFirstMatchAt_spec (M : Thunk (DenseEqConstraintMap p))
    (arr : Array (BusInteraction (DenseExpr p))) (alive : Array Bool) (busId : Nat)
    (S : BusInteraction (DenseExpr p)) (i : Nat) :
    ∀ (l : List Nat) {j : Nat}, denseFirstMatchAt M arr alive busId S i l = some j →
      i < j ∧ alive[j]?.getD false = true := by
  intro l
  induction l with
  | nil => intro j h; simp [denseFirstMatchAt] at h
  | cons hd tl ih =>
    intro j h
    rw [denseFirstMatchAt] at h
    split at h
    · rename_i hcond
      rw [Bool.and_eq_true] at hcond
      split at h
      · split at h
        · obtain rfl := Option.some.inj h
          exact ⟨of_decide_eq_true hcond.1, hcond.2⟩
        · exact ih h
      · exact ih h
    · exact ih h

/-- The evaluation of an emitted single-value byte check. -/
theorem denseMkByteCheck_eval (spec : ByteXorSpec p) (busId : Nat) (e : DenseExpr p)
    (denv : VarId → ZMod p) :
    denseBIEval (denseMkByteCheck spec busId e) denv
      = { busId := busId, multiplicity := 1,
          payload := spec.encode spec.xorOp (e.eval denv) (e.eval denv) 0 } := by
  simp only [denseMkByteCheck, denseBIEval, spec.encode_map, DenseExpr.eval]

/-- An emitted single-value byte check breaks no invariant. -/
theorem denseMkByteCheck_breaks (bs : BusSemantics p) (facts : BusFacts p bs)
    (spec : ByteXorSpec p) (busId : Nat) (hspec : facts.byteXorSpec busId = some spec)
    (e : DenseExpr p) (denv : VarId → ZMod p) :
    bs.maintainsInvariants (denseBIEval (denseMkByteCheck spec busId e) denv) := by
  obtain ⟨_, hbreak, _⟩ := facts.byteXorSpec_sound busId spec hspec
  rw [denseMkByteCheck_eval]; exact hbreak _

/-- A single-value byte check is accepted exactly when its operand is a byte. -/
theorem denseMkByteCheck_accepted (bs : BusSemantics p) (facts : BusFacts p bs)
    (spec : ByteXorSpec p) (busId : Nat) (hspec : facts.byteXorSpec busId = some spec)
    (e : DenseExpr p) (denv : VarId → ZMod p) :
    bs.accepts (denseBIEval (denseMkByteCheck spec busId e) denv)
      ↔ (e.eval denv).val < spec.bound := by
  obtain ⟨_, _, hsound⟩ := facts.byteXorSpec_sound busId spec hspec
  rw [denseMkByteCheck_eval]
  have hdec : spec.decode (spec.encode spec.xorOp (e.eval denv) (e.eval denv) 0)
      = some (spec.xorOp, e.eval denv, e.eval denv, (0 : ZMod p)) := spec.decode_encode _ _ _ _
  rw [(hsound _ spec.xorOp _ _ 0 1 hdec).1 rfl]
  have hx : (0 : ZMod p).val = Nat.xor (e.eval denv).val (e.eval denv).val := by
    rw [ZMod.val_zero]; exact (Nat.xor_self _).symm
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, h, hx⟩

/-- An emitted byte check introduces no variable beyond its operand's. -/
theorem denseMkByteCheck_payload_vars (spec : ByteXorSpec p) (busId : Nat) (e : DenseExpr p)
    {x : VarId} (pe : DenseExpr p) (hpe : pe ∈ (denseMkByteCheck spec busId e).payload)
    (hx : x ∈ pe.vars) : x ∈ e.vars := by
  simp only [denseMkByteCheck] at hpe
  rcases spec.encode_mem _ _ _ _ pe hpe with h | h | h | h <;> rw [h] at hx <;>
    first | exact hx | (simp only [DenseExpr.vars, List.not_mem_nil] at hx)

/-- A passing emit certificate makes the check stateless, implied by `R`'s own accepted receive,
    invariant-free, and adding no `VarId`s — `denseDropPair_correct`'s per-check `hchecks` element. -/
theorem denseEmitOk_sound (ops : DenseZModOps p) (bs : BusSemantics p)
    (facts : BusFacts p bs) (busId : Nat)
    (shape : MemoryBusShape) (slots : List Nat) (R ck : BusInteraction (DenseExpr p))
    (h : denseEmitOk ops bs facts busId shape slots R ck = true)
    (hRbus : R.busId = busId)
    (hRmEv : ∀ denv, (denseBIEval R denv).multiplicity = -shape.setNewMult) :
    bs.isStateful ck.busId = false ∧
    (∀ denv, bs.accepts (denseBIEval R denv) →
      bs.accepts (denseBIEval ck denv)) ∧
    (∀ denv, bs.maintainsInvariants (denseBIEval ck denv)) ∧
    (∀ v ∈ denseBIVars ck, v ∈ denseBIVars R) := by
  unfold denseEmitOk at h
  rw [ops.one_eq, ops.zero_eq, denseGetPreviousMult_eq ops shape] at h
  split at h
  · exact absurd h (by simp)
  · rename_i spec hspec
    rw [Bool.and_eq_true, Bool.and_eq_true] at h
    obtain ⟨⟨hbd, hmultd⟩, hrest⟩ := h
    have hbound : spec.bound = 256 := of_decide_eq_true hbd
    have hmult := of_decide_eq_true hmultd
    have hstateless := (facts.byteXorSpec_sound ck.busId spec hspec).1
    split at hrest
    · rename_i op o1 o2 r hdec
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hrest
      obtain ⟨⟨⟨hopd, ho12d⟩, hrd⟩, hany⟩ := hrest
      have hop := of_decide_eq_true hopd
      have ho12 := of_decide_eq_true ho12d
      have hr := of_decide_eq_true hrd
      obtain ⟨slot, hslotmem, hslot⟩ := List.any_eq_true.1 hany
      rw [Bool.and_eq_true] at hslot
      obtain ⟨hgetd, hbnd⟩ := hslot
      have hget := of_decide_eq_true hgetd
      have hckeq : ck = denseMkByteCheck spec ck.busId o1 := by
        obtain ⟨ckBus, ckMul, ckPay⟩ := ck
        have hpay : ckPay = spec.encode (.const spec.xorOp) o1 o1 (.const 0) := by
          have he := spec.decode_eq_encode ckPay op o1 o2 r hdec
          rw [hop, ← ho12, hr] at he; exact he
        have hm' : ckMul = DenseExpr.const 1 := hmult
        show ({ busId := ckBus, multiplicity := ckMul, payload := ckPay } :
          BusInteraction (DenseExpr p)) = denseMkByteCheck spec ckBus o1
        rw [hm', hpay]; rfl
      have ho1mem : o1 ∈ R.payload := by
        have := List.getElem?_eq_some_iff.mp hget
        obtain ⟨hlt, hgetE⟩ := this
        exact hgetE ▸ List.getElem_mem hlt
      refine ⟨hstateless, ?_, ?_, ?_⟩
      ·
        intro denv hRok
        cases hb : facts.slotBound busId (-shape.setNewMult) (R.payload.map DenseExpr.constValue?) slot
        with
        | none => rw [hb] at hbnd; simp at hbnd
        | some b =>
          rw [hb] at hbnd
          dsimp only at hbnd
          have hgetEv : (denseBIEval R denv).payload[slot]? = some (o1.eval denv) := by
            show (R.payload.map (fun e => e.eval denv))[slot]? = some (o1.eval denv)
            rw [List.getElem?_map, hget]; rfl
          have hfact : facts.slotBound (denseBIEval R denv).busId (denseBIEval R denv).multiplicity
              (R.payload.map DenseExpr.constValue?) slot = some b := by
            rw [hRmEv denv, show (denseBIEval R denv).busId = busId from hRbus]
            exact hb
          have hbyteE : (o1.eval denv).val < 256 :=
            lt_of_lt_of_le
              (facts.slotBound_sound (denseBIEval R denv) (R.payload.map DenseExpr.constValue?)
                slot b (o1.eval denv) hfact (denseMatches_evalPattern R.payload denv) hRok hgetEv)
              (of_decide_eq_true hbnd)
          rw [hckeq, denseMkByteCheck_accepted bs facts spec ck.busId hspec o1 denv, hbound]
          exact hbyteE
      ·
        intro denv
        rw [hckeq]; exact denseMkByteCheck_breaks bs facts spec ck.busId hspec o1 denv
      ·
        intro v hv
        rw [hckeq] at hv
        unfold denseBIVars at hv
        rw [List.mem_append] at hv
        have hvE : v ∈ o1.vars := by
          rcases hv with hm | hm
          · simp only [denseMkByteCheck, DenseExpr.vars, List.not_mem_nil] at hm
          · obtain ⟨pe, hpe, hve⟩ := List.mem_flatMap.1 hm
            exact denseMkByteCheck_payload_vars spec ck.busId o1 pe hpe hve
        unfold denseBIVars
        rw [List.mem_append]
        exact Or.inr (List.mem_flatMap.2 ⟨o1, ho1mem, hvE⟩)
    · exact absurd hrest (by simp)

/-- A passing `denseCheckCancel` — with the split equation, the witness/index membership facts,
    registry coverage, and a `Sound` fact for the threaded equality map — yields `DensePassCorrect`
    via `denseDropPair_correct`. -/
theorem denseCheckCancel_sound (isInput : VarId → Bool)
    (d : DenseConstraintSystem p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (hp1 : (1 : ZMod p) ≠ 0) (deep : Bool) (hdeep : deep = true → p.Prime)
    (ops : DenseZModOps p)
    (busId : Nat) (shape : MemoryBusShape) (hshape : facts.memShape busId = some shape)
    (slots : List Nat) (bound : Nat)
    (M : Thunk (DenseEqConstraintMap p)) (hM : M.get.Sound d.algebraicConstraints)
    (domIdx : Std.HashMap VarId (List (DenseExpr p))) (candsOf : VarId → List (DenseExpr p))
    (wits : VarId → List (BusInteraction (DenseExpr p)))
    (fbasis : VarId → List (DenseLinExpr p × Nat))
    (A : List (BusInteraction (DenseExpr p))) (S : BusInteraction (DenseExpr p))
    (B : List (BusInteraction (DenseExpr p))) (R : BusInteraction (DenseExpr p))
    (C : List (BusInteraction (DenseExpr p)))
    (hslots : facts.recvByteSlots busId (R.payload.map DenseExpr.constValue?) = some (slots, bound))
    (checks : List (BusInteraction (DenseExpr p)))
    (hsplit : d.busInteractions = A ++ S :: B ++ R :: C)
    (hdomIdx : ∀ v, ∀ c ∈ denseVarBucketLookup domIdx v, c ∈ d.algebraicConstraints)
    (hcands : ∀ x, ∀ c ∈ candsOf x, c ∈ d.algebraicConstraints)
    (hwits : ∀ v, ∀ bi ∈ wits v, bi ∈ A ++ B ++ C ++ checks)
    (hfb : ∀ (denv : VarId → ZMod p), (∀ bi ∈ A ++ B ++ C ++ checks,
        (denseBIEval bi denv).multiplicity ≠ 0 → bs.accepts (denseBIEval bi denv)) →
      ∀ v, ∀ LB ∈ fbasis v, (LB.1.eval denv).val < LB.2)
    (h : denseCheckCancel ops deep bs facts M domIdx candsOf wits fbasis busId shape slots bound S R checks
      = true) :
    DensePassCorrect isInput d { d with busInteractions := A ++ B ++ C ++ checks } [] bs := by
  unfold denseCheckCancel at h
  rw [denseSetNewMult_eq ops shape, denseGetPreviousMult_eq ops shape] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hSb, hRb⟩, hSm⟩, hRm⟩, hpay⟩, hemit⟩, hjust⟩ := h
  have hRmEv : ∀ denv, (denseBIEval R denv).multiplicity = -shape.setNewMult :=
    fun denv => R.multiplicity.constValue?_sound (-shape.setNewMult) (of_decide_eq_true hRm) denv
  refine denseDropPair_correct isInput d bs facts hp1 A B C S R busId shape hshape
    (R.payload.map DenseExpr.constValue?) slots bound hslots
    (fun denv => denseMatches_evalPattern R.payload denv) checks
    (fun ck hck => denseEmitOk_sound ops bs facts busId shape slots R ck
      (List.all_eq_true.mp hemit ck hck) (of_decide_eq_true hRb) hRmEv)
    (fun denv hall hbus => denseRecvSlotsJustified_sound bound deep d.algebraicConstraints domIdx
      candsOf bs facts (A ++ B ++ C ++ checks) wits fbasis slots R hdeep hdomIdx hcands hwits
      hjust denv (hfb denv hbus) hall hbus)
    hsplit
    (of_decide_eq_true hSb) (of_decide_eq_true hRb)
    (of_decide_eq_true hSm) (of_decide_eq_true hRm)
    (fun denv hcon => densePayloadEntailedEq_sound M hM S.payload R.payload hpay denv hcon)

end ApcOptimizer.Dense
