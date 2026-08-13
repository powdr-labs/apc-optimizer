import ApcOptimizer.Implementation.OptimizerPasses.ExecChain
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.BusUnify
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.DomainTable
import ApcOptimizer.Implementation.MemoryBusChain

set_option autoImplicit false

/-! # Soundness for the dense `execChain` pass

The certificate of `ExecChain.lean` read semantically: the key-slot constants pin the chain, each
access steps its own timestamp, and `entryKeyed_chain_copies`
(`Implementation/MemoryBusChain.lean`) then forces every non-entry receive to copy the previous
send's payload. The fiber presentations and the classification verdicts are the `busUnify` ones
(`Proofs/BusUnify.lean`); only the certificate and its consumption are new. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## The key slot -/

/-- A constant key slot evaluates to its constant. -/
theorem denseECKey_eval {slot : Nat} {bi : BusInteraction (DenseExpr p)} {c : ZMod p}
    (h : denseECKey slot bi = some c) (denv : VarId → ZMod p) :
    (denseBIEval bi denv).payload[slot]? = some c := by
  unfold denseECKey at h
  cases hp : bi.payload[slot]? with
  | none => rw [hp] at h; simp at h
  | some e =>
      rw [hp] at h
      simp only [Option.bind_some] at h
      show (bi.payload.map (fun e => e.eval denv))[slot]? = some c
      rw [List.getElem?_map, hp]
      exact congrArg some (DenseExpr.constValue?_sound e c h denv)

theorem denseECKeys_length {slot : Nat} :
    ∀ {recvs : List (BusInteraction (DenseExpr p))} {ks : List (ZMod p)},
      denseECKeys slot recvs = some ks → ks.length = recvs.length
  | [], ks, h => by
      simp only [denseECKeys, Option.some.injEq] at h
      rw [← h]; rfl
  | R :: rest, ks, h => by
      cases hk : denseECKey slot R with
      | none => simp [denseECKeys, hk] at h
      | some k =>
          cases hrec : denseECKeys slot rest with
          | none => simp [denseECKeys, hk, hrec] at h
          | some ks' =>
              simp only [denseECKeys, hk, hrec, Option.some.injEq] at h
              rw [← h]
              simp [denseECKeys_length hrec]

theorem denseECKeys_spec {slot : Nat} :
    ∀ {recvs : List (BusInteraction (DenseExpr p))} {ks : List (ZMod p)},
      denseECKeys slot recvs = some ks →
      ∀ (i : Nat) (R : BusInteraction (DenseExpr p)) (k : ZMod p),
        recvs[i]? = some R → ks[i]? = some k → denseECKey slot R = some k
  | [], ks, _, i, R, k, hR, _ => by simp at hR
  | R0 :: rest, ks, h, i, R, k, hR, hk => by
      cases hk0 : denseECKey slot R0 with
      | none => simp [denseECKeys, hk0] at h
      | some k0 =>
          cases hrec : denseECKeys slot rest with
          | none => simp [denseECKeys, hk0, hrec] at h
          | some ks' =>
              simp only [denseECKeys, hk0, hrec, Option.some.injEq] at h
              rw [← h] at hk
              cases i with
              | zero =>
                  simp only [List.getElem?_cons_zero, Option.some.injEq] at hR hk
                  rw [← hR, ← hk]
                  exact hk0
              | succ j =>
                  simp only [List.getElem?_cons_succ] at hR hk
                  exact denseECKeys_spec hrec j R k hR hk

/-! ## The per-access timestamp step -/

/-- The ts-slot value of an interaction whose ts slot linearizes. -/
private theorem denseECTs_eval {tsField : Nat} {bi : BusInteraction (DenseExpr p)}
    {L : DenseLinExpr p} (h : denseBUTsLin tsField bi = some L) (denv : VarId → ZMod p) :
    (denseBIEval bi denv).payload[tsField]? = some (L.eval denv) := by
  unfold denseBUTsLin at h
  cases hp : bi.payload[tsField]? with
  | none => rw [hp] at h; simp at h
  | some e =>
      rw [hp] at h
      show (bi.payload.map (fun e => e.eval denv))[tsField]? = _
      rw [List.getElem?_map, hp]
      exact congrArg some (denseLinearize_eval e L h denv)

/-- A verified access step: under TS_BOUND on the receive, its ts-slot value is below its own
    send's. The difference is a constant `δ` with `1 ≤ δ.val < B ≤ 2^29` and `2^30 < p`, so the
    field cannot wrap between the two (`val_lt_of_offset_lt`). -/
theorem denseECStepOk_sound {tsField B : Nat} {S R : BusInteraction (DenseExpr p)}
    (hp : 2 ^ 30 < p) (hB : B ≤ 2 ^ 29) (h : denseECStepOk tsField B S R = true)
    (denv : VarId → ZMod p) (hbnd : tsSlotVal tsField (denseBIEval R denv) < B) :
    tsSlotVal tsField (denseBIEval R denv) < tsSlotVal tsField (denseBIEval S denv) := by
  haveI : NeZero p := ⟨by omega⟩
  unfold denseECStepOk at h
  cases hLS : denseBUTsLin tsField S with
  | none => rw [hLS] at h; simp at h
  | some LS =>
  cases hLR : denseBUTsLin tsField R with
  | none => rw [hLS, hLR] at h; simp at h
  | some LR =>
  rw [hLS, hLR] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff] at h
  obtain ⟨⟨hterms, hone⟩, hlt⟩ := h
  set N := (LS.add (LR.scale (-1))).norm with hN
  -- the difference of the two ts slots is the constant `N.const`
  have hdiff : LS.eval denv = LR.eval denv + N.const := by
    have h1 : N.eval denv = (LS.add (LR.scale (-1))).eval denv := DenseLinExpr.norm_eval _ denv
    rw [DenseLinExpr.add_eval, DenseLinExpr.scale_eval] at h1
    have h2 : N.eval denv = N.const := by
      unfold DenseLinExpr.eval
      rw [hterms]
      simp
    rw [h2] at h1
    rw [h1]
    ring
  -- both slot values, in terms of the linear forms
  have hRv : tsSlotVal tsField (denseBIEval R denv) = (LR.eval denv).val := by
    unfold tsSlotVal
    rw [denseECTs_eval hLR denv]
    rfl
  have hSv : tsSlotVal tsField (denseBIEval S denv) = (LS.eval denv).val := by
    unfold tsSlotVal
    rw [denseECTs_eval hLS denv]
    rfl
  rw [hRv, hSv]
  rw [hdiff]
  exact val_lt_of_step hp (LR.eval denv) N.const B hB (hRv ▸ hbnd) (by omega) (by omega)

/-! ## The chain certificate, read semantically -/

/-- The pairwise strict order the `IsChain` check gives on the receives' keys. -/
private theorem denseEC_keys_lt {ks : List (ZMod p)}
    (hchain : List.IsChain (· < ·) (ks.map (fun k => k.val)))
    (i j : Nat) (hi : i < ks.length) (hj : j < ks.length) (hij : i < j) :
    (ks[i]'hi).val < (ks[j]'hj).val := by
  have hpw := hchain.pairwise
  rw [List.pairwise_iff_getElem] at hpw
  have hi' : i < (ks.map (fun k => k.val)).length := by simpa using hi
  have hj' : j < (ks.map (fun k => k.val)).length := by simpa using hj
  have := hpw i j hi' hj' hij
  simpa using this

/-! ## Assembling the group -/

/-- The verified chain forces every non-entry receive to copy the previous send's payload, so every
    emitted equality vanishes. -/
theorem denseECGroup?_sound (bs : BusSemantics p) (facts : BusFacts p bs)
    (reg : VarRegistry) (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg)
    (busId : Nat) (shape : MemoryBusShape) (hshape : facts.memShape busId = some shape)
    (tsField B : Nat) (htsf : facts.memTsField busId = some (tsField, B))
    (slot : Nat) (key : ZMod p) (hkeyf : facts.memEntryKey busId = some (slot, key))
    (T : DenseTwoRootMap p) (hT : T.Sound d.algebraicConstraints)
    (sends recvs : List (BusInteraction (DenseExpr p)))
    (hgrp : denseECGroup? (denseBUWits d) (denseSetNewMult denseZModOps shape)
        (denseGetPreviousMult denseZModOps shape) tsField B slot key
        ((d.busInteractions.filter (fun bi => bi.busId = busId)).map
          (fun bi => (bi, denseBUPrep shape T bi))) = some (sends, recvs))
    (denv : VarId → ZMod p) (hadm : d.admissible bs denv) (hsat : d.satisfies bs denv) :
    ∀ c ∈ denseBUGroupEqs shape sends recvs, c.eval denv = 0 := by
  set bisL := d.busInteractions.filter (fun bi => bi.busId = busId) with hbisL
  have hbmem : ∀ bi ∈ bisL, bi ∈ d.busInteractions := fun bi hb => List.mem_of_mem_filter hb
  rw [denseSetNewMult_eq, denseGetPreviousMult_eq] at hgrp
  -- invert the verifier
  cases hlp : (bisL.map (fun bi => (bi, denseBUPrep shape T bi)))[0]? with
  | none => simp [denseECGroup?, hlp] at hgrp
  | some lp =>
  cases hsplit : denseBUSplit (denseBUWits d) shape.setNewMult (-shape.setNewMult) lp.2
      (bisL.map (fun bi => (bi, denseBUPrep shape T bi))) with
  | none => simp [denseECGroup?, hlp, hsplit] at hgrp
  | some sr =>
  obtain ⟨sends', recvs'⟩ := sr
  simp only [denseECGroup?, hlp, hsplit] at hgrp
  split at hgrp
  case isFalse => simp at hgrp
  rename_i hgate
  split at hgrp
  case isFalse => simp at hgrp
  rename_i hchk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hgate
  obtain ⟨hp30, hB29⟩ := hgate
  simp only [Option.some.injEq, Prod.mk.injEq] at hgrp
  obtain ⟨rfl, rfl⟩ : sends = sends' ∧ recvs = recvs' := ⟨hgrp.1.symm, hgrp.2.symm⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨⟨⟨hk2, hklen⟩, hkeysok⟩, hsteps⟩ := hchk
  -- the leader
  obtain ⟨lbi, hlbi_get, hlp_eq⟩ : ∃ lbi, bisL[0]? = some lbi ∧
      lp = (lbi, denseBUPrep shape T lbi) := by
    rw [List.getElem?_map] at hlp
    cases hb : bisL[0]? with
    | none => rw [hb] at hlp; simp at hlp
    | some b =>
        rw [hb] at hlp
        simp only [Option.map_some, Option.some.injEq] at hlp
        exact ⟨b, rfl, hlp.symm⟩
  have hlbi_mem : lbi ∈ bisL := List.mem_of_getElem? hlbi_get
  have hlbi : lbi ∈ d.busInteractions := hbmem lbi hlbi_mem
  rw [hlp_eq] at hsplit
  -- the field facts
  haveI : NeZero p := ⟨by omega⟩
  have hp1 : (1 : ZMod p) ≠ 0 := denseBU_one_ne_zero hp30
  have hpm : -shape.setNewMult ≠ (shape.setNewMult : ZMod p) := denseBU_negSet_ne hp30 shape
  have hcon : ∀ c ∈ d.algebraicConstraints, c.eval denv = 0 := hsat.1
  -- the fibers
  obtain ⟨hsends, hrecvs⟩ := denseBUSplit_fibers reg d hcov shape T hT lbi hlbi denv hcon hp1
    hpm bisL hbmem sends recvs hsplit
  -- the relies on this bus
  have hadm' : bs.admissible ((d.busInteractions.map (fun bi => denseBIEval bi denv)).filter
      (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId)) := hadm
  have hkeyM := facts.memEntryKey_sound (d.busInteractions.map (fun bi => denseBIEval bi denv))
    hadm' busId slot key shape hshape hkeyf
  rw [dense_map_eval_filter_busId, ← hbisL] at hkeyM
  have hbnds := facts.memTsField_sound (d.busInteractions.map (fun bi => denseBIEval bi denv))
    hadm' busId tsField B htsf
  rw [dense_map_eval_filter_busId, ← hbisL] at hbnds
  -- member facts
  have hrecv_mult : ∀ R ∈ recvs, (denseBIEval R denv).multiplicity = -shape.setNewMult := by
    intro R hR
    obtain ⟨pre, hmem, hcl⟩ := denseBUSplit_recvs hsplit R hR
    obtain ⟨R', hR', heq⟩ := List.mem_map.mp hmem
    cases heq
    exact (denseBUVerdict_recv_sound shape T lbi R hcl denv).1
  have hrecv_bisL : ∀ R ∈ recvs, R ∈ bisL := by
    intro R hR
    obtain ⟨pre, hmem, -⟩ := denseBUSplit_recvs hsplit R hR
    obtain ⟨R', hR', heq⟩ := List.mem_map.mp hmem
    rw [show R' = R from congrArg Prod.fst heq] at hR'
    exact hR'
  have hrecv_ts : ∀ R ∈ recvs, tsSlotVal tsField (denseBIEval R denv) < B := by
    intro R hR
    refine hbnds (denseBIEval R denv)
      (List.mem_map.mpr ⟨R, hrecv_bisL R hR, rfl⟩) ?_
    rw [hrecv_mult R hR]
    exact neg_ne_zero.mpr (shape.setNewMult_ne_zero hp1)
  -- the key certificate
  cases hks : denseECKeys slot recvs with
  | none => simp [denseECKeysOk, hks] at hkeysok
  | some ks =>
  cases hk0 : ks.head? with
  | none => simp [denseECKeysOk, hks, hk0] at hkeysok
  | some k0 =>
  simp only [denseECKeysOk, hks, hk0, Bool.and_eq_true, decide_eq_true_eq] at hkeysok
  obtain ⟨⟨hkey0, hchain⟩, hsendkeys⟩ := hkeysok
  have hkslen : ks.length = recvs.length := denseECKeys_length hks
  -- indexing
  set k := sends.length with hk
  have hklen' : recvs.length = k := hklen.symm
  have hrecb : ∀ i : Fin k, i.val < recvs.length :=
    fun i => Nat.lt_of_lt_of_eq i.isLt hklen'.symm
  have hksb : ∀ i : Fin k, i.val < ks.length :=
    fun i => Nat.lt_of_lt_of_eq (hrecb i) hkslen.symm
  set A := shape.address (denseBIEval lbi denv) with hA
  set M : Multiset (BusInteraction (ZMod p)) :=
    ↑((bisL.map (fun bi => denseBIEval bi denv)).filter
      (fun m => decide (m.multiplicity ≠ 0))) with hMdef
  set send : Fin k → BusInteraction (ZMod p) :=
    fun i => denseBIEval (sends[i.val]'i.isLt) denv with hsendf
  set recv : Fin k → BusInteraction (ZMod p) :=
    fun i => denseBIEval (recvs[i.val]'(hrecb i)) denv with hrecvf
  have hsendP : sendsAt shape A M = Multiset.map send ↑(List.finRange k) := by
    rw [hsends, denseBU_coe_map_fin sends rfl (fun bi => denseBIEval bi denv)]
  have hrecvP : recvsAt shape A M = Multiset.map recv ↑(List.finRange k) := by
    rw [hrecvs, denseBU_coe_map_fin recvs hklen' (fun bi => denseBIEval bi denv)]
  -- each receive's key slot is its own constant
  have hrecv_key : ∀ i : Fin k, (recv i).payload[slot]? = some (ks[i.val]'(hksb i)) := by
    intro i
    refine denseECKey_eval (denseECKeys_spec hks i.val _ _ ?_ ?_) denv
    · exact List.getElem?_eq_some_iff.mpr ⟨hrecb i, rfl⟩
    · exact List.getElem?_eq_some_iff.mpr ⟨hksb i, rfl⟩
  -- distinct receive keys
  have hdistinct : ∀ i j : Fin k, (recv i).payload[slot]? = (recv j).payload[slot]? → i = j := by
    intro i j hij
    rw [hrecv_key i, hrecv_key j, Option.some.injEq] at hij
    by_contra hne
    have hvne : i.val ≠ j.val := fun h => hne (Fin.ext h)
    rcases Nat.lt_or_ge i.val j.val with hlt | hge
    · have := denseEC_keys_lt hchain i.val j.val (hksb i) (hksb j) hlt
      rw [hij] at this
      omega
    · have := denseEC_keys_lt hchain j.val i.val (hksb j) (hksb i) (by omega)
      rw [hij] at this
      omega
  -- the chain: send `i` carries receive `i + 1`'s key
  have hchainP : ∀ (i : Fin k) (h : i.val + 1 < k),
      (send i).payload[slot]? = (recv ⟨i.val + 1, h⟩).payload[slot]? := by
    intro i h
    have hlent : ks.tail.length = k - 1 := by
      rw [List.length_tail, hkslen, hklen']
    have hidx : (sends.zip ks.tail)[i.val]? = some (sends[i.val]'i.isLt,
        ks.tail[i.val]'(by omega)) := by
      rw [List.getElem?_zip_eq_some]
      exact ⟨List.getElem?_eq_some_iff.mpr ⟨i.isLt, rfl⟩,
        List.getElem?_eq_some_iff.mpr ⟨by omega, rfl⟩⟩
    have hok := List.all_eq_true.mp hsendkeys _ (List.mem_of_getElem? hidx)
    simp only [decide_eq_true_eq] at hok
    have htail : ks.tail[i.val]'(by omega) = ks[i.val + 1]'(by omega) := by
      rw [List.getElem_tail]
    rw [htail] at hok
    rw [denseECKey_eval hok denv, hrecv_key ⟨i.val + 1, h⟩]
  -- the entry designation: only the first receive carries the entry key
  have hentry : ∀ j : Fin k, 0 < j.val → (recv j).payload[slot]? ≠ some key := by
    intro j hj
    rw [hrecv_key j]
    have hk0' : ks[0]? = some k0 := by rw [← List.head?_eq_getElem?]; exact hk0
    have h0 : ks[0]'(by omega) = k0 := by
      have hgs := List.getElem?_eq_some_iff.mp hk0'
      exact hgs.choose_spec
    have hlt := denseEC_keys_lt hchain 0 j.val (by omega) (hksb j) hj
    rw [h0, hkey0] at hlt
    intro hcontra
    rw [Option.some.injEq] at hcontra
    rw [hcontra] at hlt
    omega
  -- each access steps its timestamp
  have hlt : ∀ i : Fin k, tsSlotVal tsField (recv i) < tsSlotVal tsField (send i) := by
    intro i
    have hzip : (sends.zip recvs)[i.val]? = some (sends[i.val]'i.isLt,
        recvs[i.val]'(hrecb i)) := by
      rw [List.getElem?_zip_eq_some]
      exact ⟨List.getElem?_eq_some_iff.mpr ⟨i.isLt, rfl⟩,
        List.getElem?_eq_some_iff.mpr ⟨hrecb i, rfl⟩⟩
    have hok := List.all_eq_true.mp hsteps _ (List.mem_of_getElem? hzip)
    exact denseECStepOk_sound hp30 hB29 hok denv
      (hrecv_ts (recvs[i.val]'(hrecb i)) (List.getElem_mem _))
  -- the copies
  have hcopies := entryKeyed_chain_copies shape M A slot key hkeyM send recv hsendP hrecvP
    (tsSlotVal tsField) (fun m m' h => by unfold tsSlotVal; rw [h]) hlt hdistinct hchainP hentry
  -- read off the emitted equalities
  intro c hc
  unfold denseBUGroupEqs at hc
  rw [List.mem_flatMap] at hc
  obtain ⟨sr, hsr, hcm⟩ := hc
  obtain ⟨i, hilt, hget⟩ := List.mem_iff_getElem.mp hsr
  have hizip : i < sends.length ∧ i < recvs.tail.length := by
    rw [List.length_zip] at hilt
    omega
  have hgetS : (sends.zip recvs.tail)[i] = (sends[i]'hizip.1, recvs.tail[i]'hizip.2) :=
    List.getElem_zip ..
  have htail : recvs.tail[i]'hizip.2 = recvs[i + 1]'(by
      have := hizip.2
      rw [List.length_tail] at this
      omega) := by
    rw [List.getElem_tail]
  have hi1k : i + 1 < k := by
    have := hizip.2
    rw [List.length_tail] at this
    omega
  have hpay : (recv ⟨i + 1, hi1k⟩).payload
      = (send ⟨(i + 1) - 1, Nat.lt_of_le_of_lt (Nat.sub_le (i + 1) 1) hi1k⟩).payload :=
    hcopies ⟨i + 1, hi1k⟩ (by simp)
  have hidx : ((⟨(i + 1) - 1, Nat.lt_of_le_of_lt (Nat.sub_le (i + 1) 1) hi1k⟩ : Fin k))
      = (⟨i, by omega⟩ : Fin k) := by
    ext
    simp
  rw [hidx] at hpay
  rw [← hget, hgetS] at hcm
  simp only at hcm
  rw [htail] at hcm
  unfold denseMemEqConstraints at hcm
  obtain ⟨t, -, rfl⟩ := List.mem_map.mp hcm
  rw [denseEqExpr_eval]
  have hPQ : (recvs[i + 1]'(by omega)).payload.map (fun e => e.eval denv)
      = (sends[i]'hizip.1).payload.map (fun e => e.eval denv) := hpay
  rw [densePayloadSlot_eval_eq _ _ denv hPQ t, sub_self]

/-! ## From the emitted equalities back to a verified group -/

/-- The structure of an emitted equality: a declared bus with a declared ts slot and entry key, and
    a verified chain on it containing the equality. -/
theorem denseECEqs_mem (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p)
    {c : DenseExpr p} (hc : c ∈ denseECEqs bs facts d) :
    ∃ busId shape tsField B slot key sends recvs,
      facts.memShape busId = some shape ∧
      facts.memTsField busId = some (tsField, B) ∧
      facts.memEntryKey busId = some (slot, key) ∧
      denseECGroup? (denseBUWits d) (denseSetNewMult denseZModOps shape)
        (denseGetPreviousMult denseZModOps shape) tsField B slot key
        ((d.busInteractions.filter (fun bi => bi.busId = busId)).map
          (fun bi => (bi, denseBUPrep shape
            (denseBUTable (denseBUBusLists facts.memShape d.busInteractions) d) bi)))
        = some (sends, recvs) ∧
      c ∈ denseBUGroupEqs shape sends recvs := by
  rw [show denseECEqs bs facts d
      = (if (denseBUBusLists facts.memShape d.busInteractions).isEmpty then []
         else denseECEqsOf bs facts (denseBUBusLists facts.memShape d.busInteractions) d)
    from rfl] at hc
  split at hc
  · simp at hc
  · rw [show denseECEqsOf bs facts (denseBUBusLists facts.memShape d.busInteractions) d
        = ((denseBUBusLists facts.memShape d.busInteractions).map (fun sl =>
            match facts.memEntryKey sl.1, facts.memTsField sl.1 with
            | some (slot, key), some (tsField, B) =>
              denseECForBus denseZModOps
                (denseBUTable (denseBUBusLists facts.memShape d.busInteractions) d)
                (denseBUWits d) sl.2.1 tsField B slot key sl.2.2
            | _, _ => [])).flatten from rfl,
      List.mem_flatten] at hc
    obtain ⟨l, hl, hcl⟩ := hc
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hl
    obtain ⟨hms, hfilter⟩ := denseBUBusLists_mem he
    cases hek : facts.memEntryKey e.1 with
    | none => simp only [hek] at hcl; simp at hcl
    | some sk =>
    obtain ⟨slot, key⟩ := sk
    cases htf : facts.memTsField e.1 with
    | none => simp only [hek, htf] at hcl; simp at hcl
    | some tB =>
    obtain ⟨tsField, B⟩ := tB
    simp only [hek, htf] at hcl
    unfold denseECForBus at hcl
    cases hgp : denseECGroup? (denseBUWits d) (denseSetNewMult denseZModOps e.2.1)
        (denseGetPreviousMult denseZModOps e.2.1) tsField B slot key
        (e.2.2.map (fun bi => (bi, denseBUPrep e.2.1
          (denseBUTable (denseBUBusLists facts.memShape d.busInteractions) d) bi))) with
    | none => rw [hgp] at hcl; simp at hcl
    | some sr =>
        obtain ⟨sends, recvs⟩ := sr
        rw [hgp] at hcl
        rw [hfilter] at hgp
        exact ⟨e.1, e.2.1, tsField, B, slot, key, sends, recvs, hms, htf, hek, hgp, hcl⟩

theorem denseExecChainNewCs_subset (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) {c : DenseExpr p}
    (h : c ∈ denseExecChainNewCs bs facts d) : c ∈ denseECEqs bs facts d := by
  rw [show denseExecChainNewCs bs facts d
      = (if (denseECEqs bs facts d).isEmpty then []
         else denseBUFilterNew d (denseECEqs bs facts d)) from rfl] at h
  split at h
  · simp at h
  · exact denseBUFilterNew_subset d _ h

/-- The members of a verified chain are interactions of `d`. -/
private theorem denseECGroup?_mem_bis {nw : DenseNonzeroWits p} {sm pm : ZMod p}
    {d : DenseConstraintSystem p} {shape : MemoryBusShape} {T : DenseTwoRootMap p}
    {busId tsField B slot : Nat} {key : ZMod p}
    {sends recvs : List (BusInteraction (DenseExpr p))}
    (hgrp : denseECGroup? nw sm pm tsField B slot key
        ((d.busInteractions.filter (fun bi => bi.busId = busId)).map
          (fun bi => (bi, denseBUPrep shape T bi))) = some (sends, recvs)) :
    (∀ S ∈ sends, S ∈ d.busInteractions) ∧ (∀ R ∈ recvs, R ∈ d.busInteractions) := by
  cases hlp : ((d.busInteractions.filter (fun bi => bi.busId = busId)).map
      (fun bi => (bi, denseBUPrep shape T bi)))[0]? with
  | none => simp [denseECGroup?, hlp] at hgrp
  | some lp =>
  cases hsplit : denseBUSplit nw sm pm lp.2
      ((d.busInteractions.filter (fun bi => bi.busId = busId)).map
        (fun bi => (bi, denseBUPrep shape T bi))) with
  | none => simp [denseECGroup?, hlp, hsplit] at hgrp
  | some sr =>
  obtain ⟨s', r'⟩ := sr
  simp only [denseECGroup?, hlp, hsplit] at hgrp
  split at hgrp
  case isFalse => simp at hgrp
  split at hgrp
  case isFalse => simp at hgrp
  simp only [Option.some.injEq, Prod.mk.injEq] at hgrp
  obtain ⟨rfl, rfl⟩ : sends = s' ∧ recvs = r' := ⟨hgrp.1.symm, hgrp.2.symm⟩
  constructor
  · intro S hS
    obtain ⟨pre, hmem, -⟩ := denseBUSplit_sends hsplit S hS
    obtain ⟨S', hS', heq⟩ := List.mem_map.mp hmem
    rw [show S' = S from congrArg Prod.fst heq] at hS'
    exact List.mem_of_mem_filter hS'
  · intro R hR
    obtain ⟨pre, hmem, -⟩ := denseBUSplit_recvs hsplit R hR
    obtain ⟨R', hR', heq⟩ := List.mem_map.mp hmem
    rw [show R' = R from congrArg Prod.fst heq] at hR'
    exact List.mem_of_mem_filter hR'

/-- The variables of an emitted equality occur in `d`. -/
theorem denseExecChainNewCs_vars (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) :
    ∀ c ∈ denseExecChainNewCs bs facts d, ∀ z ∈ c.vars, z ∈ d.occ := by
  intro c hc z hz
  obtain ⟨busId, shape, tsField, B, slot, key, sends, recvs, -, -, -, hgrp, hmem⟩ :=
    denseECEqs_mem bs facts d (denseExecChainNewCs_subset bs facts d hc)
  obtain ⟨hsend_mem, hrecv_mem⟩ := denseECGroup?_mem_bis hgrp
  unfold denseBUGroupEqs at hmem
  rw [List.mem_flatMap] at hmem
  obtain ⟨sr, hsr, hcm⟩ := hmem
  have hS : sr.1 ∈ sends := (List.of_mem_zip hsr).1
  have hR : sr.2 ∈ recvs.tail := (List.of_mem_zip hsr).2
  rcases denseMemEqConstraints_vars shape sr.1 sr.2 hcm hz with ⟨e, he, hze⟩ | ⟨e, he, hze⟩
  · exact DenseConstraintSystem.mem_occ_of_payload
      (hrecv_mem sr.2 (List.mem_of_mem_tail hR)) he hze
  · exact DenseConstraintSystem.mem_occ_of_payload (hsend_mem sr.1 hS) he hze

theorem denseExecChainNewCs_sound (bs : BusSemantics p) (facts : BusFacts p bs)
    (reg : VarRegistry) (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg)
    (denv : VarId → ZMod p) (hadm : d.admissible bs denv) (hsat : d.satisfies bs denv) :
    ∀ c ∈ denseExecChainNewCs bs facts d, c.eval denv = 0 := by
  intro c hc
  obtain ⟨busId, shape, tsField, B, slot, key, sends, recvs, hms, htf, hek, hgrp, hmem⟩ :=
    denseECEqs_mem bs facts d (denseExecChainNewCs_subset bs facts d hc)
  exact denseECGroup?_sound bs facts reg d hcov busId shape hms tsField B htf slot key hek
    _ (denseBUTable_sound (denseBUBusLists facts.memShape d.busInteractions) d)
    sends recvs hgrp denv hadm hsat c hmem

/-! ## The pass transform: correctness and coverage -/

theorem denseExecChainF_eq (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) :
    denseExecChainF bs facts d =
      (if (1 : ZMod p) ≠ 0 then
        (if (denseExecChainNewCs bs facts d).isEmpty then d
         else { d with algebraicConstraints :=
                  d.algebraicConstraints ++ denseExecChainNewCs bs facts d })
       else d) := rfl

theorem denseExecChainF_covered (reg : VarRegistry) (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg) :
    (denseExecChainF bs facts d).CoveredBy reg := by
  rw [denseExecChainF_eq]
  split_ifs with hp1 _hempty
  · exact hcov
  · refine ⟨fun e he => ?_, hcov.2⟩
    rcases List.mem_append.1 he with h | h
    · exact hcov.1 e h
    · intro i hi
      exact DenseConstraintSystem.occ_valid hcov i
        (denseExecChainNewCs_vars bs facts d e h i hi)
  · exact hcov

theorem denseExecChainF_correct (reg : VarRegistry) (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg) :
    DensePassCorrect reg.isInput d (denseExecChainF bs facts d) [] bs := by
  rw [denseExecChainF_eq]
  split_ifs with hp1 _hempty
  · exact DensePassCorrect.refl reg.isInput d bs
  · exact DensePassCorrect.denseAddConstraints d bs (denseExecChainNewCs bs facts d)
      (denseExecChainNewCs_vars bs facts d)
      (fun denv hadm hsat => denseExecChainNewCs_sound bs facts reg d hcov denv hadm hsat)
  · exact DensePassCorrect.refl reg.isInput d bs

/-! ## The dense `execChain` pass -/

/-- The dense `execChain` pass (see `denseExecChainF`). -/
def denseExecChainPass : DenseVerifiedPassW p :=
  DenseVerifiedPassW.of denseExecChainF (fun _ _ _ => [])
    (fun reg bs facts d hcov => denseExecChainF_covered reg bs facts d hcov)
    (fun _ _ _ _ _ => by intro x hx; simp at hx)
    (fun reg bs facts d hcov => denseExecChainF_correct reg bs facts d hcov)

end ApcOptimizer.Dense
