import ApcOptimizer.Implementation.OptimizerPasses.BusSweep
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.BusUnify

set_option autoImplicit false

/-! # Soundness for the dense `busSweep` pass

`DensePassCorrect` for `denseBusSweepF` (`BusSweep.lean`), lifted through `DenseVerifiedPassW.of`.
The pass only adds constraints, so soundness is a constraint superset
(`DensePassCorrect.denseAddConstraints`); the substance is real-trace completeness.

The justification is order-free, in two stages. `denseBSOrder?_admissibleMemoryBus` turns the
canonical-order certificate into the *positional* discipline for the bus's evaluated interaction
list, via `admissibleMemoryBus_of_pairUp` (`Implementation/MemoryBusOrdered.lean`) — the fibers come
from the chunking, the per-access `recv ts < send ts` from the solved gadget plus TS_BOUND, and the
global send order from the shared linear base with stepping constants. On that discipline the
consecutive-match sweep's verifier (`denseBSCheckPair_sound`) reads exactly as it did when the
positional discipline was assumed outright. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## `pairUp` plumbing -/

theorem pairUp_map {α β : Type*} (f : α → β) :
    ∀ {l : List α} {ps : List (α × α)}, pairUp l = some ps →
      pairUp (l.map f) = some (ps.map (fun q => (f q.1, f q.2)))
  | [], _, h => by simp only [pairUp, Option.some.injEq] at h; subst h; rfl
  | [_], _, h => by simp [pairUp] at h
  | a :: b :: rest, ps, h => by
      cases hrec : pairUp rest with
      | none => rw [pairUp, hrec] at h; simp at h
      | some ps' =>
          rw [pairUp, hrec] at h
          simp only [Option.map_some, Option.some.injEq] at h
          subst h
          simp [pairUp, pairUp_map f hrec]

/-! ## The send timestamps increase along the list -/

/-- `denseBUSendTsOk` plus TS_BOUND on the sends: one shared linear base with constants stepping by
    `[1, B)` makes the evaluated ts-slot *values* strictly increase along the list
    (`val_lt_of_step`, chained by `strictMono_of_lt_succ_fin`). Base-position independent — the
    surviving base is whichever instruction's clock substitution kept, so the offsets are signed. -/
theorem denseBSSendTs_mono (hp30 : 2 ^ 30 < p) (tsField B : Nat) (hB29 : B ≤ 2 ^ 29)
    (sends : List (BusInteraction (DenseExpr p)))
    (htsok : denseBUSendTsOk tsField B sends = true) (denv : VarId → ZMod p)
    (hbnd : ∀ S ∈ sends, tsSlotVal tsField (denseBIEval S denv) < B) :
    ∀ (i j : Nat) (hi : i < sends.length) (hj : j < sends.length), i < j →
      tsSlotVal tsField (denseBIEval (sends[i]'hi) denv)
        < tsSlotVal tsField (denseBIEval (sends[j]'hj) denv) := by
  haveI : NeZero p := ⟨by omega⟩
  cases hS0 : sends.head? with
  | none => simp [denseBUSendTsOk, hS0] at htsok
  | some S0 =>
  cases hL0 : denseBUTsLin tsField S0 with
  | none => simp [denseBUSendTsOk, hS0, hL0] at htsok
  | some L0 =>
  cases hoffs : denseBUOffs tsField (denseTermKey L0) sends with
  | none => simp [denseBUSendTsOk, hS0, hL0, hoffs] at htsok
  | some offs =>
  simp only [denseBUSendTsOk, hS0, hL0, hoffs] at htsok
  have hstepspec := denseBUStepsOk_spec htsok
  have hofflen : offs.length = sends.length := denseBUOffs_length hoffs
  set k := sends.length with hk
  have hoffb : ∀ i : Fin k, i.val < offs.length :=
    fun i => Nat.lt_of_lt_of_eq i.isLt hofflen.symm
  set send : Fin k → BusInteraction (ZMod p) :=
    fun i => denseBIEval (sends[i.val]'i.isLt) denv with hsendf
  set off : Fin k → ZMod p := fun i => offs[i.val]'(hoffb i) with hofff
  set b : ZMod p := L0.eval denv - L0.const with hb
  have hoffspec := denseBUOffs_spec hoffs
  have hts : ∀ i : Fin k, (send i).payload[tsField]? = some (b + off i) := by
    intro i
    obtain ⟨e, L, hpay, hlin, hkey, ho⟩ := hoffspec i.val (sends[i.val]'i.isLt)
      (offs[i.val]'(hoffb i))
      (List.getElem?_eq_some_iff.mpr ⟨i.isLt, rfl⟩)
      (List.getElem?_eq_some_iff.mpr ⟨hoffb i, rfl⟩)
    have hslot : (send i).payload[tsField]? = some (e.eval denv) := by
      show ((sends[i.val]'i.isLt).payload.map (fun e => e.eval denv))[tsField]? = _
      rw [List.getElem?_map, hpay]
      rfl
    rw [hslot]
    congr 1
    rw [denseLinearize_eval e L hlin denv]
    have hbase : L.eval denv - L.const = b := by
      rw [hb]; exact denseKey_eval_base_eq L L0 hkey denv
    have hcast : off i = L.const := by simp only [hofff, ho]
    rw [hcast]
    linear_combination hbase
  have hsv : ∀ i : Fin k, tsSlotVal tsField (send i) = (b + off i).val := by
    intro i
    unfold tsSlotVal
    rw [hts i]
    rfl
  have hbs : ∀ i : Fin k, tsSlotVal tsField (send i) < B :=
    fun i => hbnd (sends[i.val]'i.isLt) (List.getElem_mem _)
  have hmono : StrictMono (fun i : Fin k => tsSlotVal tsField (send i)) := by
    refine strictMono_of_lt_succ_fin ?_
    intro i hi
    obtain ⟨hd1, hdB⟩ := hstepspec i (by omega)
    have hsplit : (b + off ⟨i, Nat.lt_of_succ_lt hi⟩)
          + (off ⟨i + 1, hi⟩ - off ⟨i, Nat.lt_of_succ_lt hi⟩) = b + off ⟨i + 1, hi⟩ := by
      rw [add_assoc, add_sub_cancel]
    simp only [hsv ⟨i, Nat.lt_of_succ_lt hi⟩, hsv ⟨i + 1, hi⟩, ← hsplit]
    exact val_lt_of_step hp30 _ _ B hB29 ((hsv ⟨i, Nat.lt_of_succ_lt hi⟩) ▸ hbs _) hd1 hdB
  intro i j hi hj hij
  exact hmono (show (⟨i, hi⟩ : Fin k) < ⟨j, hj⟩ from hij)

/-! ## The proposed pairing is a permutation of the bus -/

/-- Flattening the pairs back and chunking is the identity. -/
theorem pairUp_flatMap {α : Type*} :
    ∀ l : List (α × α), pairUp (l.flatMap (fun q => [q.1, q.2])) = some l
  | [] => rfl
  | q :: rest => by
      show pairUp (q.1 :: q.2 :: (rest.flatMap (fun q => [q.1, q.2]))) = _
      rw [pairUp, pairUp_flatMap rest]
      rfl

theorem denseBSAccessesOf_flatMap (dflt : BusInteraction (DenseExpr p) × DenseBUPre p)
    (arr : Array (BusInteraction (DenseExpr p) × DenseBUPre p)) (ps : List (Nat × Nat)) :
    (denseBSAccessesOf dflt arr ps).flatMap (fun q => [q.1, q.2])
      = (ps.flatMap (fun ij => [ij.1, ij.2])).map (fun i => (arr[i]?).getD dflt) := by
  induction ps with
  | nil => rfl
  | cons ij rest ih =>
      simp only [denseBSAccessesOf, List.map_cons, List.flatMap_cons] at ih ⊢
      simp [ih]

theorem denseBS_range_map {α : Type} (arr : Array α) (dflt : α) :
    (List.range arr.size).map (fun i => (arr[i]?).getD dflt) = arr.toList := by
  refine List.ext_getElem (by simp) ?_
  intro n h1 h2
  have hn : n < arr.size := by simpa using h2
  simp [Array.getElem?_eq_getElem hn]

/-- The permutation certificate: the flattened pairing is a rearrangement of the bus's own list. -/
theorem denseBSCheckPerm_perm (dflt : BusInteraction (DenseExpr p) × DenseBUPre p)
    (zipped : List (BusInteraction (DenseExpr p) × DenseBUPre p)) (ps : List (Nat × Nat))
    (h : denseBSCheckPerm zipped.length ps = true) :
    ((denseBSAccessesOf dflt zipped.toArray ps).flatMap (fun q => [q.1, q.2])).Perm zipped := by
  set idxs := ps.flatMap (fun ij => [ij.1, ij.2]) with hidxs
  have hsort : idxs.mergeSort (· ≤ ·) = List.range zipped.length := of_decide_eq_true h
  have hperm : idxs.Perm (List.range zipped.length) := by
    rw [← hsort]; exact (List.mergeSort_perm idxs _).symm
  rw [denseBSAccessesOf_flatMap]
  refine (hperm.map (fun i => (zipped.toArray[i]?).getD dflt)).trans ?_
  have hsz : zipped.toArray.size = zipped.length := by simp
  rw [← hsz, denseBS_range_map]

/-! ## The canonical-order certificate entails the positional discipline -/

/-- Inversion of the certificate: the proposal, the permutation, the field gate, and the checks. -/
theorem denseBSOrder?_inv {bs : BusSemantics p} {facts : BusFacts p bs} {shape : MemoryBusShape}
    {T : DenseTwoRootMap p} {setMult prevMult : ZMod p} {tsField B : Nat}
    {allBis : List (BusInteraction (DenseExpr p))} {idx : DenseBUIdx}
    {zipped : List (BusInteraction (DenseExpr p) × DenseBUPre p)} {ps : List (Nat × Nat)}
    (h : denseBSOrder? bs facts shape T setMult prevMult tsField B allBis idx zipped = some ps) :
    denseBSCheckPerm zipped.length ps = true ∧ 2 ^ 30 < p ∧ B ≤ 2 ^ 29 ∧
      denseBSPairsOk setMult prevMult
        (denseBSAccessesOf (denseBSDefault shape T) zipped.toArray ps) = true ∧
      denseBSGadgetsOk bs facts allBis idx tsField B
        (denseBSAccessesOf (denseBSDefault shape T) zipped.toArray ps) = true ∧
      denseBUSendTsOk tsField B
        ((denseBSAccessesOf (denseBSDefault shape T) zipped.toArray ps).map
          (fun q => q.2.1)) = true := by
  unfold denseBSOrder? at h
  simp only at h
  by_cases hc : denseBSChecksOk bs facts shape T setMult prevMult tsField B allBis idx zipped
      (denseBSPropose setMult prevMult tsField zipped) = true
  · rw [if_pos hc] at h
    obtain rfl : denseBSPropose setMult prevMult tsField zipped = ps := by simpa using h
    unfold denseBSChecksOk at hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    exact ⟨hc.1.1.1.1.1, hc.1.1.1.1.2, hc.1.1.1.2, hc.1.1.2, hc.1.2, hc.2⟩
  · rw [if_neg hc] at h; simp at h

/-- The certificate's consequence: the *paired* list — the bus's interactions rearranged into
    canonical access order — is `admissibleMemoryBus`. Every hypothesis of
    `admissibleMemoryBus_of_pairUp` comes from a syntactic check: the chunking is by construction,
    the fibers and addresses from `denseBSPairsOk`, the per-access LessThan from `denseBSGadgetsOk`,
    the global send order from `denseBUSendTsOk` under TS_BOUND, and the identification of the
    rearranged multiset with the bus's own from the permutation certificate. -/
theorem denseBSOrder?_admissibleMemoryBus (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (busId : Nat) (shape : MemoryBusShape)
    (hshape : facts.memShape busId = some shape)
    (tsField B : Nat) (htsf : facts.memTsField busId = some (tsField, B))
    (T : DenseTwoRootMap p) (ps : List (Nat × Nat)) (idx : DenseBUIdx)
    (hord : denseBSOrder? bs facts shape T (denseSetNewMult denseZModOps shape)
        (denseGetPreviousMult denseZModOps shape) tsField B d.busInteractions idx
        ((d.busInteractions.filter (fun bi => bi.busId = busId)).map
          (fun bi => (bi, denseBUPrep shape T bi))) = some ps)
    (denv : VarId → ZMod p) (hadm : d.admissible bs denv) (hsat : d.satisfies bs denv) :
    admissibleMemoryBus shape
      ((denseBSCanon shape T (d.busInteractions.filter (fun bi => bi.busId = busId)) ps).map
        (fun bi => denseBIEval bi denv)) := by
  set bisL := d.busInteractions.filter (fun bi => bi.busId = busId) with hbisL
  set zipped := bisL.map (fun bi => (bi, denseBUPrep shape T bi)) with hzip
  set qs := denseBSAccessesOf (denseBSDefault shape T) zipped.toArray ps with hqs
  have hcanon : denseBSCanon shape T bisL ps = qs.flatMap (fun q => [q.1.1, q.2.1]) := by
    show ((qs.flatMap (fun q => [q.1, q.2])).map (fun z => z.1)) = _
    simp [List.map_flatMap]
  rw [hcanon]
  obtain ⟨hperm, hp30, hB29, hpairs, hgads, htsok⟩ := denseBSOrder?_inv hord
  rw [denseSetNewMult_eq, denseGetPreviousMult_eq] at hpairs
  haveI : NeZero p := ⟨by omega⟩
  have hp1 : (1 : ZMod p) ≠ 0 := denseBU_one_ne_zero hp30
  have hmne : -shape.setNewMult ≠ (shape.setNewMult : ZMod p) := denseBU_negSet_ne hp30 shape
  -- the pairing is a rearrangement of the bus's own interactions
  have hpermZ : (qs.flatMap (fun q => [q.1, q.2])).Perm zipped :=
    denseBSCheckPerm_perm _ zipped ps hperm
  have hpermB : (qs.flatMap (fun q => [q.1.1, q.2.1])).Perm bisL := by
    have := hpermZ.map (fun z : BusInteraction (DenseExpr p) × DenseBUPre p => z.1)
    rw [hzip, List.map_map] at this
    simpa [List.map_flatMap, Function.comp_def, List.map_id'] using this
  -- every prepared record of the pairing really is the prepared record of its interaction
  have hshapeQ : ∀ q ∈ qs, q.1.2 = denseBUPrep shape T q.1.1 ∧
      q.2.2 = denseBUPrep shape T q.2.1 := by
    intro q hq
    obtain ⟨ij, -, rfl⟩ := List.mem_map.mp hq
    have hz : ∀ (i : Nat), ((zipped.toArray[i]?).getD (denseBSDefault shape T)).2
        = denseBUPrep shape T ((zipped.toArray[i]?).getD (denseBSDefault shape T)).1 := by
      intro i
      cases hget : zipped.toArray[i]? with
      | none => rfl
      | some z =>
        have hmem : z ∈ zipped := by simpa using Array.mem_of_getElem? hget
        obtain ⟨bi, -, rfl⟩ := List.mem_map.mp hmem
        rfl
    exact ⟨hz ij.1, hz ij.2⟩
  -- the per-pair certificates
  have hpq : ∀ q ∈ qs, q.1.1.multiplicity.constValue? = some (-shape.setNewMult) ∧
      q.2.1.multiplicity.constValue? = some shape.setNewMult ∧
      denseAddrConstsEq shape q.1.1 q.2.1 = true := by
    intro q hq
    have h := List.all_eq_true.mp hpairs q hq
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    obtain ⟨hq1p, hq2p⟩ := hshapeQ q hq
    rw [hq1p, denseBUPrep_mult] at h1
    rw [hq2p, denseBUPrep_mult] at h2
    rw [hq1p, hq2p, denseBUConstsEq_eq] at h3
    exact ⟨h1, h2, h3⟩
  -- the whole bus list is active, so the rely's active filter is the identity
  have hactive : ∀ x ∈ bisL, (denseBIEval x denv).multiplicity ≠ 0 := by
    intro x hx
    have hxmem : x ∈ qs.flatMap (fun q => [q.1.1, q.2.1]) := hpermB.mem_iff.mpr hx
    rw [List.mem_flatMap] at hxmem
    obtain ⟨q, hq, hxq⟩ := hxmem
    obtain ⟨h1, h2, -⟩ := hpq q hq
    show x.multiplicity.eval denv ≠ 0
    rcases List.mem_cons.mp hxq with rfl | hx2
    · rw [denseConstValueEval _ _ h1 denv]
      exact neg_ne_zero.mpr (shape.setNewMult_ne_zero hp1)
    · rcases List.mem_cons.mp hx2 with rfl | hx3
      · rw [denseConstValueEval _ _ h2 denv]
        exact shape.setNewMult_ne_zero hp1
      · simp at hx3
  -- the order-free rely on this bus, transported to the rearranged list
  have hadm' : bs.admissible ((d.busInteractions.map (fun bi => denseBIEval bi denv)).filter
      (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId)) := hadm
  have hM := facts.admissible_sound (d.busInteractions.map (fun bi => denseBIEval bi denv))
    hadm' busId shape hshape
  rw [dense_map_eval_filter_busId, ← hbisL] at hM
  have hfilter : (bisL.map (fun bi => denseBIEval bi denv)).filter
      (fun m => decide (m.multiplicity ≠ 0)) = bisL.map (fun bi => denseBIEval bi denv) := by
    refine List.filter_eq_self.mpr ?_
    intro m hm
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hm
    simpa using hactive x hx
  rw [hfilter] at hM
  have hMc : admissibleMemoryBusM shape
      (↑((qs.flatMap (fun q => [q.1.1, q.2.1])).map (fun bi => denseBIEval bi denv)) :
        Multiset (BusInteraction (ZMod p))) :=
    (admissibleMemoryBusM_perm shape (hpermB.map (fun bi => denseBIEval bi denv))).mpr hM
  -- the TS_BOUND rely on this bus
  have hbnds := facts.memTsField_sound (d.busInteractions.map (fun bi => denseBIEval bi denv))
    hadm' busId tsField B htsf
  rw [dense_map_eval_filter_busId, ← hbisL] at hbnds
  have hbnd : ∀ x ∈ qs.flatMap (fun q => [q.1.1, q.2.1]),
      tsSlotVal tsField (denseBIEval x denv) < B := by
    intro x hx
    have hx' : x ∈ bisL := hpermB.mem_iff.mp hx
    exact hbnds (denseBIEval x denv) (List.mem_map_of_mem hx') (hactive x hx')
  -- the evaluated chunking
  refine admissibleMemoryBus_of_pairUp shape
    (ps := (qs.map (fun q => (q.1.1, q.2.1))).map
      (fun q => (denseBIEval q.1 denv, denseBIEval q.2 denv))) ?_ hMc hmne ?_ ?_
    (tsSlotVal tsField) (fun m m' h => by unfold tsSlotVal; rw [h]) ?_ ?_
  · have hQS : qs.flatMap (fun q => [q.1.1, q.2.1])
        = (qs.map (fun q => (q.1.1, q.2.1))).flatMap (fun q => [q.1, q.2]) := by
      simp [List.flatMap_map]
    rw [hQS]
    exact pairUp_map _ (pairUp_flatMap _)
  · intro q hq
    simp only [List.map_map, List.mem_map] at hq
    obtain ⟨q0, hq0, rfl⟩ := hq
    obtain ⟨h1, h2, -⟩ := hpq q0 hq0
    exact ⟨denseConstValueEval _ _ h1 denv, denseConstValueEval _ _ h2 denv⟩
  · intro q hq
    simp only [List.map_map, List.mem_map] at hq
    obtain ⟨q0, hq0, rfl⟩ := hq
    obtain ⟨-, -, h3⟩ := hpq q0 hq0
    exact denseAddrConstsEq_sound shape _ _ h3 denv
  · intro q hq
    simp only [List.map_map, List.mem_map] at hq
    obtain ⟨q0, hq0, rfl⟩ := hq
    have hok := List.all_eq_true.mp hgads q0 hq0
    refine denseBUGadgetOk_sound bs facts d idx tsField B _ _ hok denv hsat (hbnd _ ?_)
    exact List.mem_flatMap.mpr ⟨q0, hq0, by simp⟩
  · intro i j hi hj hij
    simp only [List.length_map] at hi hj
    have hsends : ∀ (t : Nat) (ht : t < qs.length),
        (((qs.map (fun q => (q.1.1, q.2.1))).map
          (fun q => (denseBIEval q.1 denv, denseBIEval q.2 denv)))[t]'(by simpa using ht)).2
          = denseBIEval ((qs.map (fun q => q.2.1))[t]'(by simpa using ht)) denv := by
      intro t ht
      simp
    rw [hsends i hi, hsends j hj]
    refine denseBSSendTs_mono hp30 tsField B hB29 (qs.map (fun q => q.2.1)) htsok denv ?_
      i j (by simpa using hi) (by simpa using hj) hij
    intro S hS
    obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hS
    exact hbnd _ (List.mem_flatMap.mpr ⟨q0, hq0, by simp⟩)

/-- The rearranged list is a rearrangement of the bus's own interactions. -/
theorem denseBSCanon_perm (shape : MemoryBusShape) (T : DenseTwoRootMap p)
    (bisL : List (BusInteraction (DenseExpr p))) (ps : List (Nat × Nat))
    (hperm : denseBSCheckPerm (bisL.map (fun bi => (bi, denseBUPrep shape T bi))).length ps
      = true) :
    (denseBSCanon shape T bisL ps).Perm bisL := by
  have h := denseBSCheckPerm_perm (denseBSDefault shape T)
    (bisL.map (fun bi => (bi, denseBUPrep shape T bi))) ps hperm
  have h2 := h.map (fun z : BusInteraction (DenseExpr p) × DenseBUPre p => z.1)
  rw [List.map_map] at h2
  simpa [denseBSCanon, Function.comp_def, List.map_id'] using h2

/-- Hence its entries are interactions of `d`. -/
theorem denseBSCanon_mem (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (busId : Nat) (shape : MemoryBusShape) (T : DenseTwoRootMap p)
    (ps : List (Nat × Nat)) {tsField B : Nat} {allBis : List (BusInteraction (DenseExpr p))}
    {idx : DenseBUIdx}
    (hord : denseBSOrder? bs facts shape T (denseSetNewMult denseZModOps shape)
        (denseGetPreviousMult denseZModOps shape) tsField B allBis idx
        ((d.busInteractions.filter (fun bi => bi.busId = busId)).map
          (fun bi => (bi, denseBUPrep shape T bi))) = some ps) :
    ∀ x ∈ denseBSCanon shape T (d.busInteractions.filter (fun bi => bi.busId = busId)) ps,
      x ∈ d.busInteractions := by
  obtain ⟨hperm, -, -, -, -, -⟩ := denseBSOrder?_inv hord
  intro x hx
  exact List.mem_of_mem_filter ((denseBSCanon_perm shape T _ ps hperm).mem_iff.mp hx)

/-! ## The verifier -/

/-- One verified `mid` position: the message is inactive or provably at a different address. -/
theorem denseBSMidOk_sound (d : DenseConstraintSystem p) (reg : VarRegistry)
    (hcov : d.CoveredBy reg) (shape : MemoryBusShape) (T : DenseTwoRootMap p)
    (hT : T.Sound d.algebraicConstraints) (S m : BusInteraction (DenseExpr p))
    (hScov : denseBICovered reg S) (hmcov : denseBICovered reg m)
    (h : denseBSMidOk denseZModOps (denseBUWits d) (denseBUPrep shape T S)
      (denseBUPrep shape T m) = true)
    (denv : VarId → ZMod p) (hcon : ∀ c ∈ d.algebraicConstraints, c.eval denv = 0) :
    (denseBIEval m denv).multiplicity ≠ 0 →
      shape.address (denseBIEval m denv) = shape.address (denseBIEval S denv) → False := by
  intro hmne hmaddr
  unfold denseBSMidOk at h
  rcases (Bool.or_eq_true _ _).mp h with hcond | hz
  · rcases (Bool.or_eq_true _ _).mp hcond with hcond_a | hnz
    · rcases (Bool.or_eq_true _ _).mp hcond_a with hcond2 | h2r
      · rcases (Bool.or_eq_true _ _).mp hcond2 with hneq | haff
        · exact denseAddrConstsNeq_sound shape S m
            (by rw [← denseBUConstsNeq_eq shape T S m]; exact hneq) denv hmaddr.symm
        · exact denseBUAffineNeq_sound shape T S m haff denv hmaddr.symm
      · exact denseBUTwoRootNeq_sound shape T hT S m h2r denv hcon hmaddr.symm
    · refine denseAddrNonzeroNeq_sound reg shape d.algebraicConstraints hcov.1 S m hScov hmcov
        ?_ denv hcon hmaddr.symm
      rw [← denseBUNonzeroNeq_eq shape T (DenseNonzeroWits.build d.algebraicConstraints) S m,
        ← denseBUWits_eq d]
      exact hnz
  · refine hmne (denseConstValueEval m.multiplicity 0 ?_ denv)
    have := of_decide_eq_true hz
    simpa [denseBUPrep, denseBUOfSlots, denseMultConst, denseZModOps, zmodZeroP_eq] using this

/-- Every position strictly between the candidate's endpoints passes `denseBSMidOk`. -/
theorem denseBSMidScan_sound (ops : DenseZModOps p) (nw : DenseNonzeroWits p)
    (arr : Array (DenseBUPre p)) (a : DenseBUPre p) (j : Nat) :
    ∀ (fuel q : Nat), denseBSMidScan ops nw arr a j fuel q = true →
      ∀ (r : Nat) (b : DenseBUPre p), q ≤ r → r < j → r < q + fuel → arr[r]? = some b →
        denseBSMidOk ops nw a b = true := by
  intro fuel
  induction fuel with
  | zero => intro q _ r _ _ _ hlt _; omega
  | succ fuel ih =>
    intro q h r b hqr hrj hrf hb
    rw [denseBSMidScan] at h
    split at h
    · omega
    · rename_i hqj
      split at h
      · rename_i hq
        rcases Nat.eq_or_lt_of_le hqr with rfl | hlt
        · rw [hb] at hq; exact absurd hq (by simp)
        · exact absurd hq (by
            intro hq0
            have : q < arr.size := by
              by_contra hc
              have : arr[r]? = none := by
                simp only [Array.getElem?_eq_none_iff]; omega
              rw [hb] at this; exact absurd this (by simp)
            simp [Array.getElem?_eq_getElem this] at hq0)
      · rename_i bq hq
        split at h
        · rename_i hok
          rcases Nat.eq_or_lt_of_le hqr with rfl | hlt
          · rw [hb] at hq; injection hq with hq; subst hq; exact hok
          · exact ih (q + 1) h r b (by omega) hrj (by omega) hb
        · exact absurd h (by simp)

/-! ## Positions back to a list split -/

private theorem dense_list_at {α : Type} {l : List α} {i : Nat} {x : α} (h : l[i]? = some x) :
    l = l.take i ++ x :: l.drop (i + 1) ∧ (l.take i).length = i := by
  obtain ⟨hi, hx⟩ := List.getElem?_eq_some_iff.1 h
  refine ⟨?_, by simp [Nat.min_eq_left hi.le]⟩
  conv_lhs => rw [← List.take_append_drop i l]
  rw [List.drop_eq_getElem_cons hi, hx]

private theorem dense_mem_mid {α : Type} {l : List α} {i j : Nat} {x : α}
    (h : x ∈ (l.drop (i + 1)).take (j - i - 1)) : ∃ q, i < q ∧ q < j ∧ l[q]? = some x := by
  obtain ⟨t, ht⟩ := List.getElem?_of_mem h
  rw [List.getElem?_take] at ht
  split at ht
  · rename_i htlt
    rw [List.getElem?_drop] at ht
    exact ⟨i + 1 + t, by omega, by omega, ht⟩
  · exact absurd ht (by simp)

private theorem dense_split_of_positions
    {L pre restAfter seen post : List (BusInteraction (DenseExpr p))}
    {S R : BusInteraction (DenseExpr p)} {i j : Nat}
    (hi : pre.length = i) (hsplit : L = pre ++ S :: restAfter)
    (hj : seen.length = j) (hnow : L = seen ++ R :: post) (hlt : i < j) :
    L = pre ++ S :: restAfter.take (j - i - 1) ++ R :: post := by
  have hRA : restAfter = L.drop (i + 1) := by
    have h1 : L = (pre ++ [S]) ++ restAfter := by rw [hsplit]; simp
    rw [h1, List.drop_left' (by simp [hi])]
  have hRp : R :: post = L.drop j := by rw [hnow, List.drop_left' (by simp [hj])]
  have hdrop : restAfter.drop (j - i - 1) = R :: post := by
    rw [hRA, List.drop_drop, hRp]; congr 1; omega
  have hn : L = pre ++ S :: (restAfter.take (j - i - 1) ++ R :: post) := by
    rw [← hdrop, List.take_append_drop]; exact hsplit
  simpa [List.append_assoc] using hn

/-! ## The verified pair -/

private theorem dense_arr_get {α β : Type} (l : List α) (f : α → β) {k : Nat} {x : α}
    (h : l[k]? = some x) : ((l.map f).toArray)[k]? = some (f x) := by
  simp [h]

/-- The verifier entails the pair's payload equality, so every slot equality it emits vanishes.
    The positional discipline is supplied by the caller (`denseBSOrder?_admissibleMemoryBus`);
    everything else is the sweep's own certificates. -/
theorem denseBSCheckPair_sound (d : DenseConstraintSystem p) (bs : BusSemantics p)
    (reg : VarRegistry) (hcov : d.CoveredBy reg)
    (T : DenseTwoRootMap p) (hT : T.Sound d.algebraicConstraints)
    (shape : MemoryBusShape)
    (bisL : List (BusInteraction (DenseExpr p)))
    (hbis : ∀ x ∈ bisL, x ∈ d.busInteractions)
    (i j : Nat) (S R : BusInteraction (DenseExpr p))
    (hS : bisL[i]? = some S) (hR : bisL[j]? = some R)
    (hchk : denseBSCheckPair denseZModOps (denseBUWits d) (denseSetNewMult denseZModOps shape)
        (denseGetPreviousMult denseZModOps shape) ((bisL.map (denseBUPrep shape T)).toArray) i j
      = true)
    (denv : VarId → ZMod p) (hsat : d.satisfies bs denv)
    (hAdm : admissibleMemoryBus shape (bisL.map (fun bi => denseBIEval bi denv))) :
    ∀ c ∈ denseMemEqConstraints shape S R, c.eval denv = 0 := by
  have hai := dense_arr_get bisL (denseBUPrep shape T) hS
  have haj := dense_arr_get bisL (denseBUPrep shape T) hR
  unfold denseBSCheckPair at hchk
  rw [hai, haj] at hchk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨⟨⟨⟨hij, hSm⟩, hRm⟩, haddrEq⟩, hscan⟩ := hchk
  rw [denseBUPrep_mult, denseSetNewMult_eq] at hSm
  rw [denseBUPrep_mult, denseGetPreviousMult_eq] at hRm
  -- the split the discipline needs
  obtain ⟨hsplitS, hlenS⟩ := dense_list_at hS
  obtain ⟨hsplitR, hlenR⟩ := dense_list_at hR
  have hsplit : bisL = bisL.take i ++ S :: (bisL.drop (i + 1)).take (j - i - 1)
      ++ R :: bisL.drop (j + 1) :=
    dense_split_of_positions hlenS hsplitS hlenR hsplitR hij
  set mid := (bisL.drop (i + 1)).take (j - i - 1) with hmid
  have hmemfilter : ∀ x ∈ bisL.take i ++ S :: mid ++ R :: bisL.drop (j + 1),
      x ∈ d.busInteractions := by
    intro x hx
    rw [← hsplit] at hx
    exact hbis x hx
  have hScov : denseBICovered reg S := hcov.2 S (hmemfilter S (by simp))
  have hRcov : denseBICovered reg R := hcov.2 R (hmemfilter R (by simp))
  have hSev : (denseBIEval S denv).multiplicity = shape.setNewMult :=
    denseConstValueEval S.multiplicity shape.setNewMult hSm denv
  have hRev : (denseBIEval R denv).multiplicity = -shape.setNewMult :=
    denseConstValueEval R.multiplicity (-shape.setNewMult) hRm denv
  have haddr : shape.address (denseBIEval S denv) = shape.address (denseBIEval R denv) :=
    denseAddrConstsEq_sound shape S R (by
      rw [← denseBUConstsEq_eq shape T S R]; exact haddrEq) denv
  have hcon : ∀ c ∈ d.algebraicConstraints, c.eval denv = 0 := hsat.1
  have hmidall : ∀ m ∈ mid, (denseBIEval m denv).multiplicity ≠ 0 →
      shape.address (denseBIEval m denv) = shape.address (denseBIEval S denv) → False := by
    intro m hm
    obtain ⟨q, hiq, hqj, hq⟩ := dense_mem_mid hm
    have hmcov : denseBICovered reg m := hcov.2 m (hmemfilter m (by simp [hm]))
    refine denseBSMidOk_sound d reg hcov shape T hT S m hScov hmcov ?_ denv hcon
    exact denseBSMidScan_sound _ _ _ _ _ (j - i) (i + 1) hscan q _ (by omega) hqj (by omega)
      (dense_arr_get bisL (denseBUPrep shape T) hq)
  -- the positional discipline, on the mapped split
  have hpay : (denseBIEval S denv).payload = (denseBIEval R denv).payload := by
    refine hAdm ((bisL.take i).map (fun bi => denseBIEval bi denv))
      (mid.map (fun bi => denseBIEval bi denv))
      ((bisL.drop (j + 1)).map (fun bi => denseBIEval bi denv))
      (denseBIEval S denv) (denseBIEval R denv) ?_ hSev hRev haddr ?_
    · conv_lhs => rw [hsplit]
      simp
    · intro m hm hmne hmaddr
      obtain ⟨m0, hm0, rfl⟩ := List.mem_map.1 hm
      exact hmidall m0 hm0 hmne hmaddr
  intro c hc
  unfold denseMemEqConstraints at hc
  obtain ⟨t, _, rfl⟩ := List.mem_map.1 hc
  rw [denseEqExpr_eval]
  have hPQ : R.payload.map (fun e => e.eval denv) = S.payload.map (fun e => e.eval denv) :=
    hpay.symm
  rw [densePayloadSlot_eval_eq R.payload S.payload denv hPQ t, sub_self]

/-! ## From the emitted equalities back to a verified pair

The sweep, the scatter and the candidate order carry no obligation: `denseBSCheckPair` re-derives
`i < j` and both endpoints from the array itself, so all the collector has to expose is *which*
pair produced an equality. -/

theorem denseBSCollect_mem (ops : DenseZModOps p) (nw : DenseNonzeroWits p)
    (setMult prevMult : ZMod p) (shape : MemoryBusShape)
    (bis : Array (BusInteraction (DenseExpr p))) (arr : Array (DenseBUPre p)) :
    ∀ (cands : List (Nat × Nat)) (c : DenseExpr p),
      c ∈ denseBSCollect ops nw setMult prevMult shape bis arr cands →
      ∃ i j S R, denseBSCheckPair ops nw setMult prevMult arr i j = true ∧
        bis[i]? = some S ∧ bis[j]? = some R ∧ c ∈ denseMemEqConstraints shape S R
  | [], c, hc => by simp [denseBSCollect] at hc
  | (i, j) :: rest, c, hc => by
      rw [denseBSCollect] at hc
      split at hc
      · rename_i hchk
        split at hc
        · rename_i S R hSi hRj
          rcases List.mem_append.1 hc with h | h
          · exact ⟨i, j, S, R, hchk, hSi, hRj, h⟩
          · exact denseBSCollect_mem ops nw setMult prevMult shape bis arr rest c h
        · exact denseBSCollect_mem ops nw setMult prevMult shape bis arr rest c hc
      · exact denseBSCollect_mem ops nw setMult prevMult shape bis arr rest c hc

theorem denseBSForBus_mem (bs : BusSemantics p) (facts : BusFacts p bs) (T : DenseTwoRootMap p)
    (nw : DenseNonzeroWits p) (shape : MemoryBusShape) (tsField B : Nat)
    (allBis : List (BusInteraction (DenseExpr p))) (idx : DenseBUIdx)
    (bisL : List (BusInteraction (DenseExpr p))) (c : DenseExpr p)
    (hc : c ∈ denseBSForBus bs facts denseZModOps T nw shape tsField B allBis idx bisL) :
    ∃ ps i j S R,
      denseBSOrder? bs facts shape T (denseSetNewMult denseZModOps shape)
        (denseGetPreviousMult denseZModOps shape) tsField B allBis idx
        (bisL.map (fun bi => (bi, denseBUPrep shape T bi))) = some ps ∧
      denseBSCheckPair denseZModOps nw (denseSetNewMult denseZModOps shape)
        (denseGetPreviousMult denseZModOps shape)
        (((denseBSCanon shape T bisL ps).map (denseBUPrep shape T)).toArray) i j = true ∧
      (denseBSCanon shape T bisL ps)[i]? = some S ∧
      (denseBSCanon shape T bisL ps)[j]? = some R ∧
      c ∈ denseMemEqConstraints shape S R := by
  unfold denseBSForBus at hc
  simp only at hc
  split at hc
  · simp at hc
  · rename_i ps hord
    obtain ⟨i, j, S, R, hchk, hSi, hRj, hmem⟩ :=
      denseBSCollect_mem _ nw _ _ shape (denseBSCanon shape T bisL ps).toArray _ _ c hc
    exact ⟨ps, i, j, S, R, hord, hchk, by simpa using hSi, by simpa using hRj, hmem⟩

/-- The structure of an emitted equality: a declared bus with a declared ts slot, the
    canonical-order certificate for a pairing of its interactions, and the verifier's verdict on the
    pair — both endpoints read off the *rearranged* list the sweep ran on. -/
theorem denseBSEqs_mem (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p)
    {c : DenseExpr p} (hc : c ∈ denseBSEqs bs facts d) :
    ∃ busId shape tsField B ps i j S R,
      facts.memShape busId = some shape ∧
      facts.memTsField busId = some (tsField, B) ∧
      denseBSOrder? bs facts shape
        (denseBUTable (denseBUBusLists facts.memShape d.busInteractions) d)
        (denseSetNewMult denseZModOps shape)
        (denseGetPreviousMult denseZModOps shape) tsField B d.busInteractions
        (denseBUBuildIdx bs facts d.busInteractions)
        ((d.busInteractions.filter (fun bi => bi.busId = busId)).map
          (fun bi => (bi, denseBUPrep shape
            (denseBUTable (denseBUBusLists facts.memShape d.busInteractions) d) bi))) = some ps ∧
      denseBSCheckPair denseZModOps (denseBUWits d) (denseSetNewMult denseZModOps shape)
        (denseGetPreviousMult denseZModOps shape)
        (((denseBSCanon shape (denseBUTable (denseBUBusLists facts.memShape d.busInteractions) d)
            (d.busInteractions.filter (fun bi => bi.busId = busId)) ps).map
          (denseBUPrep shape
            (denseBUTable (denseBUBusLists facts.memShape d.busInteractions) d))).toArray)
        i j = true ∧
      (denseBSCanon shape (denseBUTable (denseBUBusLists facts.memShape d.busInteractions) d)
        (d.busInteractions.filter (fun bi => bi.busId = busId)) ps)[i]? = some S ∧
      (denseBSCanon shape (denseBUTable (denseBUBusLists facts.memShape d.busInteractions) d)
        (d.busInteractions.filter (fun bi => bi.busId = busId)) ps)[j]? = some R ∧
      c ∈ denseMemEqConstraints shape S R := by
  rw [show denseBSEqs bs facts d
      = (if (denseBUBusLists facts.memShape d.busInteractions).isEmpty then []
         else denseBSEqsOf bs facts (denseBUBusLists facts.memShape d.busInteractions) d)
      from rfl] at hc
  split at hc
  · simp at hc
  · rw [show denseBSEqsOf bs facts (denseBUBusLists facts.memShape d.busInteractions) d
        = ((denseBUBusLists facts.memShape d.busInteractions).map (fun sl =>
            match facts.memTsField sl.1 with
            | some (tsField, B) =>
              denseBSForBus bs facts denseZModOps
                (denseBUTable (denseBUBusLists facts.memShape d.busInteractions) d)
                (denseBUWits d) sl.2.1 tsField B d.busInteractions
                (denseBUBuildIdx bs facts d.busInteractions) sl.2.2
            | none => [])).flatten from rfl,
      List.mem_flatten] at hc
    obtain ⟨l, hl, hcl⟩ := hc
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hl
    obtain ⟨hms, hfilter⟩ := denseBUBusLists_mem he
    cases htsf : facts.memTsField e.1 with
    | none => rw [htsf] at hcl; simp at hcl
    | some tb =>
      obtain ⟨tsField, B⟩ := tb
      rw [htsf] at hcl
      obtain ⟨ps, i, j, S, R, hord, hchk, hSi, hRj, hmem⟩ :=
        denseBSForBus_mem bs facts _ _ _ _ _ _ _ _ c hcl
      rw [hfilter] at hord hchk hSi hRj
      exact ⟨e.1, e.2.1, tsField, B, ps, i, j, S, R, hms, htsf, hord, hchk, hSi, hRj, hmem⟩

/-! ## The appended constraints -/

theorem denseBusSweepNewCs_subset (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) {c : DenseExpr p} (h : c ∈ denseBusSweepNewCs bs facts d) :
    c ∈ denseBSEqs bs facts d := by
  rw [show denseBusSweepNewCs bs facts d
      = (if (denseBSEqs bs facts d).isEmpty then []
         else denseBUFilterNew d (denseBSEqs bs facts d)) from rfl] at h
  split at h
  · simp at h
  · exact denseBUFilterNew_subset d _ h

/-! ## The pass transform: correctness and coverage -/

theorem denseBusSweepNewCs_vars (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) :
    ∀ c ∈ denseBusSweepNewCs bs facts d, ∀ z ∈ c.vars, z ∈ d.occ := by
  intro c hc z hz
  obtain ⟨busId, shape, tsField, B, ps, i, j, S, R, -, -, hord, -, hSi, hRj, hmem⟩ :=
    denseBSEqs_mem bs facts d (denseBusSweepNewCs_subset bs facts d hc)
  have hcm := denseBSCanon_mem bs facts d busId shape _ ps hord
  rcases denseMemEqConstraints_vars shape S R hmem hz with ⟨e, he, hze⟩ | ⟨e, he, hze⟩
  · exact DenseConstraintSystem.mem_occ_of_payload (hcm R (List.mem_of_getElem? hRj)) he hze
  · exact DenseConstraintSystem.mem_occ_of_payload (hcm S (List.mem_of_getElem? hSi)) he hze

theorem denseBusSweepNewCs_sound (bs : BusSemantics p) (facts : BusFacts p bs) (reg : VarRegistry)
    (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg)
    (denv : VarId → ZMod p) (hadm : d.admissible bs denv) (hsat : d.satisfies bs denv) :
    ∀ c ∈ denseBusSweepNewCs bs facts d, c.eval denv = 0 := by
  intro c hc
  obtain ⟨busId, shape, tsField, B, ps, i, j, S, R, hms, htsf, hord, hchk, hSi, hRj, hmem⟩ :=
    denseBSEqs_mem bs facts d (denseBusSweepNewCs_subset bs facts d hc)
  exact denseBSCheckPair_sound d bs reg hcov _
    (denseBUTable_sound (denseBUBusLists facts.memShape d.busInteractions) d) shape
    _ (denseBSCanon_mem bs facts d busId shape _ ps hord) i j S R hSi hRj hchk denv hsat
    (denseBSOrder?_admissibleMemoryBus bs facts d busId shape hms tsField B htsf _ ps
      (denseBUBuildIdx bs facts d.busInteractions) hord denv hadm hsat) c hmem

/-- The `let`-bound body, unfolded (definitionally). -/
theorem denseBusSweepF_eq (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) :
    denseBusSweepF bs facts d =
      (if (1 : ZMod p) ≠ 0 then
        (if (denseBusSweepNewCs bs facts d).isEmpty then d
         else { d with algebraicConstraints :=
                  d.algebraicConstraints ++ denseBusSweepNewCs bs facts d })
       else d) := rfl

theorem denseBusSweepF_covered (reg : VarRegistry) (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg) :
    (denseBusSweepF bs facts d).CoveredBy reg := by
  rw [denseBusSweepF_eq]
  split_ifs with hp1 _hempty
  · exact hcov
  · refine ⟨fun e he => ?_, hcov.2⟩
    rcases List.mem_append.1 he with h | h
    · exact hcov.1 e h
    · intro i hi
      exact DenseConstraintSystem.occ_valid hcov i (denseBusSweepNewCs_vars bs facts d e h i hi)
  · exact hcov

theorem denseBusSweepF_correct (reg : VarRegistry) (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg) :
    DensePassCorrect reg.isInput d (denseBusSweepF bs facts d) [] bs := by
  rw [denseBusSweepF_eq]
  split_ifs with hp1 _hempty
  · exact DensePassCorrect.refl reg.isInput d bs
  · exact DensePassCorrect.denseAddConstraints d bs (denseBusSweepNewCs bs facts d)
      (denseBusSweepNewCs_vars bs facts d)
      (fun denv hadm hsat => denseBusSweepNewCs_sound bs facts reg d hcov denv hadm hsat)
  · exact DensePassCorrect.refl reg.isInput d bs

/-! ## The dense `busSweep` pass -/

/-- The dense `busSweep` pass (see `denseBusSweepF`). -/
def denseBusSweepPass : DenseVerifiedPassW p :=
  DenseVerifiedPassW.of denseBusSweepF (fun _ _ _ => [])
    (fun reg bs facts d hcov => denseBusSweepF_covered reg bs facts d hcov)
    (fun _ _ _ _ _ => by intro x hx; simp at hx)
    (fun reg bs facts d hcov => denseBusSweepF_correct reg bs facts d hcov)

end ApcOptimizer.Dense
