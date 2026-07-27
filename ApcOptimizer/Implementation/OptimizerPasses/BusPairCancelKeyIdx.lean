import ApcOptimizer.Implementation.OptimizerPasses.BusPairCancelCheck

set_option autoImplicit false

/-! # Constant-address-key position index for `busPairCancel`'s region scans

The mid/shield scans walked every position of their region per candidate pair — with tens of
thousands of accepted drops each re-scanning an `O(prefix)` region, the scan *volume* dominated
the pass. For a candidate whose address slots are all constants, a message can only fail the
region tests if it is on the same bus and either shares the candidate's constant address key or
has a non-constant key: every other position is refuted by the bus-id or constant-disequality arm
and contributes the identity to the scan fold. `DenseKeyIdx` buckets each bus's positions by
constant address key (plus a `sym` list for non-constant keys), so the sparse scans visit only
the same-key and symbolic positions; the `*_eq` lemmas rewrite the sparse results back to the
full-region scans via the skipped positions' refutation certificates. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## The constant address key -/

/-- The all-constant address key of an interaction under a shape (`none` if any address slot is
    missing or non-constant). -/
def denseAddrKeyOf (shape : MemoryBusShape) (bi : BusInteraction (DenseExpr p)) :
    Option (List (ZMod p)) :=
  shape.addressFields.foldr (fun slot acc =>
    match acc, (bi.payload[slot]?).bind DenseExpr.constValue? with
    | some ks, some c => some (c :: ks)
    | _, _ => none) (some [])

/-- Over an arbitrary field list: two constant keys that differ force a slot whose constants
    differ, so the constant-disequality test fires. -/
theorem denseKeyFold_ne_any (S m : BusInteraction (DenseExpr p)) :
    ∀ (fields : List Nat) (kS km : List (ZMod p)),
      fields.foldr (fun slot acc =>
        match acc, (S.payload[slot]?).bind DenseExpr.constValue? with
        | some ks, some c => some (c :: ks)
        | _, _ => none) (some []) = some kS →
      fields.foldr (fun slot acc =>
        match acc, (m.payload[slot]?).bind DenseExpr.constValue? with
        | some ks, some c => some (c :: ks)
        | _, _ => none) (some []) = some km →
      kS ≠ km →
      fields.any (fun slot =>
        match S.payload[slot]?, m.payload[slot]? with
        | some e, some e' =>
          (match e.constValue?, e'.constValue? with
           | some c, some c' => decide (c ≠ c')
           | _, _ => false)
        | _, _ => false) = true := by
  intro fields
  induction fields with
  | nil =>
      intro kS km hS hm hne
      simp only [List.foldr_nil, Option.some.injEq] at hS hm
      exact absurd (hS.symm.trans hm) hne
  | cons slot rest ih =>
      intro kS km hS hm hne
      rw [List.foldr_cons] at hS hm
      cases hSr : (rest.foldr (fun slot acc =>
          match acc, (S.payload[slot]?).bind DenseExpr.constValue? with
          | some ks, some c => some (c :: ks)
          | _, _ => none) (some []) : Option (List (ZMod p))) with
      | none => rw [hSr] at hS; exact absurd hS (by simp)
      | some ksr =>
        cases hSc : (S.payload[slot]?).bind DenseExpr.constValue? with
        | none => rw [hSr, hSc] at hS; exact absurd hS (by simp)
        | some cS =>
          rw [hSr, hSc] at hS
          cases hmr : (rest.foldr (fun slot acc =>
              match acc, (m.payload[slot]?).bind DenseExpr.constValue? with
              | some ks, some c => some (c :: ks)
              | _, _ => none) (some []) : Option (List (ZMod p))) with
          | none => rw [hmr] at hm; exact absurd hm (by simp)
          | some kmr =>
            cases hmc : (m.payload[slot]?).bind DenseExpr.constValue? with
            | none => rw [hmr, hmc] at hm; exact absurd hm (by simp)
            | some cm =>
              rw [hmr, hmc] at hm
              simp only [Option.some.injEq] at hS hm
              rw [List.any_cons]
              by_cases hc : cS = cm
              · -- the head slot agrees, so the tails must differ
                have htne : ksr ≠ kmr := fun h => hne (by rw [← hS, ← hm, hc, h])
                rw [ih ksr kmr hSr hmr htne, Bool.or_true]
              · -- the head slot differs: its constants witness the disequality
                obtain ⟨eS, heS, heSc⟩ := Option.bind_eq_some_iff.mp hSc
                obtain ⟨em, hem, hemc⟩ := Option.bind_eq_some_iff.mp hmc
                have hhead : (match S.payload[slot]?, m.payload[slot]? with
                    | some e, some e' =>
                      (match e.constValue?, e'.constValue? with
                       | some c, some c' => decide (c ≠ c')
                       | _, _ => false)
                    | _, _ => false) = true := by
                  simp only [heS, hem, heSc, hemc]
                  exact decide_eq_true hc
                rw [hhead, Bool.true_or]

/-- Two constant keys that differ force a slot whose constants differ, so the constant
    disequality certificate fires. -/
theorem denseAddrKeyOf_ne_constsNeq (shape : MemoryBusShape)
    (S m : BusInteraction (DenseExpr p)) (kS km : List (ZMod p))
    (hS : denseAddrKeyOf shape S = some kS) (hm : denseAddrKeyOf shape m = some km)
    (hne : kS ≠ km) : denseAddrConstsNeq shape S m = true :=
  denseKeyFold_ne_any S m shape.addressFields kS km hS hm hne

/-- Two constant keys that differ refute the constant address-equality test. -/
theorem denseAddrKeyOf_ne_constsEq (shape : MemoryBusShape)
    (S m : BusInteraction (DenseExpr p)) (kS km : List (ZMod p))
    (hS : denseAddrKeyOf shape S = some kS) (hm : denseAddrKeyOf shape m = some km)
    (hne : kS ≠ km) : denseAddrConstsEq shape S m = false := by
  have hneq := denseAddrKeyOf_ne_constsNeq shape S m kS km hS hm hne
  unfold denseAddrConstsNeq at hneq
  unfold denseAddrConstsEq
  rw [List.any_eq_true] at hneq
  obtain ⟨slot, hslot, hval⟩ := hneq
  rw [List.all_eq_false]
  refine ⟨slot, hslot, ?_⟩
  cases hpS : S.payload[slot]? with
  | none => simp [hpS] at hval
  | some e =>
    cases hpm : m.payload[slot]? with
    | none => simp [hpS, hpm] at hval
    | some e' =>
      simp only [hpS, hpm] at hval
      cases hcS : e.constValue? with
      | none => simp [hcS] at hval
      | some c =>
        cases hcm : e'.constValue? with
        | none => simp [hcS, hcm] at hval
        | some c' =>
          simp only [hcS, hcm, decide_eq_true_eq] at hval
          have hee : e ≠ e' := fun h => hval (by
            rw [h] at hcS
            exact Option.some.inj (hcS.symm.trans hcm))
          intro hcontra
          rw [Bool.or_eq_true] at hcontra
          rcases hcontra with h1 | h2
          · exact hee (of_decide_eq_true h1)
          · simp only [hcS, hcm, decide_eq_true_eq] at h2
            exact hval h2

/-! ## Refutation of skipped positions -/

/-- A cross-bus message is mid-refuted. -/
theorem denseMidRefuted_of_crossBus (ops : DenseZModOps p) (shape : MemoryBusShape)
    (T : Thunk (DenseAddrCerts p)) (busId : Nat) (S m : BusInteraction (DenseExpr p))
    (h : m.busId ≠ busId) : denseMidRefuted ops shape T busId S m = true := by
  unfold denseMidRefuted
  rw [decide_eq_true h]
  simp

/-- A same-bus message with a different constant key is mid-refuted. -/
theorem denseMidRefuted_of_keyNe (ops : DenseZModOps p) (shape : MemoryBusShape)
    (T : Thunk (DenseAddrCerts p)) (busId : Nat) (S m : BusInteraction (DenseExpr p))
    (kS km : List (ZMod p)) (hS : denseAddrKeyOf shape S = some kS)
    (hm : denseAddrKeyOf shape m = some km) (hne : kS ≠ km) :
    denseMidRefuted ops shape T busId S m = true := by
  unfold denseMidRefuted
  rw [denseAddrKeyOf_ne_constsNeq shape S m kS km hS hm hne]
  simp

/-- A cross-bus message is not a provable receive. -/
theorem denseProvRecv_of_crossBus (ops : DenseZModOps p) (shape : MemoryBusShape) (busId : Nat)
    (S m : BusInteraction (DenseExpr p)) (h : m.busId ≠ busId) :
    denseProvRecv ops shape busId S m = false := by
  unfold denseProvRecv
  rw [decide_eq_false h]
  simp

/-- A same-bus message with a different constant key is not a provable receive. -/
theorem denseProvRecv_of_keyNe (ops : DenseZModOps p) (shape : MemoryBusShape) (busId : Nat)
    (S m : BusInteraction (DenseExpr p)) (kS km : List (ZMod p))
    (hS : denseAddrKeyOf shape S = some kS) (hm : denseAddrKeyOf shape m = some km)
    (hne : kS ≠ km) : denseProvRecv ops shape busId S m = false := by
  unfold denseProvRecv
  rw [denseAddrKeyOf_ne_constsEq shape S m kS km hS hm hne]
  simp

/-- Skipped positions are pre-refuted (the shield's `P` test): `densePreRefuted` contains
    `denseMidRefuted` as its first disjunct. -/
theorem densePreRefuted_of_midRefuted (ops : DenseZModOps p) (shape : MemoryBusShape)
    (T : Thunk (DenseAddrCerts p)) (busId : Nat) (S m : BusInteraction (DenseExpr p))
    (h : denseMidRefuted ops shape T busId S m = true) :
    densePreRefuted ops shape T busId S m = true := by
  unfold densePreRefuted
  rw [h]
  simp

/-! ## The index -/

def denseKeyHash (k : List (ZMod p)) : UInt64 :=
  k.foldl (fun h c => mixHash h (hash c.val)) 7

/-- Per-bus constant-key position index: `byKey` buckets the bus's all-constant-key positions by
    key hash, `sym` lists its non-constant-key positions; both ascending. -/
structure DenseKeyIdx (p : ℕ) where
  byKey : Std.HashMap UInt64 (List Nat)
  sym : List Nat

/-- Insert one position (front of its bucket; the builder folds positions descending). -/
def denseKeyIdxAdd (shape : MemoryBusShape) (busId : Nat)
    (arr : Array (BusInteraction (DenseExpr p))) (pos : Nat) (idx : DenseKeyIdx p) :
    DenseKeyIdx p :=
  match arr[pos]? with
  | some m =>
    if m.busId = busId then
      match denseAddrKeyOf shape m with
      | some k =>
          let h := denseKeyHash k
          { idx with byKey := idx.byKey.insert h (pos :: idx.byKey.getD h []) }
      | none => { idx with sym := pos :: idx.sym }
    else idx
  | none => idx

def denseKeyIdxBuild (shape : MemoryBusShape) (busId : Nat)
    (arr : Array (BusInteraction (DenseExpr p))) : DenseKeyIdx p :=
  (List.range arr.size).foldr (denseKeyIdxAdd shape busId arr) ⟨∅, []⟩

/-- What the builder guarantees, all in one bundle: completeness (every same-bus position is in
    its key's bucket, or in `sym` when its key is not constant), and strict ascending order of
    every bucket and of `sym`. -/
structure DenseKeyIdx.Sound (shape : MemoryBusShape) (busId : Nat)
    (arr : Array (BusInteraction (DenseExpr p))) (idx : DenseKeyIdx p) : Prop where
  complete_key : ∀ pos m k, arr[pos]? = some m → m.busId = busId →
    denseAddrKeyOf shape m = some k → pos ∈ idx.byKey.getD (denseKeyHash k) []
  complete_sym : ∀ pos m, arr[pos]? = some m → m.busId = busId →
    denseAddrKeyOf shape m = none → pos ∈ idx.sym
  sorted_key : ∀ h, (idx.byKey.getD h []).Pairwise (· < ·)
  sorted_sym : idx.sym.Pairwise (· < ·)
  mem_key : ∀ h pos, pos ∈ idx.byKey.getD h [] → ∃ m k, arr[pos]? = some m ∧
    m.busId = busId ∧ denseAddrKeyOf shape m = some k ∧ denseKeyHash k = h
  mem_sym : ∀ pos, pos ∈ idx.sym → ∃ m, arr[pos]? = some m ∧ m.busId = busId ∧
    denseAddrKeyOf shape m = none

/-- The fold-step invariant: soundness for the positions processed so far, plus a lower bound
    keeping every stored position strictly above the positions still to be processed. -/
theorem denseKeyIdxBuild_sound_aux (shape : MemoryBusShape) (busId : Nat)
    (arr : Array (BusInteraction (DenseExpr p))) :
    ∀ (ps : List Nat), ps.Pairwise (· < ·) →
      (let idx := ps.foldr (denseKeyIdxAdd shape busId arr) ⟨∅, []⟩
       (∀ pos m k, pos ∈ ps → arr[pos]? = some m → m.busId = busId →
          denseAddrKeyOf shape m = some k → pos ∈ idx.byKey.getD (denseKeyHash k) []) ∧
       (∀ pos m, pos ∈ ps → arr[pos]? = some m → m.busId = busId →
          denseAddrKeyOf shape m = none → pos ∈ idx.sym) ∧
       (∀ h, (idx.byKey.getD h []).Pairwise (· < ·)) ∧
       idx.sym.Pairwise (· < ·) ∧
       (∀ h pos, pos ∈ idx.byKey.getD h [] → pos ∈ ps ∧ ∃ m k, arr[pos]? = some m ∧
          m.busId = busId ∧ denseAddrKeyOf shape m = some k ∧ denseKeyHash k = h) ∧
       (∀ pos, pos ∈ idx.sym → pos ∈ ps ∧ ∃ m, arr[pos]? = some m ∧ m.busId = busId ∧
          denseAddrKeyOf shape m = none)) := by
  intro ps hps
  induction ps with
  | nil =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [Std.HashMap.getD_empty]
  | cons q rest ih =>
      have hqlt : ∀ r ∈ rest, q < r := fun r hr => (List.pairwise_cons.mp hps).1 r hr
      obtain ⟨ck, cs, sk, ss, mk, ms⟩ := ih (List.pairwise_cons.mp hps).2
      simp only [List.foldr_cons]
      set idx := rest.foldr (denseKeyIdxAdd shape busId arr) (⟨∅, []⟩ : DenseKeyIdx p) with hidx
      unfold denseKeyIdxAdd
      cases hq : arr[q]? with
      | none =>
          dsimp only
          refine ⟨fun pos m k hpos hm hb hk => ?_, fun pos m hpos hm hb hk => ?_, sk, ss,
            fun h pos hpos => ?_, fun pos hpos => ?_⟩
          · rcases List.mem_cons.mp hpos with rfl | hpos
            · rw [hq] at hm; exact absurd hm (by simp)
            · exact ck pos m k hpos hm hb hk
          · rcases List.mem_cons.mp hpos with rfl | hpos
            · rw [hq] at hm; exact absurd hm (by simp)
            · exact cs pos m hpos hm hb hk
          · obtain ⟨hin, rest'⟩ := mk h pos hpos
            exact ⟨List.mem_cons_of_mem _ hin, rest'⟩
          · obtain ⟨hin, rest'⟩ := ms pos hpos
            exact ⟨List.mem_cons_of_mem _ hin, rest'⟩
      | some mq =>
          dsimp only
          by_cases hbq : mq.busId = busId
          · rw [if_pos hbq]
            cases hkq : denseAddrKeyOf shape mq with
            | some kq =>
                dsimp only
                refine ⟨fun pos m k hpos hm hb hk => ?_, fun pos m hpos hm hb hk => ?_,
                  fun h => ?_, ss, fun h pos hpos => ?_, fun pos hpos => ?_⟩
                · rcases List.mem_cons.mp hpos with rfl | hpos
                  · rw [hq] at hm
                    obtain rfl := Option.some.inj hm
                    rw [hkq] at hk
                    obtain rfl := Option.some.inj hk
                    rw [Std.HashMap.getD_insert_self]
                    exact List.mem_cons_self ..
                  · have hmem := ck pos m k hpos hm hb hk
                    by_cases hh : denseKeyHash kq = denseKeyHash k
                    · rw [← hh, Std.HashMap.getD_insert_self]
                      rw [← hh] at hmem
                      exact List.mem_cons_of_mem _ hmem
                    · rw [Std.HashMap.getD_insert,
                        if_neg (fun hc => hh (beq_iff_eq.mp hc))]
                      exact hmem
                · rcases List.mem_cons.mp hpos with rfl | hpos
                  · rw [hq] at hm
                    obtain rfl := Option.some.inj hm
                    rw [hkq] at hk
                    exact absurd hk (by simp)
                  · exact cs pos m hpos hm hb hk
                · by_cases hh : h = denseKeyHash kq
                  · subst hh
                    rw [Std.HashMap.getD_insert_self]
                    refine List.pairwise_cons.mpr ⟨fun r hr => ?_, sk _⟩
                    exact hqlt r (mk _ r hr).1
                  · rw [Std.HashMap.getD_insert,
                      if_neg (fun hc => hh (beq_iff_eq.mp hc).symm)]
                    exact sk h
                · by_cases hh : h = denseKeyHash kq
                  · subst hh
                    rw [Std.HashMap.getD_insert_self] at hpos
                    rcases List.mem_cons.mp hpos with rfl | hpos
                    · exact ⟨List.mem_cons_self .., mq, kq, hq, hbq, hkq, rfl⟩
                    · obtain ⟨hin, rest'⟩ := mk _ pos hpos
                      exact ⟨List.mem_cons_of_mem _ hin, rest'⟩
                  · rw [Std.HashMap.getD_insert,
                      if_neg (fun hc => hh (beq_iff_eq.mp hc).symm)] at hpos
                    obtain ⟨hin, rest'⟩ := mk h pos hpos
                    exact ⟨List.mem_cons_of_mem _ hin, rest'⟩
                · obtain ⟨hin, rest'⟩ := ms pos hpos
                  exact ⟨List.mem_cons_of_mem _ hin, rest'⟩
            | none =>
                dsimp only
                refine ⟨fun pos m k hpos hm hb hk => ?_, fun pos m hpos hm hb hk => ?_,
                  sk, ?_, fun h pos hpos => ?_, fun pos hpos => ?_⟩
                · rcases List.mem_cons.mp hpos with rfl | hpos
                  · rw [hq] at hm
                    obtain rfl := Option.some.inj hm
                    rw [hkq] at hk
                    exact absurd hk (by simp)
                  · exact ck pos m k hpos hm hb hk
                · rcases List.mem_cons.mp hpos with rfl | hpos
                  · exact List.mem_cons_self ..
                  · exact List.mem_cons_of_mem _ (cs pos m hpos hm hb hk)
                · refine List.pairwise_cons.mpr ⟨fun r hr => ?_, ss⟩
                  exact hqlt r (ms r hr).1
                · obtain ⟨hin, rest'⟩ := mk h pos hpos
                  exact ⟨List.mem_cons_of_mem _ hin, rest'⟩
                · rcases List.mem_cons.mp hpos with rfl | hpos
                  · exact ⟨List.mem_cons_self .., mq, hq, hbq, hkq⟩
                  · obtain ⟨hin, rest'⟩ := ms pos hpos
                    exact ⟨List.mem_cons_of_mem _ hin, rest'⟩
          · rw [if_neg hbq]
            refine ⟨fun pos m k hpos hm hb hk => ?_, fun pos m hpos hm hb hk => ?_, sk, ss,
              fun h pos hpos => ?_, fun pos hpos => ?_⟩
            · rcases List.mem_cons.mp hpos with rfl | hpos
              · rw [hq] at hm
                obtain rfl := Option.some.inj hm
                exact absurd hb hbq
              · exact ck pos m k hpos hm hb hk
            · rcases List.mem_cons.mp hpos with rfl | hpos
              · rw [hq] at hm
                obtain rfl := Option.some.inj hm
                exact absurd hb hbq
              · exact cs pos m hpos hm hb hk
            · obtain ⟨hin, rest'⟩ := mk h pos hpos
              exact ⟨List.mem_cons_of_mem _ hin, rest'⟩
            · obtain ⟨hin, rest'⟩ := ms pos hpos
              exact ⟨List.mem_cons_of_mem _ hin, rest'⟩

theorem denseKeyIdxBuild_sound (shape : MemoryBusShape) (busId : Nat)
    (arr : Array (BusInteraction (DenseExpr p))) :
    (denseKeyIdxBuild shape busId arr).Sound shape busId arr := by
  have hrange : (List.range arr.size).Pairwise (· < ·) := List.pairwise_lt_range
  obtain ⟨ck, cs, sk, ss, mk, ms⟩ :=
    denseKeyIdxBuild_sound_aux shape busId arr (List.range arr.size) hrange
  have hin : ∀ pos m, arr[pos]? = some m → pos ∈ List.range arr.size := by
    intro pos m hm
    rw [List.mem_range]
    by_contra hc
    rw [Array.getElem?_eq_none (Nat.le_of_not_lt hc)] at hm
    exact absurd hm (by simp)
  exact ⟨fun pos m k hm hb hk => ck pos m k (hin pos m hm) hm hb hk,
    fun pos m hm hb hk => cs pos m (hin pos m hm) hm hb hk,
    sk, ss,
    fun h pos hpos => (mk h pos hpos).2,
    fun pos hpos => (ms pos hpos).2⟩

/-! ## Ascending merge -/

def denseMergeAsc : List Nat → List Nat → List Nat
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
    if x ≤ y then x :: denseMergeAsc xs (y :: ys) else y :: denseMergeAsc (x :: xs) ys
  termination_by xs ys => xs.length + ys.length

theorem denseMergeAsc_mem : ∀ (xs ys : List Nat) (q : Nat),
    q ∈ denseMergeAsc xs ys ↔ q ∈ xs ∨ q ∈ ys
  | [], ys, q => by simp [denseMergeAsc]
  | x :: xs, [], q => by simp [denseMergeAsc]
  | x :: xs, y :: ys, q => by
      unfold denseMergeAsc
      split
      · simp only [List.mem_cons, denseMergeAsc_mem xs (y :: ys) q]
        tauto
      · simp only [List.mem_cons, denseMergeAsc_mem (x :: xs) ys q]
        tauto
  termination_by xs ys => xs.length + ys.length

theorem denseMergeAsc_pairwise : ∀ (xs ys : List Nat),
    xs.Pairwise (· < ·) → ys.Pairwise (· < ·) → (∀ x ∈ xs, x ∉ ys) →
    (denseMergeAsc xs ys).Pairwise (· < ·)
  | [], ys, _, hys, _ => by simpa [denseMergeAsc] using hys
  | x :: xs, [], hxs, _, _ => by simpa [denseMergeAsc] using hxs
  | x :: xs, y :: ys, hxs, hys, hdisj => by
      unfold denseMergeAsc
      obtain ⟨hxlt, hxs'⟩ := List.pairwise_cons.mp hxs
      obtain ⟨hylt, hys'⟩ := List.pairwise_cons.mp hys
      split
      · rename_i hxy
        refine List.pairwise_cons.mpr ⟨?_, ?_⟩
        · intro q hq
          rcases (denseMergeAsc_mem xs (y :: ys) q).mp hq with h | h
          · exact hxlt q h
          · rcases List.mem_cons.mp h with rfl | h
            · exact Nat.lt_of_le_of_ne hxy (fun hc =>
                hdisj x (List.mem_cons_self ..) (hc ▸ List.mem_cons_self ..))
            · exact Nat.lt_of_le_of_lt hxy (hylt q h)
        · exact denseMergeAsc_pairwise xs (y :: ys) hxs' hys
            (fun z hz => hdisj z (List.mem_cons_of_mem _ hz))
      · rename_i hxy
        have hyx : y < x := Nat.lt_of_not_le hxy
        refine List.pairwise_cons.mpr ⟨?_, ?_⟩
        · intro q hq
          rcases (denseMergeAsc_mem (x :: xs) ys q).mp hq with h | h
          · rcases List.mem_cons.mp h with rfl | h
            · exact hyx
            · exact Nat.lt_trans hyx (hxlt q h)
          · exact hylt q h
        · exact denseMergeAsc_pairwise (x :: xs) ys hxs hys'
            (fun z hz hzys => hdisj z hz (List.mem_cons_of_mem _ hzys))
  termination_by xs ys => xs.length + ys.length

/-! ## The sparse scans -/

/-- `denseLiveAllSegP` restricted to a position list. -/
def denseLiveAllSparse {α : Type} (preArr : Array α) (alive : Array Bool)
    (P : α → Bool) : List Nat → Bool
  | [] => true
  | pos :: rest =>
    (if alive[pos]?.getD false then (preArr[pos]?).elim true P else true)
      && denseLiveAllSparse preArr alive P rest

/-- `denseShieldScanSegP` restricted to a position list. -/
def denseShieldScanSparse {α : Type} (P Q : α → Bool) (preArr : Array α)
    (alive : Array Bool) : List Nat → Bool × Bool
  | [] => (false, true)
  | pos :: rest =>
    let r := denseShieldScanSparse P Q preArr alive rest
    if alive[pos]?.getD false then
      match preArr[pos]? with
      | some m0 => (r.1 || Q m0, r.2 && (P m0 || r.1))
      | none => r
    else r

/-- A visited-position list that covers every non-refuted live position decides the full range
    scan: skipped positions contribute the identity (`P` holds on them). -/
theorem denseLiveAllSparse_eq {α : Type} (preArr : Array α) (alive : Array Bool)
    (P : α → Bool) :
    ∀ (n lo : Nat) (vs : List Nat), vs.Pairwise (· < ·) →
      (∀ q ∈ vs, lo ≤ q ∧ q < lo + n) →
      (∀ q, lo ≤ q → q < lo + n → q ∉ vs → ∀ m, preArr[q]? = some m →
        alive[q]?.getD false = true → P m = true) →
      denseLiveAllSparse preArr alive P vs = denseLiveAllSegP preArr alive P lo n := by
  intro n
  induction n with
  | zero =>
      intro lo vs _ hbound _
      cases vs with
      | nil => rfl
      | cons q rest => exact absurd (hbound q (List.mem_cons_self ..)) (by omega)
  | succ n ih =>
      intro lo vs hsort hbound hskip
      have hstepid : (lo ∉ vs) →
          (if alive[lo]?.getD false then (preArr[lo]?).elim true P else true) = true := by
        intro hnot
        cases halive : alive[lo]?.getD false with
        | false => simp
        | true =>
            rw [if_pos rfl]
            cases hm : preArr[lo]? with
            | none => rfl
            | some m => exact hskip lo (Nat.le_refl _) (by omega) hnot m hm halive
      cases vs with
      | nil =>
          rw [denseLiveAllSegP, ← ih (lo + 1) [] (by simp) (by simp)
            (fun q hq1 hq2 _ => hskip q (by omega) (by omega) (by simp)),
            hstepid (by simp)]
          rfl
      | cons q rest =>
          by_cases hq : q = lo
          · subst hq
            rw [denseLiveAllSparse, denseLiveAllSegP]
            have hrest : ∀ r ∈ rest, q < r := fun r hr => (List.pairwise_cons.mp hsort).1 r hr
            rw [ih (q + 1) rest (List.pairwise_cons.mp hsort).2
              (fun r hr => ⟨hrest r hr, by have := (hbound r (List.mem_cons_of_mem _ hr)).2; omega⟩)
              (fun r hr1 hr2 hnot m hm halive => hskip r (by omega) (by omega)
                (by
                  intro hmem
                  rcases List.mem_cons.mp hmem with rfl | hmem
                  · omega
                  · exact hnot hmem) m hm halive)]
          · have hlonot : lo ∉ (q :: rest) := by
              intro hmem
              rcases List.mem_cons.mp hmem with rfl | hmem
              · exact hq rfl
              · have := (List.pairwise_cons.mp hsort).1 lo hmem
                have := (hbound q (List.mem_cons_self ..)).1
                omega
            rw [denseLiveAllSegP, hstepid hlonot, Bool.true_and]
            refine ih (lo + 1) (q :: rest) hsort (fun r hr => ?_)
              (fun r hr1 hr2 hnot m hm halive => hskip r (by omega) (by omega) hnot m hm halive)
            obtain ⟨h1, h2⟩ := hbound r hr
            rcases List.mem_cons.mp hr with rfl | hmem
            · refine ⟨by omega, by omega⟩
            · have hq1 := (hbound q (List.mem_cons_self ..)).1
              have := (List.pairwise_cons.mp hsort).1 r hmem
              exact ⟨by omega, by omega⟩

/-- Same for the shield scan: skipped positions have `P` true (pre-refuted) and `Q` false (not a
    provable receive), which is the fold's identity step. -/
theorem denseShieldScanSparse_eq {α : Type} (P Q : α → Bool) (preArr : Array α)
    (alive : Array Bool) :
    ∀ (n lo : Nat) (vs : List Nat), vs.Pairwise (· < ·) →
      (∀ q ∈ vs, lo ≤ q ∧ q < lo + n) →
      (∀ q, lo ≤ q → q < lo + n → q ∉ vs → ∀ m, preArr[q]? = some m →
        alive[q]?.getD false = true → P m = true ∧ Q m = false) →
      denseShieldScanSparse P Q preArr alive vs = denseShieldScanSegP P Q preArr alive lo n := by
  intro n
  induction n with
  | zero =>
      intro lo vs _ hbound _
      cases vs with
      | nil => rfl
      | cons q rest => exact absurd (hbound q (List.mem_cons_self ..)) (by omega)
  | succ n ih =>
      intro lo vs hsort hbound hskip
      have hstepid : (lo ∉ vs) → ∀ (r : Bool × Bool),
          (if alive[lo]?.getD false then
            match preArr[lo]? with
            | some m0 => (r.1 || Q m0, r.2 && (P m0 || r.1))
            | none => r
          else r) = r := by
        intro hnot r
        cases halive : alive[lo]?.getD false with
        | false => simp
        | true =>
            rw [if_pos rfl]
            cases hm : preArr[lo]? with
            | none => rfl
            | some m =>
                obtain ⟨hP, hQ⟩ := hskip lo (Nat.le_refl _) (by omega) hnot m hm halive
                simp [hP, hQ]
      cases vs with
      | nil =>
          rw [denseShieldScanSegP]
          rw [← ih (lo + 1) [] (by simp) (by simp)
            (fun q hq1 hq2 _ => hskip q (by omega) (by omega) (by simp))]
          exact (hstepid (by simp) _).symm
      | cons q rest =>
          by_cases hq : q = lo
          · subst hq
            rw [denseShieldScanSparse, denseShieldScanSegP]
            have hrest : ∀ r ∈ rest, q < r := fun r hr => (List.pairwise_cons.mp hsort).1 r hr
            rw [ih (q + 1) rest (List.pairwise_cons.mp hsort).2
              (fun r hr => ⟨hrest r hr, by have := (hbound r (List.mem_cons_of_mem _ hr)).2; omega⟩)
              (fun r hr1 hr2 hnot m hm halive => hskip r (by omega) (by omega)
                (by
                  intro hmem
                  rcases List.mem_cons.mp hmem with rfl | hmem
                  · omega
                  · exact hnot hmem) m hm halive)]
            rfl
          · have hlonot : lo ∉ (q :: rest) := by
              intro hmem
              rcases List.mem_cons.mp hmem with rfl | hmem
              · exact hq rfl
              · have := (List.pairwise_cons.mp hsort).1 lo hmem
                have := (hbound q (List.mem_cons_self ..)).1
                omega
            rw [denseShieldScanSegP]
            rw [← ih (lo + 1) (q :: rest) hsort (fun r hr => by
                obtain ⟨h1, h2⟩ := hbound r hr
                have hrne : r ≠ lo := fun hrl => hlonot (hrl ▸ hr)
                exact ⟨by omega, by omega⟩)
              (fun r hr1 hr2 hnot m hm halive => hskip r (by omega) (by omega) hnot m hm halive)]
            exact (hstepid hlonot _).symm

/-! ## The combined region test

One decision for a candidate pair's mid and shield regions, sparse when the candidate's address
key is constant, with the scan results already converted to the forms `denseMkDropResult`
consumes. -/

/-- Decide both region tests for the candidate `S` at `i` with matched receive at `j`. With a
    constant candidate key the scans visit only the same-key bucket and the symbolic-key list;
    every skipped position is refuted by the bus-id or constant-key arm. -/
def denseRegionTests (ops : DenseZModOps p) (shape : MemoryBusShape)
    (T : Thunk (DenseAddrCerts p)) (busId : Nat)
    (arr : Array (BusInteraction (DenseExpr p))) (alive : Array Bool)
    (preArr : Array (DenseAddrPre p))
    (hpre : preArr = arr.map (denseAddrPrep shape T.get.tworoot))
    (kIdx : DenseKeyIdx p) (hkIdx : kIdx = denseKeyIdxBuild shape busId arr)
    (S : BusInteraction (DenseExpr p)) (preS : DenseAddrPre p)
    (hpreS : preS = denseAddrPrep shape T.get.tworoot S)
    (i j : Nat) (hij : i < j) :
    { b : Bool // b = true →
      (∀ m0 ∈ denseLiveSeg arr alive (i + 1) (j - i - 1),
        denseMidRefuted ops shape T busId S m0 = true) ∧
      denseShieldOk ops shape T busId S (denseLiveSeg arr alive 0 i) = true } :=
  -- converting a full-region result to the consumed forms (shared by both paths)
  have hmidOf : denseLiveAllSegP preArr alive
      (denseMidRefutedP ops T.get.nonzero busId preS) (i + 1) (j - i - 1) = true →
      ∀ m0 ∈ denseLiveSeg arr alive (i + 1) (j - i - 1),
        denseMidRefuted ops shape T busId S m0 = true := by
    intro hmidB
    rw [hpre, denseLiveAllSegP_eq, denseLiveAllSeg_eq] at hmidB
    intro m0 hm0
    have h := List.all_eq_true.mp hmidB m0 hm0
    rw [hpreS] at h
    rwa [denseMidRefutedP_eq] at h
  have hshieldOf : (denseShieldScanSegP
      (densePreRefutedP ops T.get.nonzero busId (denseSetNewMult ops shape) preS)
      (denseProvRecvP busId (denseGetPreviousMult ops shape) preS)
      preArr alive 0 i).2 = true →
      denseShieldOk ops shape T busId S (denseLiveSeg arr alive 0 i) = true := by
    intro hshieldA
    rw [hpre, denseShieldScanSegP_eq] at hshieldA
    have hP : (fun m => densePreRefutedP ops T.get.nonzero busId
          (denseSetNewMult ops shape) preS (denseAddrPrep shape T.get.tworoot m))
        = densePreRefuted ops shape T busId S :=
      funext fun m => by rw [hpreS]; exact densePreRefutedP_eq ops shape T busId S m
    have hQ : (fun m => denseProvRecvP busId (denseGetPreviousMult ops shape) preS
          (denseAddrPrep shape T.get.tworoot m))
        = denseProvRecv ops shape busId S :=
      funext fun m => by rw [hpreS]; exact denseProvRecvP_eq ops shape T.get.tworoot busId S m
    rw [hP, hQ, denseShieldScanW_eq] at hshieldA
    exact hshieldA
  match hkS : denseAddrKeyOf shape S with
  | none =>
      ⟨denseLiveAllSegP preArr alive
            (denseMidRefutedP ops T.get.nonzero busId preS) (i + 1) (j - i - 1)
          && (denseShieldScanSegP
            (densePreRefutedP ops T.get.nonzero busId (denseSetNewMult ops shape) preS)
            (denseProvRecvP busId (denseGetPreviousMult ops shape) preS)
            preArr alive 0 i).2, by
        intro hb
        rw [Bool.and_eq_true] at hb
        exact ⟨hmidOf hb.1, hshieldOf hb.2⟩⟩
  | some kS =>
      let bucket := kIdx.byKey.getD (denseKeyHash kS) []
      let visMid := denseMergeAsc
        (bucket.filter (fun q => decide (i + 1 ≤ q) && decide (q < j)))
        (kIdx.sym.filter (fun q => decide (i + 1 ≤ q) && decide (q < j)))
      let visShield := denseMergeAsc
        (bucket.filter (fun q => decide (q < i)))
        (kIdx.sym.filter (fun q => decide (q < i)))
      have hsound := hkIdx ▸ denseKeyIdxBuild_sound shape busId arr
      -- bucket/sym disjointness (a position's key cannot be both constant and not)
      have hdisj : ∀ q, q ∈ bucket → q ∈ kIdx.sym → False := by
        intro q hqb hqs
        obtain ⟨m, k, hm, _, hk, _⟩ := hsound.mem_key _ q hqb
        obtain ⟨m', hm', _, hk'⟩ := hsound.mem_sym q hqs
        rw [hm] at hm'
        obtain rfl := Option.some.inj hm'
        rw [hk] at hk'
        exact absurd hk' (by simp)
      -- a skipped in-range position is refuted: cross-bus, or constant key ≠ kS
      have hskipP : ∀ (inRange : Nat → Prop) (vs : List Nat),
          (∀ q, q ∈ bucket → inRange q → q ∈ vs) →
          (∀ q, q ∈ kIdx.sym → inRange q → q ∈ vs) →
          ∀ q, inRange q → q ∉ vs → ∀ m, arr[q]? = some m →
            denseMidRefuted ops shape T busId S m = true ∧
            denseProvRecv ops shape busId S m = false := by
        intro inRange vs hbk hsy q hqr hqnot m hm
        by_cases hbus : m.busId = busId
        · cases hkm : denseAddrKeyOf shape m with
          | none =>
              exact absurd (hsy q (hsound.complete_sym q m hm hbus hkm) hqr) hqnot
          | some km =>
              by_cases hkeq : km = kS
              · subst hkeq
                exact absurd (hbk q (hsound.complete_key q m km hm hbus hkm) hqr) hqnot
              · refine ⟨denseMidRefuted_of_keyNe ops shape T busId S m kS km hkS hkm
                  (fun h => hkeq (h.symm)) , ?_⟩
                exact denseProvRecv_of_keyNe ops shape busId S m kS km hkS hkm
                  (fun h => hkeq h.symm)
        · exact ⟨denseMidRefuted_of_crossBus ops shape T busId S m hbus,
            denseProvRecv_of_crossBus ops shape busId S m hbus⟩
      ⟨denseLiveAllSparse preArr alive
            (denseMidRefutedP ops T.get.nonzero busId preS) visMid
          && (denseShieldScanSparse
            (densePreRefutedP ops T.get.nonzero busId (denseSetNewMult ops shape) preS)
            (denseProvRecvP busId (denseGetPreviousMult ops shape) preS)
            preArr alive visShield).2, by
        intro hb
        rw [Bool.and_eq_true] at hb
        obtain ⟨hmidB, hshieldA⟩ := hb
        have hbucketSorted : bucket.Pairwise (· < ·) := hsound.sorted_key _
        have hsymSorted : kIdx.sym.Pairwise (· < ·) := hsound.sorted_sym
        -- the mid region
        have hmid : denseLiveAllSegP preArr alive
            (denseMidRefutedP ops T.get.nonzero busId preS) (i + 1) (j - i - 1) = true := by
          rw [← denseLiveAllSparse_eq preArr alive
            (denseMidRefutedP ops T.get.nonzero busId preS) (j - i - 1) (i + 1) visMid
            (denseMergeAsc_pairwise _ _ (hbucketSorted.filter _) (hsymSorted.filter _)
              (fun x hx hx' => hdisj x (List.mem_of_mem_filter hx) (List.mem_of_mem_filter hx')))
            (fun q hq => by
              rcases (denseMergeAsc_mem _ _ q).mp hq with h | h <;>
              · have := List.of_mem_filter h
                simp only [Bool.and_eq_true, decide_eq_true_eq] at this
                omega)
            (fun q hq1 hq2 hqnot m hm halive => by
              rw [hpre, Array.getElem?_map] at hm
              cases harr : arr[q]? with
              | none => rw [harr] at hm; exact absurd hm (by simp)
              | some m0 =>
                  rw [harr] at hm
                  obtain rfl := Option.some.inj hm
                  have href := (hskipP (fun q => i + 1 ≤ q ∧ q < j) visMid
                    (fun q hqb hqr => (denseMergeAsc_mem _ _ q).mpr (Or.inl
                      (List.mem_filter.mpr ⟨hqb, by
                        simp only [Bool.and_eq_true, decide_eq_true_eq]; omega⟩)))
                    (fun q hqs hqr => (denseMergeAsc_mem _ _ q).mpr (Or.inr
                      (List.mem_filter.mpr ⟨hqs, by
                        simp only [Bool.and_eq_true, decide_eq_true_eq]; omega⟩)))
                    q ⟨hq1, by omega⟩ hqnot m0 harr).1
                  rw [hpreS, denseMidRefutedP_eq]
                  exact href)]
          exact hmidB
        -- the shield region
        have hshield : (denseShieldScanSegP
            (densePreRefutedP ops T.get.nonzero busId (denseSetNewMult ops shape) preS)
            (denseProvRecvP busId (denseGetPreviousMult ops shape) preS)
            preArr alive 0 i).2 = true := by
          rw [← denseShieldScanSparse_eq
            (densePreRefutedP ops T.get.nonzero busId (denseSetNewMult ops shape) preS)
            (denseProvRecvP busId (denseGetPreviousMult ops shape) preS)
            preArr alive i 0 visShield
            (denseMergeAsc_pairwise _ _ (hbucketSorted.filter _) (hsymSorted.filter _)
              (fun x hx hx' => hdisj x (List.mem_of_mem_filter hx) (List.mem_of_mem_filter hx')))
            (fun q hq => by
              rcases (denseMergeAsc_mem _ _ q).mp hq with h | h <;>
              · have := List.of_mem_filter h
                simp only [decide_eq_true_eq] at this
                omega)
            (fun q hq1 hq2 hqnot m hm halive => by
              rw [hpre, Array.getElem?_map] at hm
              cases harr : arr[q]? with
              | none => rw [harr] at hm; exact absurd hm (by simp)
              | some m0 =>
                  rw [harr] at hm
                  obtain rfl := Option.some.inj hm
                  have href := hskipP (fun q => q < i) visShield
                    (fun q hqb hqr => (denseMergeAsc_mem _ _ q).mpr (Or.inl
                      (List.mem_filter.mpr ⟨hqb, by simp only [decide_eq_true_eq]; omega⟩)))
                    (fun q hqs hqr => (denseMergeAsc_mem _ _ q).mpr (Or.inr
                      (List.mem_filter.mpr ⟨hqs, by simp only [decide_eq_true_eq]; omega⟩)))
                    q (by omega) hqnot m0 harr
                  constructor
                  · rw [hpreS, densePreRefutedP_eq]
                    exact densePreRefuted_of_midRefuted ops shape T busId S m0 href.1
                  · rw [hpreS, denseProvRecvP_eq]
                    exact href.2)]
          exact hshieldA
        exact ⟨hmidOf hmid, hshieldOf hshield⟩⟩

end ApcOptimizer.Dense
