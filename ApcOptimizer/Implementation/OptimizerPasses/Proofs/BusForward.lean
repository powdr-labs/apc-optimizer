import ApcOptimizer.Implementation.OptimizerPasses.BusForward
import ApcOptimizer.Implementation.OptimizerPasses.Proofs.BusUnify

set_option autoImplicit false

/-! # Soundness for the dense `busForward` pass

`DensePassCorrect` for `denseBusForwardF` (`BusForward.lean`). The pass only adds constraints, so
soundness is a constraint superset (`DensePassCorrect.denseAddConstraints`); the substance is the
chain lemma `memFwdChain`: through strictly-ordered, internally same-address receive→send pairs, a
payload slot preserved by every pair is forwarded from the send to the receive whatever the pairs'
aliasing. Per assignment, a pair either aliases the window address — then the discipline routes
the value through it and preservation carries the slot — or it does not and is excluded like any
different-address message; the syntactic certificate never decides which.

The strict ordering of the pairs is load-bearing. With interleaved pairs `r_A r_B s_A s_B` the
both-alias case only forces `S = r_A` and `s_B = R`, leaving `r_B` (hence `R`) unconstrained, so
an assignment exploiting that satisfies `admissibleMemoryBus` while violating the would-be
equality. `denseBFCheckPairs` verifies the ordering positionally. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Local copies of `Proofs/BusUnify.lean`'s private helpers -/

private theorem bfConstValueEval (e : DenseExpr p) (c : ZMod p) (h : e.constValue? = some c)
    (denv : VarId → ZMod p) : e.eval denv = c := by
  rw [← DenseExpr.fold_eval e denv]
  grind [DenseExpr.constValue?, DenseExpr.eval]

private theorem bf_list_at {γ : Type} {l : List γ} {i : Nat} {x : γ} (h : l[i]? = some x) :
    l = l.take i ++ x :: l.drop (i + 1) ∧ (l.take i).length = i := by
  obtain ⟨hi, hx⟩ := List.getElem?_eq_some_iff.1 h
  refine ⟨?_, by simp [Nat.min_eq_left hi.le]⟩
  conv_lhs => rw [← List.take_append_drop i l]
  rw [List.drop_eq_getElem_cons hi, hx]

private theorem bf_arr_get {γ β : Type} (l : List γ) (f : γ → β) {k : Nat} {x : γ}
    (h : l[k]? = some x) : (l.toArray.map f)[k]? = some (f x) := by
  simp [h]

private theorem bf_arr_get_inv {γ β : Type} (l : List γ) (f : γ → β) {k : Nat} {y : β}
    (h : (l.toArray.map f)[k]? = some y) : ∃ x, l[k]? = some x ∧ y = f x := by
  have h' : (l[k]?).map f = some y := by simpa using h
  cases hx : l[k]? <;> rw [hx] at h' <;> simp_all

private theorem bf_mem_of_filter_get {d : DenseConstraintSystem p} {busId k : Nat}
    {S : BusInteraction (DenseExpr p)}
    (h : (d.busInteractions.filter (fun bi => bi.busId = busId))[k]? = some S) :
    S ∈ d.busInteractions :=
  List.mem_of_mem_filter (List.mem_of_getElem? h)

/-! ## Segment plumbing -/

/-- Splitting the segment `[q, j)` of `l` at a position `q ≤ k < j`. -/
private theorem bf_seg_split {γ : Type} (l : List γ) (q k j : Nat) (x : γ)
    (hqk : q ≤ k) (hkj : k < j) (hk : l[k]? = some x) :
    (l.drop q).take (j - q)
      = (l.drop q).take (k - q) ++ x :: (l.drop (k + 1)).take (j - (k + 1)) := by
  obtain ⟨hklen, hx⟩ := List.getElem?_eq_some_iff.1 hk
  rw [show j - q = (k - q) + (j - k) by omega, List.take_add, List.drop_drop,
    show q + (k - q) = k by omega, List.drop_eq_getElem_cons hklen, hx,
    show j - k = (j - (k + 1)) + 1 by omega, List.take_succ_cons]

private theorem bf_mem_seg {γ : Type} {l : List γ} {a n : Nat} {x : γ}
    (h : x ∈ (l.drop a).take n) : ∃ r, a ≤ r ∧ r < a + n ∧ l[r]? = some x := by
  obtain ⟨t, ht⟩ := List.getElem?_of_mem h
  rw [List.getElem?_take] at ht
  split at ht
  · rename_i htlt
    rw [List.getElem?_drop] at ht
    exact ⟨a + t, by omega, by omega, ht⟩
  · exact absurd ht (by simp)

/-! ## Slot-wise value lemmas -/

/-- Slot-wise form of `densePayloadSlot_eval_eq`. -/
private theorem bf_slot_getD_eq (P Q : List (DenseExpr p)) (denv : VarId → ZMod p) (t : Nat)
    (h : (P.map (fun e => e.eval denv))[t]? = (Q.map (fun e => e.eval denv))[t]?) :
    ((P[t]?).getD (.const 0)).eval denv = ((Q[t]?).getD (.const 0)).eval denv := by
  simp only [List.getElem?_map] at h
  cases hP : P[t]? <;> cases hQ : Q[t]? <;> rw [hP, hQ] at h <;> simp_all

/-- A syntactically preserved slot is preserved on the evaluated messages. -/
theorem denseBFSlotEq_sound (r s : BusInteraction (DenseExpr p)) (t : Nat)
    (h : denseBFSlotEq r s t = true) (denv : VarId → ZMod p) :
    (denseBIEval r denv).payload[t]? = (denseBIEval s denv).payload[t]? := by
  show (r.payload.map (fun e => e.eval denv))[t]? = (s.payload.map (fun e => e.eval denv))[t]?
  unfold denseBFSlotEq at h
  simp only [List.getElem?_map]
  cases hr : r.payload[t]? with
  | none => rw [hr] at h; simp at h
  | some e =>
    rw [hr] at h
    cases hs : s.payload[t]? with
    | none => rw [hs] at h; simp at h
    | some e' =>
      rw [hs] at h
      simp only [Option.map_some, Option.some.injEq]
      rcases (Bool.or_eq_true _ _).mp h with he | hc
      · rw [of_decide_eq_true he]
      · cases hce : e.constValue? with
        | none => rw [hce] at hc; simp at hc
        | some c =>
          cases hce' : e'.constValue? with
          | none => rw [hce, hce'] at hc; simp at hc
          | some c' =>
            rw [hce, hce'] at hc
            rw [bfConstValueEval e c hce denv, bfConstValueEval e' c' hce' denv,
              of_decide_eq_true hc]

/-! ## The chain lemma -/

/-- `mid` splits into messages excluded at the window address `av` (inactive or evaluated-address
    `≠ av`) and, in strict left-to-right order, the given internally same-address receive→send
    forwarding pairs. -/
inductive MemFwdMid (shape : MemoryBusShape) (av : List (Option (ZMod p))) :
    List (BusInteraction (ZMod p) × BusInteraction (ZMod p)) →
    List (BusInteraction (ZMod p)) → Prop
  | nil (mid : List (BusInteraction (ZMod p)))
      (hexcl : ∀ m ∈ mid, m.multiplicity ≠ 0 → shape.address m = av → False) :
      MemFwdMid shape av [] mid
  | cons (r s : BusInteraction (ZMod p))
      (pairs : List (BusInteraction (ZMod p) × BusInteraction (ZMod p)))
      (excl0 excl1 mid2 : List (BusInteraction (ZMod p)))
      (hexcl0 : ∀ m ∈ excl0, m.multiplicity ≠ 0 → shape.address m = av → False)
      (hexcl1 : ∀ m ∈ excl1, m.multiplicity ≠ 0 → shape.address m = av → False)
      (hr : r.multiplicity = -shape.setNewMult) (hs : s.multiplicity = shape.setNewMult)
      (hrs : shape.address r = shape.address s)
      (hrest : MemFwdMid shape av pairs mid2) :
      MemFwdMid shape av ((r, s) :: pairs) (excl0 ++ r :: excl1 ++ s :: mid2)

theorem MemFwdMid.prepend_excl {shape : MemoryBusShape} {av : List (Option (ZMod p))}
    {pairs : List (BusInteraction (ZMod p) × BusInteraction (ZMod p))}
    {mid : List (BusInteraction (ZMod p))} (E : List (BusInteraction (ZMod p)))
    (hE : ∀ m ∈ E, m.multiplicity ≠ 0 → shape.address m = av → False)
    (h : MemFwdMid shape av pairs mid) : MemFwdMid shape av pairs (E ++ mid) := by
  cases h with
  | nil mid hexcl =>
    exact .nil _ (fun m hm => (List.mem_append.1 hm).elim (hE m) (hexcl m))
  | cons r s pairs excl0 excl1 mid2 hexcl0 hexcl1 hr hs hrs hrest =>
    rw [show E ++ (excl0 ++ r :: excl1 ++ s :: mid2) = (E ++ excl0) ++ r :: excl1 ++ s :: mid2
      by simp]
    exact .cons r s pairs (E ++ excl0) excl1 mid2
      (fun m hm => (List.mem_append.1 hm).elim (hE m) (hexcl0 m)) hexcl1 hr hs hrs hrest

/-- The chain lemma. `S` (send) and `R` (receive) sit at the same evaluated address `av`; the
    messages between them split per `MemFwdMid`. A payload slot preserved by every forwarding pair
    reaches `R` from `S`: per assignment, the head pair either aliases `av` — the discipline pairs
    `S` with its receive, preservation carries the slot to its send, and the recursion continues
    from that send — or it does not alias and joins the excluded set (`prepend_excl`). -/
theorem memFwdChain (shape : MemoryBusShape) (hp1 : (1 : ZMod p) ≠ 0)
    (Lraw : List (BusInteraction (ZMod p)))
    (hadm : admissibleMemoryBus shape (Lraw.filter (fun m => decide (m.multiplicity ≠ 0))))
    (av : List (Option (ZMod p))) :
    ∀ (pairs : List (BusInteraction (ZMod p) × BusInteraction (ZMod p)))
      (mid : List (BusInteraction (ZMod p))), MemFwdMid shape av pairs mid →
      ∀ (pre post : List (BusInteraction (ZMod p))) (S R : BusInteraction (ZMod p)),
        Lraw = pre ++ S :: mid ++ R :: post →
        S.multiplicity = shape.setNewMult → R.multiplicity = -shape.setNewMult →
        shape.address S = av → shape.address R = av →
        ∀ t : Nat, (∀ pr ∈ pairs, pr.1.payload[t]? = pr.2.payload[t]?) →
        S.payload[t]? = R.payload[t]?
  | [], mid, hmid, pre, post, S, R, hL, hS, hR, hSav, hRav, t, _ => by
    cases hmid with
    | nil _ hexcl =>
      have hpay : S.payload = R.payload :=
        admissibleMemoryBus.consecutive shape Lraw hp1 hadm pre mid post S R hL hS hR
          (hSav.trans hRav.symm) (fun m hm hne haddr => hexcl m hm hne (haddr.trans hSav))
      exact congrArg (fun P => P[t]?) hpay
  | (r, s) :: rest, mid, hmid, pre, post, S, R, hL, hS, hR, hSav, hRav, t, hpres => by
    cases hmid with
    | cons _ _ _ excl0 excl1 mid2 hexcl0 hexcl1 hr hs hrs hrest =>
      by_cases hral : shape.address r = av
      · -- the pair aliases: `S` pairs with `r`; preservation carries the slot to `s`; recurse.
        have hSr : S.payload = r.payload :=
          admissibleMemoryBus.consecutive shape Lraw hp1 hadm pre excl0
            (excl1 ++ s :: mid2 ++ R :: post) S r
            (by rw [hL]; simp) hS hr (hSav.trans hral.symm)
            (fun m hm hne haddr => hexcl0 m hm hne (haddr.trans hSav))
        have hsR : s.payload[t]? = R.payload[t]? :=
          memFwdChain shape hp1 Lraw hadm av rest mid2 hrest
            (pre ++ S :: excl0 ++ r :: excl1) post s R
            (by rw [hL]; simp) hs hR (hrs.symm.trans hral) hRav t
            (fun pr hpr => hpres pr (List.mem_cons_of_mem _ hpr))
        calc S.payload[t]? = r.payload[t]? := congrArg (fun P => P[t]?) hSr
          _ = s.payload[t]? := hpres (r, s) (List.mem_cons_self ..)
          _ = R.payload[t]? := hsR
      · -- the pair does not alias: both halves join the excluded set; recurse on `rest`.
        have hmid' : MemFwdMid shape av rest (excl0 ++ r :: excl1 ++ s :: mid2) := by
          have h1 : MemFwdMid shape av rest (s :: mid2) :=
            MemFwdMid.prepend_excl [s] (by
              intro m hm _ haddr
              rw [List.mem_singleton.1 hm] at haddr
              exact hral (hrs.trans haddr)) hrest
          have h2 := MemFwdMid.prepend_excl (excl0 ++ r :: excl1) (by
              intro m hm hne haddr
              rcases List.mem_append.1 hm with hm0 | hm1
              · exact hexcl0 m hm0 hne haddr
              · rcases List.mem_cons.1 hm1 with rfl | hm1'
                · exact hral haddr
                · exact hexcl1 m hm1' hne haddr) h1
          simpa using h2
        exact memFwdChain shape hp1 Lraw hadm av rest _ hmid' pre post S R hL hS hR hSav hRav t
          (fun pr hpr => hpres pr (List.mem_cons_of_mem _ hpr))

/-! ## The verifier: from the certificate to `MemFwdMid` -/

/-- A `denseBUMidScan`-cleared range `[a, b)` of the bus list is excluded, message-wise. -/
private theorem bf_seg_excl (d : DenseConstraintSystem p) (reg : VarRegistry)
    (hcov : d.CoveredBy reg) (shape : MemoryBusShape) (T : DenseTwoRootMap p)
    (hT : T.Sound d.algebraicConstraints)
    (bisL : List (BusInteraction (DenseExpr p)))
    (hsub : ∀ m ∈ bisL, m ∈ d.busInteractions)
    (S : BusInteraction (DenseExpr p)) (hScov : denseBICovered reg S)
    (denv : VarId → ZMod p) (hcon : ∀ c ∈ d.algebraicConstraints, c.eval denv = 0)
    (a b : Nat)
    (hscan : denseBUMidScan denseZModOps (denseBUWits d)
        (bisL.toArray.map (denseBUPrep shape T)) (denseBUPrep shape T S) b (b - a) a = true) :
    ∀ m ∈ ((bisL.drop a).take (b - a)).map (fun bi => denseBIEval bi denv),
      m.multiplicity ≠ 0 → shape.address m = shape.address (denseBIEval S denv) → False := by
  intro m hm
  obtain ⟨m0, hm0, rfl⟩ := List.mem_map.1 hm
  obtain ⟨r, har, hrb, hr⟩ := bf_mem_seg hm0
  have hok := denseBUMidScan_sound denseZModOps (denseBUWits d)
    (bisL.toArray.map (denseBUPrep shape T)) (denseBUPrep shape T S) b (b - a) a hscan
    r (denseBUPrep shape T m0) har (by omega) (by omega)
    (bf_arr_get bisL (denseBUPrep shape T) hr)
  exact denseBUMidOk_sound d reg hcov shape T hT S m0 hScov
    (hcov.2 m0 (hsub m0 (List.mem_of_getElem? hr))) hok denv hcon

/-- A verified pair list yields the evaluated `MemFwdMid` decomposition of the segment `[q, j)`,
    with the syntactic per-slot preservation test carrying over to the evaluated pairs. -/
private theorem denseBFCheckPairs_sound (d : DenseConstraintSystem p) (reg : VarRegistry)
    (hcov : d.CoveredBy reg) (shape : MemoryBusShape) (T : DenseTwoRootMap p)
    (hT : T.Sound d.algebraicConstraints)
    (bisL : List (BusInteraction (DenseExpr p)))
    (hsub : ∀ m ∈ bisL, m ∈ d.busInteractions)
    (S : BusInteraction (DenseExpr p)) (hScov : denseBICovered reg S)
    (denv : VarId → ZMod p) (hcon : ∀ c ∈ d.algebraicConstraints, c.eval denv = 0) :
    ∀ (pairs : List (Nat × Nat)) (q j : Nat),
      denseBFCheckPairs denseZModOps (denseBUWits d) (denseSetNewMult denseZModOps shape)
          (denseGetPreviousMult denseZModOps shape)
          (bisL.toArray.map (denseBUPrep shape T)) (denseBUPrep shape T S) j pairs q = true →
      ∃ evPairs, MemFwdMid shape (shape.address (denseBIEval S denv)) evPairs
          (((bisL.drop q).take (j - q)).map (fun bi => denseBIEval bi denv)) ∧
        ∀ t : Nat, denseBFPairsPreserve bisL.toArray pairs t = true →
          ∀ pr ∈ evPairs, pr.1.payload[t]? = pr.2.payload[t]?
  | [], q, j, hchk => by
    refine ⟨[], MemFwdMid.nil _
      (bf_seg_excl d reg hcov shape T hT bisL hsub S hScov denv hcon q j hchk), ?_⟩
    intro t _ pr hpr
    simp at hpr
  | (k, l) :: rest, q, j, hchk => by
    rw [denseBFCheckPairs] at hchk
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
    obtain ⟨⟨⟨hqk, hkl⟩, hlj⟩, hmatch⟩ := hchk
    cases hak : (bisL.toArray.map (denseBUPrep shape T))[k]? with
    | none => rw [hak] at hmatch; cases (bisL.toArray.map (denseBUPrep shape T))[l]? <;>
        simp at hmatch
    | some ak =>
      rw [hak] at hmatch
      cases hal : (bisL.toArray.map (denseBUPrep shape T))[l]? with
      | none => rw [hal] at hmatch; simp at hmatch
      | some al =>
        rw [hal] at hmatch
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hmatch
        obtain ⟨⟨⟨⟨⟨hakm, halm⟩, haddrkl⟩, hscan0⟩, hscan1⟩, hrestchk⟩ := hmatch
        obtain ⟨rk, hrk, rfl⟩ := bf_arr_get_inv bisL (denseBUPrep shape T) hak
        obtain ⟨sl, hsl, rfl⟩ := bf_arr_get_inv bisL (denseBUPrep shape T) hal
        rw [denseBUPrep_mult, denseGetPreviousMult_eq] at hakm
        rw [denseBUPrep_mult, denseSetNewMult_eq] at halm
        have hrkm : (denseBIEval rk denv).multiplicity = -shape.setNewMult :=
          bfConstValueEval rk.multiplicity _ hakm denv
        have hslm : (denseBIEval sl denv).multiplicity = shape.setNewMult :=
          bfConstValueEval sl.multiplicity _ halm denv
        have haddrEv : shape.address (denseBIEval rk denv)
            = shape.address (denseBIEval sl denv) :=
          denseAddrConstsEq_sound shape rk sl
            (by rw [← denseBUConstsEq_eq shape T rk sl]; exact haddrkl) denv
        obtain ⟨evRest, hmidRest, hpresRest⟩ := denseBFCheckPairs_sound d reg hcov shape T hT
          bisL hsub S hScov denv hcon rest (l + 1) j hrestchk
        have hsplit : (bisL.drop q).take (j - q)
            = (bisL.drop q).take (k - q)
              ++ (rk :: (bisL.drop (k + 1)).take (l - (k + 1)))
              ++ sl :: (bisL.drop (l + 1)).take (j - (l + 1)) := by
          rw [bf_seg_split bisL q k j rk hqk (by omega) hrk,
            bf_seg_split bisL (k + 1) l j sl (by omega) hlj hsl]
          simp
        refine ⟨(denseBIEval rk denv, denseBIEval sl denv) :: evRest, ?_, ?_⟩
        · rw [hsplit]
          simp only [List.map_append, List.map_cons]
          exact MemFwdMid.cons _ _ _ _ _ _
            (bf_seg_excl d reg hcov shape T hT bisL hsub S hScov denv hcon q k hscan0)
            (bf_seg_excl d reg hcov shape T hT bisL hsub S hScov denv hcon (k + 1) l hscan1)
            hrkm hslm haddrEv hmidRest
        · intro t hpt pr hpr
          have hbk : bisL.toArray[k]? = some rk := by simpa using hrk
          have hbl : bisL.toArray[l]? = some sl := by simpa using hsl
          simp only [denseBFPairsPreserve, List.all_cons, Bool.and_eq_true, hbk, hbl] at hpt
          rcases List.mem_cons.1 hpr with rfl | hpr'
          · exact denseBFSlotEq_sound rk sl t hpt.1 denv
          · exact hpresRest t hpt.2 pr hpr'

/-- The engine's verifier entails the chain lemma's conclusion: every slot equality it emits
    vanishes on every admissible satisfying assignment. -/
theorem denseBFCheckCert_sound (d : DenseConstraintSystem p) (bs : BusSemantics p)
    (facts : BusFacts p bs) (hp1 : (1 : ZMod p) ≠ 0) (reg : VarRegistry) (hcov : d.CoveredBy reg)
    (T : DenseTwoRootMap p) (hT : T.Sound d.algebraicConstraints)
    (busId : Nat) (shape : MemoryBusShape) (hshape : facts.memShape busId = some shape)
    (bisL : List (BusInteraction (DenseExpr p)))
    (hbis : bisL = d.busInteractions.filter (fun bi => bi.busId = busId))
    (i : Nat) (pairs : List (Nat × Nat)) (j : Nat) (S R : BusInteraction (DenseExpr p))
    (hS : bisL[i]? = some S) (hR : bisL[j]? = some R)
    (hchk : denseBFCheckCert denseZModOps (denseBUWits d) (denseSetNewMult denseZModOps shape)
        (denseGetPreviousMult denseZModOps shape) (bisL.toArray.map (denseBUPrep shape T))
        i pairs j = true)
    (denv : VarId → ZMod p) (hadm : d.admissible bs denv) (hsat : d.satisfies bs denv) :
    ∀ c ∈ denseBFEmit shape bisL.toArray pairs S R, c.eval denv = 0 := by
  have hai := bf_arr_get bisL (denseBUPrep shape T) hS
  have haj := bf_arr_get bisL (denseBUPrep shape T) hR
  unfold denseBFCheckCert at hchk
  rw [hai, haj] at hchk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨⟨⟨⟨⟨hij, hSm⟩, hRm⟩, haddrEq⟩, -⟩, hpairs⟩ := hchk
  rw [denseBUPrep_mult, denseSetNewMult_eq] at hSm
  rw [denseBUPrep_mult, denseGetPreviousMult_eq] at hRm
  subst hbis
  set bisL := d.busInteractions.filter (fun bi => bi.busId = busId) with hbisL
  have hsub : ∀ m ∈ bisL, m ∈ d.busInteractions := fun m hm => List.mem_of_mem_filter hm
  have hScov : denseBICovered reg S := hcov.2 S (hsub S (List.mem_of_getElem? hS))
  have hcon : ∀ c ∈ d.algebraicConstraints, c.eval denv = 0 := hsat.1
  have hSev : (denseBIEval S denv).multiplicity = shape.setNewMult :=
    bfConstValueEval S.multiplicity _ hSm denv
  have hRev : (denseBIEval R denv).multiplicity = -shape.setNewMult :=
    bfConstValueEval R.multiplicity _ hRm denv
  have haddrSR : shape.address (denseBIEval S denv) = shape.address (denseBIEval R denv) :=
    denseAddrConstsEq_sound shape S R
      (by rw [← denseBUConstsEq_eq shape T S R]; exact haddrEq) denv
  -- the evaluated-list admissibility (as in `denseConsecutivePayloadEq`)
  have hadm' : bs.admissible ((d.busInteractions.map (fun bi => denseBIEval bi denv)).filter
      (fun m => decide (m.multiplicity ≠ 0) && bs.isStateful m.busId)) := hadm
  have hb := facts.admissible_sound (d.busInteractions.map (fun bi => denseBIEval bi denv)) hadm'
    busId shape hshape
  rw [dense_map_eval_filter_busId] at hb
  -- the split at the endpoints
  obtain ⟨hsplitS, hlenS⟩ := bf_list_at hS
  obtain ⟨hsplitR, hlenR⟩ := bf_list_at hR
  have hsplit : bisL = bisL.take i ++ S :: (bisL.drop (i + 1)).take (j - i - 1)
      ++ R :: bisL.drop (j + 1) :=
    dense_split_of_positions hlenS hsplitS hlenR hsplitR hij
  -- the pairs
  obtain ⟨evPairs, hmid, hpres⟩ := denseBFCheckPairs_sound d reg hcov shape T hT bisL hsub S
    hScov denv hcon pairs (i + 1) j hpairs
  rw [Nat.sub_sub] at hsplit
  -- the chain
  have hchain : ∀ t : Nat, denseBFPairsPreserve bisL.toArray pairs t = true →
      (denseBIEval S denv).payload[t]? = (denseBIEval R denv).payload[t]? := by
    intro t hpt
    exact memFwdChain shape hp1 (bisL.map (fun bi => denseBIEval bi denv)) hb
      (shape.address (denseBIEval S denv)) evPairs _ hmid
      ((bisL.take i).map (fun bi => denseBIEval bi denv))
      ((bisL.drop (j + 1)).map (fun bi => denseBIEval bi denv))
      (denseBIEval S denv) (denseBIEval R denv)
      (by conv_lhs => rw [hsplit]
          simp)
      hSev hRev rfl haddrSR.symm t (hpres t hpt)
  -- the emitted equalities
  intro c hc
  unfold denseBFEmit at hc
  obtain ⟨t, htmem, rfl⟩ := List.mem_map.1 hc
  have htf := List.mem_filter.1 htmem
  simp only [Bool.and_eq_true] at htf
  rw [denseEqExpr_eval]
  rw [bf_slot_getD_eq R.payload S.payload denv t (hchain t htf.2.2).symm, sub_self]

/-! ## From the emitted equalities back to a verified certificate -/

theorem denseBFCollect_mem (ops : DenseZModOps p) (nw : DenseNonzeroWits p)
    (setMult prevMult : ZMod p) (shape : MemoryBusShape)
    (bis : Array (BusInteraction (DenseExpr p))) (arr : Array (DenseBUPre p)) :
    ∀ (props : List (Nat × List (Nat × Nat) × Nat)) (c : DenseExpr p),
      c ∈ denseBFCollect ops nw setMult prevMult shape bis arr props →
      ∃ i pairs j S R, denseBFCheckCert ops nw setMult prevMult arr i pairs j = true ∧
        bis[i]? = some S ∧ bis[j]? = some R ∧ c ∈ denseBFEmit shape bis pairs S R
  | [], c, hc => by simp [denseBFCollect] at hc
  | (i, pairs, j) :: rest, c, hc => by
      rw [denseBFCollect] at hc
      split at hc
      · rename_i hchk
        split at hc
        · rename_i S R hSi hRj
          rcases List.mem_append.1 hc with h | h
          · exact ⟨i, pairs, j, S, R, hchk, hSi, hRj, h⟩
          · exact denseBFCollect_mem ops nw setMult prevMult shape bis arr rest c h
        · exact denseBFCollect_mem ops nw setMult prevMult shape bis arr rest c hc
      · exact denseBFCollect_mem ops nw setMult prevMult shape bis arr rest c hc

theorem denseBFForBus_mem (ops : DenseZModOps p) (T : DenseTwoRootMap p)
    (nw : DenseNonzeroWits p) (shape : MemoryBusShape)
    (bisL : List (BusInteraction (DenseExpr p))) (c : DenseExpr p)
    (hc : c ∈ denseBFForBus ops T nw shape bisL) :
    ∃ i pairs j S R,
      denseBFCheckCert ops nw (denseSetNewMult ops shape) (denseGetPreviousMult ops shape)
        (bisL.toArray.map (denseBUPrep shape T)) i pairs j = true ∧
      bisL[i]? = some S ∧ bisL[j]? = some R ∧ c ∈ denseBFEmit shape bisL.toArray pairs S R := by
  obtain ⟨i, pairs, j, S, R, hchk, hSi, hRj, hmem⟩ :=
    denseBFCollect_mem ops nw _ _ shape bisL.toArray _ _ c hc
  exact ⟨i, pairs, j, S, R, hchk, by simpa using hSi, by simpa using hRj, hmem⟩

/-- The structure of an emitted equality: a declared bus, positions in that bus's interaction
    list, and the verifier's verdict on the certificate. -/
theorem denseBFEqs_mem (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p)
    {c : DenseExpr p} (hc : c ∈ denseBFEqs facts.memShape d) :
    ∃ busId shape i pairs j S R,
      facts.memShape busId = some shape ∧
      (d.busInteractions.filter (fun bi => bi.busId = busId))[i]? = some S ∧
      (d.busInteractions.filter (fun bi => bi.busId = busId))[j]? = some R ∧
      denseBFCheckCert denseZModOps (denseBUWits d) (denseSetNewMult denseZModOps shape)
        (denseGetPreviousMult denseZModOps shape)
        ((d.busInteractions.filter (fun bi => bi.busId = busId)).toArray.map
          (denseBUPrep shape (denseBUTable (denseBUBusLists facts.memShape d.busInteractions) d)))
        i pairs j = true ∧
      c ∈ denseBFEmit shape (d.busInteractions.filter (fun bi => bi.busId = busId)).toArray
        pairs S R := by
  rw [show denseBFEqs facts.memShape d
      = (if (denseBUBusLists facts.memShape d.busInteractions).isEmpty then []
         else denseBFEqsOf (denseBUBusLists facts.memShape d.busInteractions) d) from rfl] at hc
  split at hc
  · simp at hc
  · rw [show denseBFEqsOf (denseBUBusLists facts.memShape d.busInteractions) d
        = ((denseBUBusLists facts.memShape d.busInteractions).map (fun sl =>
            denseBFForBus denseZModOps
              (denseBUTable (denseBUBusLists facts.memShape d.busInteractions) d)
              (denseBUWits d) sl.2.1 sl.2.2)).flatten from rfl,
      List.mem_flatten] at hc
    obtain ⟨l, hl, hcl⟩ := hc
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hl
    obtain ⟨hms, hfilter⟩ := denseBUBusLists_mem he
    obtain ⟨i, pairs, j, S, R, hchk, hSi, hRj, hmem⟩ := denseBFForBus_mem _ _ _ _ _ c hcl
    rw [hfilter] at hSi hRj hchk hmem
    exact ⟨e.1, e.2.1, i, pairs, j, S, R, hms, hSi, hRj, hchk, hmem⟩

/-! ## The appended constraints -/

/-- Every var of an emitted slot equality comes from the send's or receive's payload. -/
theorem denseBFEmit_vars (shape : MemoryBusShape) (bis : Array (BusInteraction (DenseExpr p)))
    (pairs : List (Nat × Nat)) (S Rt : BusInteraction (DenseExpr p))
    {c : DenseExpr p} (hc : c ∈ denseBFEmit shape bis pairs S Rt) {z : VarId} (hz : z ∈ c.vars) :
    (∃ e ∈ Rt.payload, z ∈ e.vars) ∨ (∃ e ∈ S.payload, z ∈ e.vars) := by
  grind [denseBFEmit, denseEqExpr, DenseExpr.vars, List.mem_of_getElem?]

theorem denseBusForwardNewCs_subset (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) {c : DenseExpr p} (h : c ∈ denseBusForwardNewCs bs facts d) :
    c ∈ denseBFEqs facts.memShape d := by
  rw [show denseBusForwardNewCs bs facts d
      = (if (denseBFEqs facts.memShape d).isEmpty then []
         else denseBUFilterNew d (denseBFEqs facts.memShape d)) from rfl] at h
  split at h
  · simp at h
  · exact denseBUFilterNew_subset d _ h

theorem denseBusForwardNewCs_vars (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) :
    ∀ c ∈ denseBusForwardNewCs bs facts d, ∀ z ∈ c.vars, z ∈ d.occ := by
  intro c hc z hz
  obtain ⟨busId, shape, i, pairs, j, S, R, _, hSi, hRj, _, hmem⟩ :=
    denseBFEqs_mem bs facts d (denseBusForwardNewCs_subset bs facts d hc)
  rcases denseBFEmit_vars shape _ pairs S R hmem hz with ⟨e, he, hze⟩ | ⟨e, he, hze⟩
  · exact DenseConstraintSystem.mem_occ_of_payload (bf_mem_of_filter_get hRj) he hze
  · exact DenseConstraintSystem.mem_occ_of_payload (bf_mem_of_filter_get hSi) he hze

theorem denseBusForwardNewCs_sound (bs : BusSemantics p) (facts : BusFacts p bs)
    (reg : VarRegistry) (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg)
    (hp1 : (1 : ZMod p) ≠ 0) (denv : VarId → ZMod p) (hadm : d.admissible bs denv)
    (hsat : d.satisfies bs denv) :
    ∀ c ∈ denseBusForwardNewCs bs facts d, c.eval denv = 0 := by
  intro c hc
  obtain ⟨busId, shape, i, pairs, j, S, R, hms, hSi, hRj, hchk, hmem⟩ :=
    denseBFEqs_mem bs facts d (denseBusForwardNewCs_subset bs facts d hc)
  exact denseBFCheckCert_sound d bs facts hp1 reg hcov _
    (denseBUTable_sound (denseBUBusLists facts.memShape d.busInteractions) d) busId shape hms
    _ rfl i pairs j S R hSi hRj hchk denv hadm hsat c hmem

/-! ## The pass -/

/-- The `let`-bound body, unfolded (definitionally). -/
theorem denseBusForwardF_eq (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) :
    denseBusForwardF bs facts d =
      (if (1 : ZMod p) ≠ 0 then
        (if (denseBusForwardNewCs bs facts d).isEmpty then d
         else { d with algebraicConstraints :=
                  d.algebraicConstraints ++ denseBusForwardNewCs bs facts d })
       else d) := rfl

theorem denseBusForwardF_covered (reg : VarRegistry) (bs : BusSemantics p)
    (facts : BusFacts p bs) (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg) :
    (denseBusForwardF bs facts d).CoveredBy reg := by
  rw [denseBusForwardF_eq]
  split_ifs with hp1 _hempty
  · exact hcov
  · refine ⟨fun e he => ?_, hcov.2⟩
    rcases List.mem_append.1 he with h | h
    · exact hcov.1 e h
    · intro i hi
      exact DenseConstraintSystem.occ_valid hcov i
        (denseBusForwardNewCs_vars bs facts d e h i hi)
  · exact hcov

theorem denseBusForwardF_correct (reg : VarRegistry) (bs : BusSemantics p)
    (facts : BusFacts p bs) (d : DenseConstraintSystem p) (hcov : d.CoveredBy reg) :
    DensePassCorrect reg.isInput d (denseBusForwardF bs facts d) [] bs := by
  rw [denseBusForwardF_eq]
  split_ifs with hp1 _hempty
  · exact DensePassCorrect.refl reg.isInput d bs
  · exact DensePassCorrect.denseAddConstraints d bs (denseBusForwardNewCs bs facts d)
      (denseBusForwardNewCs_vars bs facts d)
      (fun denv hadm hsat => denseBusForwardNewCs_sound bs facts reg d hcov hp1 denv hadm hsat)
  · exact DensePassCorrect.refl reg.isInput d bs

/-- The dense `busForward` pass (see `denseBusForwardF`). -/
def denseBusForwardPass : DenseVerifiedPassW p :=
  DenseVerifiedPassW.of denseBusForwardF (fun _ _ _ => [])
    (fun reg bs facts d hcov => denseBusForwardF_covered reg bs facts d hcov)
    (fun _ _ _ _ _ => by intro x hx; simp at hx)
    (fun reg bs facts d hcov => denseBusForwardF_correct reg bs facts d hcov)

end ApcOptimizer.Dense
