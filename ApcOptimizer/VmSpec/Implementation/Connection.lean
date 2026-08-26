import ApcOptimizer.VmSpec.Implementation.Realizes
import ApcOptimizer.VmSpec.Implementation.Validation
import Mathlib.Data.List.Forall2
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

/-! Connecting `Spec.lean`'s per-chip replacement conditions to `Basic.lean`'s VM-level
    `VmEquivalent`. This file proves the **soundness** half: if every guest chip is replaced by a
    `Circuit.isSoundReplacementOf`, the optimized VM can produce no effect the original could not
    (`vmSoundReplacement_of_forall₂`).

    Only *one* chip is ever replaced at a time (`vmSoundReplacement_cons`). Replacing many is then
    a chain of single steps: `VmSoundReplacement.trans` composes them, and
    `VmSoundReplacement.of_perm` rotates the list between steps so that the chip to replace next
    is always at the head. That is what `Validation.lean`'s "the guest-chip list is a set" buys.

    In a single step, two vocabularies have to be bridged:

    * `VmSat` gives each guest instance only `Circuit.satisfiesAlgebraic`, whereas
      `Circuit.satisfies` also demands `BusSemantics.accepts` on every active message.
      `Host.forcesAccepts` (`Realizes.lean`) is the missing half, and it is derived, not assumed.

    * `Circuit.sideEffects` — what a sound replacement preserves — covers only *stateful* buses,
      whereas `VmAssignment.busEffect` sums over *all* of them. So replacing a guest chip may well
      unbalance the stateless buses (dropping a redundant range check is exactly this), and the
      host's lookup chips have to be rebuilt to match. `Host.absorbsStateless` is the permission
      to do that, and it pins the input and output chips, so the observed `VmEffect` is carried
      across untouched.

    Where the assumptions live: everything about the guest chips is `Circuit.legalGuest`, every
    clause of which has the shape "the chip's algebraic constraints imply X", and it is required
    only of the chips the optimizer was *given* — `VmSat` carries it for what the optimizer
    produced, through the `Host.legalGuest` field. Everything else is a property of the fixed VM,
    collected into the single `Host.realizes`. -/

variable {p : ℕ}

--------- Choosing the original assignment a sound replacement promises ---------

open Classical in
/-- The original-circuit assignment `Circuit.isSoundReplacementOf` promises for `asg`, as a total
    function (`asg` itself on inputs where no such assignment exists, which
    `soundWitness_spec`'s hypothesis rules out). -/
noncomputable def soundWitness (optimized original : Circuit p) (bs : BusSemantics p)
    (asg : ChipAssignment p) : ChipAssignment p :=
  if h : ∃ asg', original.satisfies bs asg' ∧
      optimized.sideEffects bs asg = original.sideEffects bs asg'
    then h.choose else asg

theorem soundWitness_spec {optimized original : Circuit p} {bs : BusSemantics p}
    {asg : ChipAssignment p}
    (h : ∃ asg', original.satisfies bs asg' ∧
      optimized.sideEffects bs asg = original.sideEffects bs asg') :
    original.satisfies bs (soundWitness optimized original bs asg) ∧
      optimized.sideEffects bs asg =
        original.sideEffects bs (soundWitness optimized original bs asg) := by
  rw [soundWitness, dif_pos h]
  exact h.choose_spec

--------- Splitting a guest assignment at the first chip type ---------

theorem guestNet_cons {c : Circuit p} {R : Guest p} {l : List (ChipAssignment p)}
    {gA : GuestAssignment p R} {gA' : GuestAssignment p (c :: R)}
    (h0 : gA' 0 = l) (hs : ∀ i : Fin R.length, gA' i.succ = gA i) (m : BusMessage p) :
    gA'.busEffect m = (l.map (fun asg => c.allEffects asg m)).sum + gA.busEffect m := by
  show (∑ t : Fin (R.length + 1),
      ((gA' t).map (fun asg => ((c :: R).get t).allEffects asg m)).sum)
    = (l.map (fun asg => c.allEffects asg m)).sum
      + ∑ t : Fin R.length, ((gA t).map (fun asg => (R.get t).allEffects asg m)).sum
  rw [Fin.sum_univ_succ, h0]
  exact congrArg₂ (· + ·) rfl (Finset.sum_congr rfl (fun i _ => by rw [hs i]; rfl))

theorem guestInstanceCount_cons {c : Circuit p} {R : Guest p}
    {l : List (ChipAssignment p)} {gA : GuestAssignment p R}
    {gA' : GuestAssignment p (c :: R)}
    (h0 : gA' 0 = l) (hs : ∀ i : Fin R.length, gA' i.succ = gA i) :
    gA'.instanceCount = l.length + gA.instanceCount := by
  show (∑ t : Fin (R.length + 1), (gA' t).length)
    = l.length + ∑ t : Fin R.length, (gA t).length
  rw [Fin.sum_univ_succ, h0]
  exact congrArg₂ (· + ·) rfl (Finset.sum_congr rfl (fun i _ => by rw [hs i]))

--------- Carrying the observed effect across ---------

/-- Two assignments over the same host with the same input- and output-chip instances have the
    same observable effect, whatever their guest chips do. -/
theorem effects_eq_of_io {host : Host p} {G G' : Guest p}
    {a : VmAssignment p ⟨host, G⟩} {a' : VmAssignment p ⟨host, G'⟩}
    (hin : ∀ i ∈ host.inputChips, a.hostAssignment i = a'.hostAssignment i)
    (hout : a.hostAssignment host.outputChip = a'.hostAssignment host.outputChip) :
    a.effects = a'.effects := by
  have hinst : (host.inputChips.flatMap fun i => (a.hostAssignment i).map (fun c => (i, c)))
      = host.inputChips.flatMap fun i => (a'.hostAssignment i).map (fun c => (i, c)) :=
    List.flatMap_congr (fun i hi => by rw [hin i hi])
  have hord : a.orderedInputInstances = a'.orderedInputInstances := by
    unfold VmAssignment.orderedInputInstances VmAssignment.inputInstances
    rw [hinst]
  exact congrArg₂ VmEffect.mk
    (congrArg (List.flatMap fun x => host.getInputChunk x.1 x.2) hord)
    (congrArg host.getOutput (congrArg (fun l => l.headD 0) hout))

--------- One substitution ---------

/-- **The soundness half of the VM-level connection, for a single chip.** Replacing one guest
    chip by a `Circuit.isSoundReplacementOf` of it, leaving the rest of the VM alone, produces no
    effect the original could not.

    The witness keeps the host's stateful chips — memory, input, output — exactly as they were,
    replaces each instance of the substituted chip by the assignment
    `Circuit.isSoundReplacementOf` promises, and lets `Host.absorbsStateless` rebuild the lookup
    chips around the difference.

    Legality is required of the list being *run* — the optimized one. Nothing is asked of `c`:
    `VmSat` carries no circuit-level property, so the restored run has nothing to re-establish. -/
theorem vmSoundReplacement_cons [Fact p.Prime]
    {host : Host p} {bs : BusSemantics p} {rm : RankModel p} {r0 : GuestBusRules p}
    {c c' : Circuit p} {R : Guest p}
    (hHost : host.realizes bs rm r0)
    (hLegal : ∀ d ∈ c' :: R, host.legalGuest d)
    (hSound : c'.isSoundReplacementOf c bs) :
    VmSoundReplacement host (c :: R) (c' :: R) := by
  rintro e ⟨a', hsat', rfl⟩
  -- The host forces every optimized guest instance to be `Circuit.satisfies`-good.
  have hsat'g : ∀ (t : Fin (c' :: R).length), ∀ asg ∈ a'.guestAssignments t,
      ((c' :: R).get t).satisfies bs asg :=
    hHost.forcesAccepts (c' :: R) hLegal a' hsat'
  -- Per instance of the replaced chip, the original assignment soundness promises.
  set w : ChipAssignment p → ChipAssignment p := soundWitness c' c bs with hw
  have hwit : ∀ asg ∈ a'.guestAssignments 0,
      c.satisfies bs (w asg) ∧ c'.sideEffects bs asg = c.sideEffects bs (w asg) :=
    fun asg hasg => soundWitness_spec (hSound.1 asg (hsat'g 0 asg hasg))
  set gA : GuestAssignment p (c :: R) :=
    Fin.cons ((a'.guestAssignments 0).map w) (Fin.tail a'.guestAssignments) with hgA
  have hg0 : gA 0 = (a'.guestAssignments 0).map w := by rw [hgA]; exact Fin.cons_zero _ _
  have hgs : ∀ i : Fin R.length, gA i.succ = a'.guestAssignments i.succ := by
    intro i; rw [hgA]; exact Fin.cons_succ _ _ i
  have hsatG : ∀ t : Fin (c :: R).length, ∀ asg ∈ gA t, ((c :: R).get t).satisfies bs asg := by
    intro t
    induction t using Fin.cases with
    | zero =>
      rw [hg0]
      intro asg hasg
      obtain ⟨asg0, hasg0, rfl⟩ := List.mem_map.mp hasg
      exact (hwit asg0 hasg0).1
    | succ i =>
      intro asg hasg
      rw [hgs i] at hasg
      exact hsat'g i.succ asg hasg
  -- Stateful buses see no change at all: that is exactly what `sideEffects` preservation says.
  have hstateful : ∀ m : BusMessage p, bs.isStateful m.1 = true →
      gA.busEffect m = a'.guestAssignments.busEffect m := by
    intro m hm
    have h1 := guestNet_cons (gA := Fin.tail a'.guestAssignments) (gA' := gA) hg0 hgs m
    have h2 := guestNet_cons (c := c') (l := a'.guestAssignments 0)
      (gA := Fin.tail a'.guestAssignments) (gA' := a'.guestAssignments) rfl (fun _ => rfl) m
    rw [h1, h2, add_left_inj, List.map_map]
    refine congrArg List.sum (List.map_congr_left (fun asg hasg => ?_))
    show c.allEffects (w asg) m = c'.allEffects asg m
    rw [allEffects_eq_sideEffects hm, allEffects_eq_sideEffects hm, ← (hwit asg hasg).2]
  -- The stateless imbalance the replacement leaves behind.
  set δ : BusState p := fun m => a'.guestAssignments.busEffect m - gA.busEffect m with hδ
  have hδspec : ∀ m : BusMessage p, δ m ≠ 0 →
      bs.isStateful m.1 = false ∧ ∃ mult : ZMod p, mult ≠ 0 ∧ bs.accepts ⟨m.1, mult, m.2⟩ := by
    intro m hm
    have hne : a'.guestAssignments.busEffect m ≠ gA.busEffect m := sub_ne_zero.mp hm
    refine ⟨?_, ?_⟩
    · by_contra hst
      exact hne (hstateful m (by simpa using hst)).symm
    · -- Some instance, original or optimized, actively carries `m`; its chip `satisfies`.
      have hactive : ∃ (d : Circuit p) (asg : ChipAssignment p),
          d.satisfies bs asg ∧ d.allEffects asg m ≠ 0 := by
        by_cases hz : a'.guestAssignments.busEffect m = 0
        · obtain ⟨t, asg, hasg, hne'⟩ :=
            exists_instance_of_guestNet_ne_zero (fun hc => hne (hz.trans hc.symm))
          exact ⟨(c :: R).get t, asg, hsatG t asg hasg, hne'⟩
        · obtain ⟨t, asg, hasg, hne'⟩ := exists_instance_of_guestNet_ne_zero hz
          exact ⟨(c' :: R).get t, asg, hsat'g t asg hasg, hne'⟩
      obtain ⟨d, asg, hdsat, hdne⟩ := hactive
      obtain ⟨bi, hbi, hmsg, hmult⟩ := exists_active_of_allEffects_ne_zero hdne
      refine ⟨(bi.eval asg).multiplicity, hmult, ?_⟩
      rw [← show ((bi.eval asg).busId, (bi.eval asg).payload) = m from hmsg]
      exact hdsat.2 bi hbi hmult
  obtain ⟨hA', hA'legal, hA'net, hA'in, hA'out⟩ :=
    hHost.absorbsStateless a'.hostAssignment (hsat'.satisfiesHost) δ hδspec
  have hsat : VmSat (⟨host, c :: R⟩ : Vm p) ⟨gA, hA'⟩ := by
    refine ⟨fun t asg hasg => (hsatG t asg hasg).1, hA'legal, fun m => ?_, ?_⟩
    · have hb : a'.guestAssignments.busEffect m + a'.hostAssignment.busEffect m = 0 :=
        hsat'.balances m
      have hn : hA'.busEffect m = a'.hostAssignment.busEffect m + δ m := congrFun hA'net m
      rw [busEffect_apply, hn, hδ]
      show gA.busEffect m +
        (a'.hostAssignment.busEffect m + (a'.guestAssignments.busEffect m - gA.busEffect m)) = 0
      linear_combination hb
    · -- Instance counts are preserved exactly (the new list is a `map`), so the budget transfers.
      show gA.instanceCount ≤ host.maxInstances
      have h1 := guestInstanceCount_cons (gA := Fin.tail a'.guestAssignments) (gA' := gA) hg0 hgs
      have h2 := guestInstanceCount_cons (c := c') (l := a'.guestAssignments 0)
        (gA := Fin.tail a'.guestAssignments) (gA' := a'.guestAssignments) rfl (fun _ => rfl)
      rw [h1, List.length_map, ← h2]
      exact hsat'.withinBudget
  exact ⟨⟨gA, hA'⟩, hsat, effects_eq_of_io hA'in hA'out⟩

--------- Many substitutions ---------

/-- The induction behind `vmSoundReplacement_of_forall₂`: `S` accumulates the chips already
    replaced, rotated to the back of the list, so the next chip to replace is always at the head.

    Note that legality is needed of *both* lists, not just the optimized one: the intermediate
    lists mix chips from each, and `Host.forcesAccepts` applies to a whole list. -/
theorem vmSoundReplacement_append [Fact p.Prime]
    {host : Host p} {bs : BusSemantics p} {rm : RankModel p} {r0 : GuestBusRules p}
    (hHost : host.realizes bs rm r0)
    {T T' : Guest p}
    (hSound : List.Forall₂ (fun c c' => c'.isSoundReplacementOf c bs) T T') :
    host.legalGuests (T ++ T') →
    ∀ S : Guest p, host.legalGuests S →
        VmSoundReplacement host (T ++ S) (S ++ T') := by
  induction hSound with
  | nil => intro _ S _; simpa using VmSoundReplacement.refl host S
  | @cons c c' U U' hcc _ ih =>
    intro hLegal S hLS
    have hmemU : ∀ d ∈ U, d ∈ (c :: U) ++ (c' :: U') := fun d hd => by simp [hd]
    have hmemU' : ∀ d ∈ U', d ∈ (c :: U) ++ (c' :: U') := fun d hd => by simp [hd]
    have hlc' : host.legalGuest c' := hLegal c' (by simp)
    have h1 : VmSoundReplacement host (c :: (U ++ S)) (c' :: (U ++ S)) := by
      refine vmSoundReplacement_cons hHost (fun d hd => ?_) hcc
      rcases List.mem_cons.mp hd with rfl | hd
      · exact hlc'
      · rcases List.mem_append.mp hd with hd | hd
        · exact hLegal d (hmemU d hd)
        · exact hLS d hd
    have h2 : VmSoundReplacement host (c' :: (U ++ S)) (U ++ (S ++ [c'])) :=
      VmSoundReplacement.of_perm (by
        rw [← List.append_assoc]
        exact (List.perm_append_singleton c' (U ++ S)).symm)
    have h3 : VmSoundReplacement host (U ++ (S ++ [c'])) ((S ++ [c']) ++ U') := by
      refine ih (fun d hd => ?_) (S ++ [c']) (fun d hd => ?_)
      · rcases List.mem_append.mp hd with hd | hd
        · exact hLegal d (hmemU d hd)
        · exact hLegal d (hmemU' d hd)
      · rcases List.mem_append.mp hd with hd | hd
        · exact hLS d hd
        · rw [List.mem_singleton.mp hd]; exact hlc'
    simpa using h1.trans (h2.trans h3)

/-- **The soundness half of the VM-level connection.** If every guest chip of `G'` is a sound
    replacement for the corresponding chip of `G`, then `G'` is a `VmSoundReplacement` for `G`
    against `host`: every effect the optimized guest chips can produce, the original ones can
    produce too.

    Legality is required of *both* lists at once, and the `G'` half is not redundant: the
    intermediate lists of `vmSoundReplacement_append` mix chips from each, and `Host.forcesAccepts`
    runs its balancing argument over whichever whole list the VM is executing. That single
    hypothesis is also all that is assumed about the optimizer's output — the interaction-count
    bound that keeps those arguments from wrapping around `ZMod p` is a clause of legality
    (`Circuit.legalGuest`'s `size`), so it rides along.

    Whoever supplies this has to establish `G'` legal *somehow*; per-chip soundness does not give
    it — nothing in `Circuit.isSoundReplacementOf` rules out a sound replacement that violates
    `Circuit.statelessSendOnly` outright. -/
theorem vmSoundReplacement_of_forall₂ [Fact p.Prime]
    {host : Host p} {bs : BusSemantics p} {rm : RankModel p} {r0 : GuestBusRules p}
    {G G' : Guest p}
    (hHost : host.realizes bs rm r0)
    (hLegal : host.legalGuests (G ++ G'))
    (hSound : List.Forall₂ (fun c c' => c'.isSoundReplacementOf c bs) G G') :
    VmSoundReplacement host G G' := by
  simpa using vmSoundReplacement_append hHost hSound hLegal [] (by simp [Host.legalGuests])
