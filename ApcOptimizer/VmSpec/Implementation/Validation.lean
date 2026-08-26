import ApcOptimizer.VmSpec.Implementation.Counting

set_option autoImplicit false

/-! Sanity checks on `Basic.lean`'s definitions: what `VmSat` and `CanProduce` *don't* see.

    Two things are established here, and both are load-bearing rather than decorative.

    * **Instance order is invisible** (`VmSat.perm_iff`). This is why `CanProduce` need not
      existentially permute a chip type's realized instances.
    * **The guest-chip list is a set** (`canProduce_congr_of_mem`): only which circuits occur
      matters, not their order or multiplicity. `Connection.lean` uses this to replace guest chips
      one at a time — it rotates the list between substitutions, which the theorems here make
      free.

    `VmSoundReplacement` is a preorder (`.refl`/`.trans`) which is what makes that chaining
    possible in the first place.

    One further check that the spec is not vacuous: a VM whose singleton host chips can sit idle
    always has at least the empty run (`canProduce_idle`). Without it, `VmSoundReplacement` — a
    statement about *all* producible effects — would be at risk of holding for want of any. -/

variable {p : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
theorem vmEquivalent_iff {host : Host p} {guestChips guestChips' : Guest p} :
    VmEquivalent host guestChips guestChips' ↔
      ∀ e : VmEffect p, CanProduce ⟨host, guestChips⟩ e ↔ CanProduce ⟨host, guestChips'⟩ e :=
  ⟨fun h e => ⟨h.2 e, h.1 e⟩, fun h => ⟨fun e => (h e).mpr, fun e => (h e).mp⟩⟩

omit [Fact p.Prime] in
/-- The two halves are each other's mirror image: completeness for `G'` *is* soundness the other
    way round. -/
theorem vmCompleteReplacement_iff {host : Host p} {G G' : Guest p} :
    VmCompleteReplacement host G G' ↔ VmSoundReplacement host G' G := Iff.rfl

--------- Sound replacement is a preorder ---------

omit [Fact p.Prime] in
theorem VmSoundReplacement.refl (host : Host p) (G : Guest p) :
    VmSoundReplacement host G G := fun _ h => h

omit [Fact p.Prime] in
/-- Replacements chain: substituting one chip at a time and composing gives the same guarantee as
    substituting them all at once. -/
theorem VmSoundReplacement.trans {host : Host p} {G G' G'' : Guest p}
    (h : VmSoundReplacement host G G') (h' : VmSoundReplacement host G' G'') :
    VmSoundReplacement host G G'' := fun e he => h e (h' e he)

omit [Fact p.Prime] in
theorem VmEquivalent.refl (host : Host p) (G : Guest p) : VmEquivalent host G G :=
  ⟨VmSoundReplacement.refl host G, VmSoundReplacement.refl host G⟩

omit [Fact p.Prime] in
theorem VmEquivalent.symm {host : Host p} {G G' : Guest p}
    (h : VmEquivalent host G G') : VmEquivalent host G' G := ⟨h.2, h.1⟩

omit [Fact p.Prime] in
theorem VmEquivalent.trans {host : Host p} {G G' G'' : Guest p}
    (h : VmEquivalent host G G') (h' : VmEquivalent host G' G'') : VmEquivalent host G G'' :=
  ⟨h.1.trans h'.1, VmSoundReplacement.trans h'.2 h.2⟩

--------- Instance order is invisible ---------

omit [Fact p.Prime] in
/-- VM-satisfiability is assignment-order-independent (unidirectional). -/
theorem VmSat.of_perm {vm : Vm p} {a a' : VmAssignment p vm}
    (hguest : ∀ t, (a'.guestAssignments t).Perm (a.guestAssignments t))
    (hhost : ∀ t, (a'.hostAssignment t).Perm (a.hostAssignment t))
    (hsat : VmSat vm a) : VmSat vm a' := by
  obtain ⟨h1, ⟨h2, h3⟩, h4, h5⟩ := hsat
  have hnet : a'.busEffect = a.busEffect := by
    funext message
    simp only [busEffect_apply, GuestAssignment.busEffect, HostAssignment.busEffect]
    rw [Finset.sum_congr rfl (fun t _ => ((hguest t).map _).sum_eq),
      Finset.sum_congr rfl (fun t _ => ((hhost t).map _).sum_eq)]
  have hcount : a'.guestAssignments.instanceCount = a.guestAssignments.instanceCount :=
    Finset.sum_congr rfl (fun t _ => (hguest t).length_eq)
  exact ⟨fun t asg hasg => h1 t asg ((hguest t).mem_iff.mp hasg),
    ⟨fun t effect hcontrib => h2 t effect ((hhost t).mem_iff.mp hcontrib),
      fun t => (hhost t).length_eq ▸ h3 t⟩,
    fun message => (congrFun hnet message).trans (h4 message),
    hcount.trans_le h5⟩

omit [Fact p.Prime] in
/-- VM-satisfiability is assignment-order-independent (bidirectional). -/
theorem VmSat.perm_iff {vm : Vm p} {a a' : VmAssignment p vm}
    (hguest : ∀ t, (a'.guestAssignments t).Perm (a.guestAssignments t))
    (hhost : ∀ t, (a'.hostAssignment t).Perm (a.hostAssignment t)) :
    VmSat vm a' ↔ VmSat vm a :=
  ⟨fun h => VmSat.of_perm (fun t => (hguest t).symm) (fun t => (hhost t).symm) h,
    fun h => VmSat.of_perm hguest hhost h⟩

-- TODO: prove that the host chip list is a *set* (the guest side is `canProduce_congr_of_mem`)

--------- The guest-chip list is a set ---------

omit [Fact p.Prime] in
/-- Regrouping a sum over `Fin m` by the fibres of `φ` changes nothing. -/
theorem sum_fiber {M : Type} [AddCommMonoid M] {n m : ℕ} (φ : Fin m → Fin n) (X : Fin m → M) :
    (∑ s : Fin n, ∑ t : Fin m, if φ t = s then X t else 0) = ∑ t : Fin m, X t := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun t _ => by simp)

omit [Fact p.Prime] in
/-- If every chip of `guestChips'` also occurs in `guestChips`, then `guestChips` can produce
    every effect `guestChips'` can.

    Each chip type of `guestChips'` is assigned a home in `guestChips` carrying the same circuit,
    and the instances of everything mapped to one home are pooled into that home's instance list.
    Pooling is invisible to `VmSat`: the balance sums regroup by fibre (`sum_fiber`), the
    algebraic constraints are per-instance and the two homes carry the same circuit, and
    `VmAssignment.withinBudget` survives because pooling moves instances around without creating
    any. -/
theorem canProduce_of_subset {host : Host p} {G G' : Guest p}
    (hsub : ∀ c ∈ G', c ∈ G) {e : VmEffect p} (h : CanProduce ⟨host, G'⟩ e) :
    CanProduce ⟨host, G⟩ e := by
  obtain ⟨a', hsat', rfl⟩ := h
  have hex : ∀ t : Fin G'.length, ∃ s : Fin G.length, G.get s = G'.get t := fun t =>
    List.mem_iff_get.mp (hsub _ (List.get_mem G' t))
  choose φ hφ using hex
  set gA : GuestAssignment p G := fun s =>
    (List.ofFn fun t : Fin G'.length => if φ t = s then a'.guestAssignments t else []).flatten
    with hgA
  have hmem : ∀ (s : Fin G.length) (asg : ChipAssignment p), asg ∈ gA s →
      ∃ t : Fin G'.length, φ t = s ∧ asg ∈ a'.guestAssignments t := by
    intro s asg hasg
    rw [hgA] at hasg
    obtain ⟨l, hl, hin⟩ := List.mem_flatten.mp hasg
    obtain ⟨t, rfl⟩ := List.mem_ofFn.mp hl
    by_cases ht : φ t = s
    · exact ⟨t, ht, by simpa [ht] using hin⟩
    · simp [ht] at hin
  have hguest : gA.satisfiesAlgebraic := by
    intro s asg hasg
    obtain ⟨t, ht, hin⟩ := hmem s asg hasg
    subst ht
    rw [hφ t]
    exact hsat'.satisfiesGuest t asg hin
  have hnet : ∀ m : BusMessage p, gA.busEffect m = a'.guestAssignments.busEffect m := by
    intro m
    show (∑ s : Fin G.length, ((gA s).map fun asg => (G.get s).allEffects asg m).sum)
      = ∑ t : Fin G'.length,
          ((a'.guestAssignments t).map fun asg => (G'.get t).allEffects asg m).sum
    have hs : ∀ s : Fin G.length,
        ((gA s).map fun asg => (G.get s).allEffects asg m).sum
          = ∑ t : Fin G'.length, if φ t = s then
              ((a'.guestAssignments t).map fun asg => (G'.get t).allEffects asg m).sum else 0 := by
      intro s
      rw [hgA]
      simp only [List.map_flatten, List.sum_flatten, List.map_ofFn, List.sum_ofFn]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      by_cases ht : φ t = s
      · simp only [Function.comp_apply, if_pos ht]
        rw [← ht, hφ t]
      · simp [ht]
    rw [Finset.sum_congr rfl (fun s _ => hs s)]
    exact sum_fiber φ _
  have hlensum : gA.instanceCount = a'.guestAssignments.instanceCount := by
    show (∑ s : Fin G.length, (gA s).length) = ∑ t : Fin G'.length, (a'.guestAssignments t).length
    have hs : ∀ s : Fin G.length, (gA s).length
        = ∑ t : Fin G'.length, if φ t = s then (a'.guestAssignments t).length else 0 := by
      intro s
      rw [hgA]
      simp only [List.length_flatten, List.map_ofFn, List.sum_ofFn]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      by_cases ht : φ t = s <;> simp [ht]
    rw [Finset.sum_congr rfl (fun s _ => hs s)]
    exact sum_fiber φ _
  refine ⟨⟨gA, a'.hostAssignment⟩,
    ⟨hguest, hsat'.satisfiesHost, fun m => ?_, ?_⟩, rfl⟩
  · rw [busEffect_apply, hnet]
    exact hsat'.balances m
  · show gA.instanceCount ≤ host.maxInstances
    rw [hlensum]
    exact hsat'.withinBudget

omit [Fact p.Prime] in
/-- **The guest-chip list is a set.** Only *which* circuits occur matters: neither their order
    nor how many times each is repeated changes what the VM can produce. -/
theorem canProduce_congr_of_mem {host : Host p} {G G' : Guest p}
    (hmem : {c : Circuit p | c ∈ G} = {c | c ∈ G'}) (e : VmEffect p) :
    CanProduce ⟨host, G⟩ e ↔ CanProduce ⟨host, G'⟩ e :=
  ⟨fun h => canProduce_of_subset (fun c hc => (Set.ext_iff.mp hmem c).mp hc) h,
    fun h => canProduce_of_subset (fun c hc => (Set.ext_iff.mp hmem c).mpr hc) h⟩

omit [Fact p.Prime] in
/-- Two guest-chip lists with the same elements are `VmEquivalent` — reordering them, repeating a
    chip, or dropping a repeat is never an observable change. -/
theorem vmEquivalent_of_mem {host : Host p} {G G' : Guest p}
    (hmem : {c : Circuit p | c ∈ G} = {c | c ∈ G'}) : VmEquivalent host G G' :=
  vmEquivalent_iff.mpr (canProduce_congr_of_mem hmem)

omit [Fact p.Prime] in
/-- Permuting the guest-chip list is not observable. -/
theorem vmEquivalent_of_perm {host : Host p} {G G' : Guest p} (hperm : G.Perm G') :
    VmEquivalent host G G' :=
  vmEquivalent_of_mem (Set.ext fun _ => hperm.mem_iff)

omit [Fact p.Prime] in
/-- Reordering the guest-chip list is a sound replacement, in either direction. -/
theorem VmSoundReplacement.of_perm {host : Host p} {G G' : Guest p} (hperm : G.Perm G') :
    VmSoundReplacement host G G' :=
  (vmEquivalent_of_perm hperm).1

omit [Fact p.Prime] in
/-- **The spec is not vacuous.** Every VM has at least the empty run: no guest instance at all and
    no host instance either, which every `HostChip.instanceBound` allows.

    Worth stating because `VmSoundReplacement` is a statement about *all* producible effects, and
    would hold for free of a `CanProduce` that were empty. It needs no hypothesis on the host: since a chip's instance count is bounded above and
    never forced, leaving one out is always legal, and a chip that must be present cannot be
    written down (`HostChip.instanceBound`). -/
theorem canProduce_idle {host : Host p} {G : Guest p} :
    CanProduce ⟨host, G⟩ ⟨[], host.getOutput 0⟩ := by
  refine ⟨⟨fun _ => [], fun _ => []⟩, ⟨fun t asg hasg => absurd hasg (by simp),
    ⟨fun t effect hmem => absurd hmem (by simp), fun t => by simp⟩, fun m => ?_,
    by simp [GuestAssignment.instanceCount]⟩, ?_⟩
  · show GuestAssignment.busEffect (G := G) (fun _ => []) m
      + HostAssignment.busEffect (host := host) (fun _ => []) m = 0
    simp [GuestAssignment.busEffect, HostAssignment.busEffect]
  · show VmAssignment.effects (vm := ⟨host, G⟩) ⟨fun _ => [], fun _ => []⟩ = _
    simp [VmAssignment.effects, VmAssignment.orderedInputInstances,
      VmAssignment.inputInstances]

