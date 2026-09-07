import ApcOptimizer.VmSpec.Basic
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod

set_option autoImplicit false

/-! Turning a balance equation into "somebody else touched this message".

    The manuscript argues with `mᵢ > 0`/`mᵢ < 0` over the canonical embedding in `ℤ`, but
    balancing is an equation in `ZMod p`: `p` instances that each send the same message sum to `0`
    in the field while summing to `p` in `ℤ`, and the sink is never obliged to receive them.
    `Circuit.countAt` tracks the honest natural number instead, and `VmAssignment.withinBudget`
    keeps it below `p` — which is why the budget has to count bus *interactions*
    (`maxInteractions * host.maxInstances < p`), not instances: one instance may carry the same
    message several times.

    `guestNet_ne_zero_of_uniform` is what the rest of the folder uses: if every guest
    multiplicity at a message is `0` or one fixed nonzero `v`, and some instance actually carries
    it, the guests leave a genuinely nonzero net there. -/

variable {p : ℕ}

/-- `VmAssignment.busEffect` splits into its guest and host halves. A `rfl` lemma: `busEffect` is a
    lambda, so an application does not rewrite without it, and every balancing argument needs to
    take a net apart. -/
theorem busEffect_apply {vm : Vm p} (a : VmAssignment p vm) (message : BusMessage p) :
    a.busEffect message =
      a.guestAssignments.busEffect message + a.hostAssignment.busEffect message := rfl

--------- `allEffects` vs `sideEffects` ---------

/-- On a stateful message the two agree: `Circuit.sideEffects`'s extra `isStateful` filter is
    implied by the message-equality filter both share. This is the bridge between what a sound
    replacement preserves and what `VmSat` balances. -/
theorem allEffects_eq_sideEffects {c : Circuit p} {bs : BusSemantics p}
    {asg : ChipAssignment p} {m : BusMessage p} (hm : bs.isStateful m.1 = true) :
    c.allEffects asg m = c.sideEffects bs asg m := by
  have hpt : ∀ x : BusInteraction (ZMod p),
      decide ((x.busId, x.payload) = m) =
        (bs.isStateful x.busId && decide ((x.busId, x.payload) = m)) := by
    intro x
    by_cases h : (x.busId, x.payload) = m
    · have hbus : x.busId = m.1 := congrArg Prod.fst h
      simp [hbus, hm]
    · simp [h]
  have key : (c.busInteractions.map (fun bi => bi.eval asg)).filter
        (fun x => decide ((x.busId, x.payload) = m)) =
      (c.busInteractions.map (fun bi => bi.eval asg)).filter
        (fun x => bs.isStateful x.busId && decide ((x.busId, x.payload) = m)) :=
    List.filter_congr (fun x _ => hpt x)
  simp only [Circuit.allEffects, Circuit.sideEffects, key]

--------- Finding the instance behind a nonzero net ---------

/-- A message a chip nets a nonzero multiplicity onto is carried by one of its bus interactions,
    with a nonzero multiplicity of its own — the step that turns `VmSat`'s balance into a
    `Circuit.satisfies` acceptance obligation. -/
theorem exists_active_of_allEffects_ne_zero {c : Circuit p} {asg : ChipAssignment p}
    {m : BusMessage p} (h : c.allEffects asg m ≠ 0) :
    ∃ bi ∈ c.busInteractions, ((bi.eval asg).busId, (bi.eval asg).payload) = m ∧
      (bi.eval asg).multiplicity ≠ 0 := by
  by_contra hcon
  refine h (List.sum_eq_zero ?_)
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  obtain ⟨hy1, hy2⟩ := List.mem_filter.mp hy
  obtain ⟨bi, hbi, rfl⟩ := List.mem_map.mp hy1
  by_contra hmult
  exact hcon ⟨bi, hbi, of_decide_eq_true hy2, hmult⟩

/-- A family of instance lists whose contributions sum to something nonzero has an instance whose
    own contribution is nonzero. Both `GuestAssignment.busEffect` and `HostAssignment.busEffect`
    are of this shape. -/
theorem exists_instance_of_sum_ne_zero {α : Type} {n : ℕ} {l : Fin n → List α}
    {f : Fin n → α → ZMod p} (h : (∑ t : Fin n, ((l t).map (f t)).sum) ≠ 0) :
    ∃ (t : Fin n) (x : α), x ∈ l t ∧ f t x ≠ 0 := by
  obtain ⟨t, -, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  by_contra hcon
  refine ht (List.sum_eq_zero ?_)
  intro y hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  by_contra hne
  exact hcon ⟨t, x, hx, hne⟩

theorem exists_instance_of_guestNet_ne_zero {G : Guest p} {gA : GuestAssignment p G}
    {m : BusMessage p} (h : gA.busEffect m ≠ 0) :
    ∃ (t : Fin G.length) (asg : ChipAssignment p),
      asg ∈ gA t ∧ (G.get t).allEffects asg m ≠ 0 :=
  exists_instance_of_sum_ne_zero (l := gA) (f := fun t asg => (G.get t).allEffects asg m) h

theorem exists_instance_of_hostNet_ne_zero {host : Host p} {hA : HostAssignment p host}
    {m : BusMessage p} (h : hA.busEffect m ≠ 0) :
    ∃ (t : Fin host.chips.length) (c : BusState p), c ∈ hA t ∧ c m ≠ 0 :=
  exists_instance_of_sum_ne_zero (l := hA) (f := fun _ effect => effect m) h

/-- Nobody else touching `m` means the host leaves nothing there. -/
theorem hostNet_eq_zero_of_all_zero {host : Host p} {hA : HostAssignment p host}
    {m : BusMessage p} (h : ∀ (t : Fin host.chips.length), ∀ c ∈ hA t, c m = 0) :
    hA.busEffect m = 0 := by
  by_contra hne
  obtain ⟨t, c, hc, hcm⟩ := exists_instance_of_hostNet_ne_zero hne
  exact hcm (h t c hc)

--------- The honest natural-number count ---------

/-- The multiplicities a chip's bus interactions put on `m` — precisely the list
    `Circuit.allEffects` sums. -/
def Circuit.multsAt (c : Circuit p) (asg : ChipAssignment p) (m : BusMessage p) : List (ZMod p) :=
  ((c.busInteractions.map (fun bi => bi.eval asg)).filter
    (fun x => decide ((x.busId, x.payload) = m))).map (fun x => x.multiplicity)

/-- How many of a chip's bus interactions actively carry `m`. The natural number that must be
    kept below `p`: it is what `Circuit.allEffects` degenerates to once the multiplicities at `m`
    are all `0` or one fixed `v`, and unlike the field element it cannot silently wrap. -/
def Circuit.countAt (c : Circuit p) (asg : ChipAssignment p) (m : BusMessage p) : ℕ :=
  (c.multsAt asg m).countP (fun v => decide (v ≠ 0))

/-- Every multiplicity the chip puts on `m` is `0` or `v`. -/
def Circuit.uniformAt (c : Circuit p) (asg : ChipAssignment p) (m : BusMessage p) (v : ZMod p) :
    Prop :=
  ∀ bi ∈ c.busInteractions, ((bi.eval asg).busId, (bi.eval asg).payload) = m →
    (bi.eval asg).multiplicity = 0 ∨ (bi.eval asg).multiplicity = v

theorem countAt_le_length (c : Circuit p) (asg : ChipAssignment p) (m : BusMessage p) :
    c.countAt asg m ≤ c.busInteractions.length := by
  refine le_trans List.countP_le_length ?_
  simp only [Circuit.multsAt, List.length_map]
  exact le_trans (List.length_filter_le _ _) (le_of_eq (List.length_map _))

/-- A list whose entries are all `0` or `v` sums to its count of nonzeros times `v`. -/
theorem sum_eq_countP_mul {l : List (ZMod p)} {v : ZMod p} (h : ∀ x ∈ l, x = 0 ∨ x = v) :
    l.sum = (l.countP (fun x => decide (x ≠ 0)) : ZMod p) * v := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.sum_cons, List.countP_cons, ih (fun x hx => h x (by simp [hx]))]
    rcases h a (by simp) with ha | ha
    · simp [ha]
    · subst ha
      -- `a = v` still leaves two cases: in `ZMod 1` the value `v` is itself `0`.
      by_cases hv : a = 0
      · simp [hv]
      · simp only [ne_eq, hv, not_false_eq_true, decide_true, if_true]
        push_cast
        ring

theorem multsAt_of_uniformAt {c : Circuit p} {asg : ChipAssignment p} {m : BusMessage p}
    {v : ZMod p} (h : c.uniformAt asg m v) : ∀ x ∈ c.multsAt asg m, x = 0 ∨ x = v := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  obtain ⟨hy1, hy2⟩ := List.mem_filter.mp hy
  obtain ⟨bi, hbi, rfl⟩ := List.mem_map.mp hy1
  exact h bi hbi (of_decide_eq_true hy2)

theorem allEffects_eq_countAt_mul {c : Circuit p} {asg : ChipAssignment p} {m : BusMessage p}
    {v : ZMod p} (h : c.uniformAt asg m v) :
    c.allEffects asg m = (c.countAt asg m : ZMod p) * v :=
  sum_eq_countP_mul (multsAt_of_uniformAt h)

theorem countAt_ne_zero {c : Circuit p} {asg : ChipAssignment p} {m : BusMessage p}
    {bi : BusInteraction (Expression p)} (hbi : bi ∈ c.busInteractions)
    (hmsg : ((bi.eval asg).busId, (bi.eval asg).payload) = m)
    (hmult : (bi.eval asg).multiplicity ≠ 0) : c.countAt asg m ≠ 0 := by
  intro h
  have hmem : (bi.eval asg).multiplicity ∈ c.multsAt asg m :=
    List.mem_map_of_mem (List.mem_filter.mpr ⟨List.mem_map_of_mem hbi, by simpa using hmsg⟩)
  have hzero := List.countP_eq_zero.mp h _ hmem
  simp only [decide_eq_true_eq, Bool.not_eq_true, decide_not, Bool.not_eq_false'] at hzero
  exact hmult hzero

/-- The natural-number analogue of `GuestAssignment.busEffect`, on one message. -/
def GuestAssignment.count {G : Guest p} (gA : GuestAssignment p G) (m : BusMessage p) :
    ℕ :=
  ∑ t : Fin G.length, ((gA t).map (fun asg => (G.get t).countAt asg m)).sum

theorem list_sum_map_cast_mul {α : Type} {l : List α} (f : α → ℕ) (v : ZMod p) :
    (l.map (fun a => (f a : ZMod p) * v)).sum = ((l.map f).sum : ℕ) * v := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons]
    push_cast
    ring

theorem guestNet_eq_count_mul {G : Guest p}
    {gA : GuestAssignment p G} {m : BusMessage p} {v : ZMod p}
    (h : ∀ t : Fin G.length, ∀ asg ∈ gA t, (G.get t).uniformAt asg m v) :
    gA.busEffect m = (gA.count m : ZMod p) * v := by
  show (∑ t : Fin G.length, ((gA t).map (fun asg => (G.get t).allEffects asg m)).sum) = _
  rw [GuestAssignment.count]
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [List.map_congr_left (fun asg hasg => allEffects_eq_countAt_mul (h t asg hasg)),
    list_sum_map_cast_mul]
  push_cast
  ring

theorem guestCount_le {G : Guest p}
    {gA : GuestAssignment p G} {m : BusMessage p} {maxInteractions : ℕ}
    (hSize : ∀ c ∈ G, c.busInteractions.length ≤ maxInteractions) :
    gA.count m ≤ gA.instanceCount * maxInteractions := by
  rw [GuestAssignment.count, GuestAssignment.instanceCount, Finset.sum_mul]
  refine Finset.sum_le_sum (fun t _ => ?_)
  refine le_trans (List.sum_le_card_nsmul _ maxInteractions (fun x hx => ?_)) (by simp)
  obtain ⟨asg, -, rfl⟩ := List.mem_map.mp hx
  exact le_trans (countAt_le_length _ _ _) (hSize _ (List.get_mem G t))

/-- If every guest multiplicity at `m` is `0` or a fixed nonzero `v`, and at least one instance
    actually carries `m`, then the guests leave a genuinely nonzero net there. The honest
    natural-number count stays below `p`, so it cannot wrap to zero. -/
theorem guestNet_ne_zero_of_uniform [Fact p.Prime] {host : Host p} {G : Guest p}
    {maxInteractions : ℕ}
    {a : VmAssignment p ⟨host, G⟩} {m : BusMessage p} {v : ZMod p} (hsat : VmSat ⟨host, G⟩ a)
    (hSize : ∀ c ∈ G, c.busInteractions.length ≤ maxInteractions)
    (hBudget : maxInteractions * host.maxInstances < p) (hv : v ≠ 0)
    (huni : ∀ t : Fin G.length, ∀ asg ∈ a.guestAssignments t, (G.get t).uniformAt asg m v)
    {t : Fin G.length} {asg : ChipAssignment p} (hasg : asg ∈ a.guestAssignments t)
    {bi : BusInteraction (Expression p)} (hbi : bi ∈ (G.get t).busInteractions)
    (hmsg : ((bi.eval asg).busId, (bi.eval asg).payload) = m)
    (hmult : (bi.eval asg).multiplicity ≠ 0) :
    a.guestAssignments.busEffect m ≠ 0 := by
  have hpos : a.guestAssignments.count m ≠ 0 := by
    intro h
    refine countAt_ne_zero hbi hmsg hmult ?_
    have hz := Finset.sum_eq_zero_iff.mp h t (Finset.mem_univ t)
    exact List.sum_eq_zero_iff.mp hz _ (List.mem_map_of_mem hasg)
  have hlt : a.guestAssignments.count m < p :=
    lt_of_le_of_lt
      (le_trans (guestCount_le hSize) (Nat.mul_le_mul_right maxInteractions hsat.withinBudget))
      (by rwa [Nat.mul_comm])
  rw [guestNet_eq_count_mul huni]
  refine mul_ne_zero ?_ hv
  have hne : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  intro hcast
  refine hpos ?_
  have := ZMod.val_cast_of_lt hlt
  rw [hcast, ZMod.val_zero] at this
  exact this.symm

/-- Like `guestNet_ne_zero_of_uniform`, but absorbs one extra uniform contribution `e` — a
    singleton host chip's own touch of `m`, which is `0` or the same `v` the guests carry. The
    extra unit of budget headroom (`+ 1 < p` rather than `< p`) is not decoration: without it,
    exactly `p - 1` guest receives plus the one host receive sum to `p ≡ 0`, and the pile *would*
    balance. -/
theorem guestNet_add_ne_zero_of_uniform [Fact p.Prime] {host : Host p} {G : Guest p}
    {maxInteractions : ℕ}
    {a : VmAssignment p ⟨host, G⟩} {m : BusMessage p} {v : ZMod p} (hsat : VmSat ⟨host, G⟩ a)
    (hSize : ∀ c ∈ G, c.busInteractions.length ≤ maxInteractions)
    (hBudget : maxInteractions * host.maxInstances + 1 < p) (hv : v ≠ 0)
    (huni : ∀ t : Fin G.length, ∀ asg ∈ a.guestAssignments t, (G.get t).uniformAt asg m v)
    {t : Fin G.length} {asg : ChipAssignment p} (hasg : asg ∈ a.guestAssignments t)
    {bi : BusInteraction (Expression p)} (hbi : bi ∈ (G.get t).busInteractions)
    (hmsg : ((bi.eval asg).busId, (bi.eval asg).payload) = m)
    (hmult : (bi.eval asg).multiplicity ≠ 0)
    {e : ZMod p} (he : e = 0 ∨ e = v) :
    a.guestAssignments.busEffect m + e ≠ 0 := by
  have hcount_le : a.guestAssignments.count m ≤ host.maxInstances * maxInteractions :=
    le_trans (guestCount_le hSize) (Nat.mul_le_mul_right maxInteractions hsat.withinBudget)
  have hlt : a.guestAssignments.count m + 1 < p := by
    have hcomm : host.maxInstances * maxInteractions = maxInteractions * host.maxInstances :=
      Nat.mul_comm _ _
    omega
  have hne : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [guestNet_eq_count_mul huni]
  rcases he with he | he
  · subst he
    rw [add_zero]
    refine mul_ne_zero ?_ hv
    have hpos : a.guestAssignments.count m ≠ 0 := by
      intro h
      refine countAt_ne_zero hbi hmsg hmult ?_
      have hz := Finset.sum_eq_zero_iff.mp h t (Finset.mem_univ t)
      exact List.sum_eq_zero_iff.mp hz _ (List.mem_map_of_mem hasg)
    intro hcast
    refine hpos ?_
    have hval := ZMod.val_cast_of_lt (lt_of_le_of_lt (Nat.le_succ _) hlt)
    rw [hcast, ZMod.val_zero] at hval
    exact hval.symm
  · subst he
    rw [← add_one_mul]
    refine mul_ne_zero ?_ hv
    have hcast_eq : (a.guestAssignments.count m : ZMod p) + 1
        = ((a.guestAssignments.count m + 1 : ℕ) : ZMod p) := by push_cast; ring
    rw [hcast_eq]
    intro hcast
    have hval := ZMod.val_cast_of_lt hlt
    rw [hcast, ZMod.val_zero] at hval
    omega
