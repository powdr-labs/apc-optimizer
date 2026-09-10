import ApcOptimizer.VmSpec.Basic
import ApcOptimizer.VmSpec.Implementation.Connection
import ApcOptimizer.Utils.Dsl
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-! Fusing two guest chips into one — powdr's `autoprecompiles` starting point: concatenate two
    instruction chips, fix their PCs to line up, and equate their timestamps, so the fused chip is
    one instruction step rather than two unconnected ones (cf. `StepLayout`'s docstring in
    `Legal.lean`).

    `vmSoundReplacement_fuse_cons` shows that *offering* the fused chip alongside `c1`/`c2` (not
    replacing them) is sound: a fused instance can always be unfused back into one `c1` instance
    and one `c2` instance with the *same* assignment, since `fuse` only concatenates lists — no
    renaming, so nothing needs the two circuits' variables to be disjoint, and no `legalGuest`,
    `Host.realizes` or `BusSemantics` is needed either (the reused assignment is definitionally
    still algebraically-satisfying for each half, and `allEffects` distributes exactly over the
    concatenation, for *every* bus, not just stateful ones). The one real cost: unfusing doubles
    the instance count of whatever used the fused chip, which can exceed `host.maxInstances` — that
    is `hBudget`, and it is not free, so it is a genuine hypothesis rather than a derived fact. -/

variable {p : ℕ}

open ApcOptimizer.Spec.Dsl

/-- Concatenate `c1` then `c2`, adding two equations that identify `c1`'s outgoing
    execution-bridge message `(pcOut, tOut)` with `c2`'s incoming one `(pcIn, tIn)` — the pc and
    timestamp expressions each actually sends/receives on the bridge.

    Assumes `c1` and `c2` use disjoint variables (callers must freshen one side first) and that
    `pcOut`/`tOut`/`pcIn`/`tIn` are genuinely `c1`'s send and `c2`'s receive payloads. Neither
    assumption is used by `vmSoundReplacement_fuse_cons` below — they matter for showing `fuse`
    produces a *legal* chip, not for this direction. -/
def Circuit.fuse (c1 c2 : Circuit p) (pcOut tOut pcIn tIn : Expression p) : Circuit p where
  algebraicConstraints :=
    c1.algebraicConstraints ++ c2.algebraicConstraints ++ [pcOut - pcIn, tOut - tIn]
  busInteractions := c1.busInteractions ++ c2.busInteractions

--------- Fusing is a purely structural concatenation ---------

theorem Circuit.fuse_allEffects (c1 c2 : Circuit p) (pcOut tOut pcIn tIn : Expression p)
    (asg : ChipAssignment p) (m : BusMessage p) :
    (c1.fuse c2 pcOut tOut pcIn tIn).allEffects asg m = c1.allEffects asg m + c2.allEffects asg m := by
  simp [Circuit.allEffects, Circuit.fuse, List.filter_append, List.sum_append]

theorem Circuit.fuse_satisfiesAlgebraic_left (c1 c2 : Circuit p) (pcOut tOut pcIn tIn : Expression p)
    {asg : ChipAssignment p} (h : (c1.fuse c2 pcOut tOut pcIn tIn).satisfiesAlgebraic asg) :
    c1.satisfiesAlgebraic asg :=
  fun e he => h e (by simp only [Circuit.fuse, List.mem_append]; tauto)

theorem Circuit.fuse_satisfiesAlgebraic_right (c1 c2 : Circuit p) (pcOut tOut pcIn tIn : Expression p)
    {asg : ChipAssignment p} (h : (c1.fuse c2 pcOut tOut pcIn tIn).satisfiesAlgebraic asg) :
    c2.satisfiesAlgebraic asg :=
  fun e he => h e (by simp only [Circuit.fuse, List.mem_append]; tauto)

/-- Summed over a whole instance list: `fuse`'s net effect on any message is the sum of `c1`'s and
    `c2`'s, since `Circuit.fuse_allEffects` holds instance-by-instance. -/
theorem Circuit.fuse_allEffects_sum (c1 c2 : Circuit p) (pcOut tOut pcIn tIn : Expression p)
    (l : List (ChipAssignment p)) (m : BusMessage p) :
    (l.map (fun asg => (c1.fuse c2 pcOut tOut pcIn tIn).allEffects asg m)).sum =
      (l.map (fun asg => c1.allEffects asg m)).sum + (l.map (fun asg => c2.allEffects asg m)).sum := by
  have heq : (fun asg => (c1.fuse c2 pcOut tOut pcIn tIn).allEffects asg m)
      = (fun asg => c1.allEffects asg m + c2.allEffects asg m) :=
    funext (fun asg => Circuit.fuse_allEffects c1 c2 pcOut tOut pcIn tIn asg m)
  rw [heq]
  induction l with
  | nil => simp
  | cons hd tl ih => simp only [List.map_cons, List.sum_cons, ih]; ring

--------- Soundness of offering the fused chip alongside its ingredients ---------

/-- **Adding a fused chip to a guest list that already has both its ingredients is sound.**
    Every effect the fused chip's presence enables, `c1`/`c2` alone already could: unfuse each
    fused instance's assignment into one `c1` instance and one `c2` instance carrying that exact
    same assignment.

    `hBudget` is the defect, of course: unfusing turns each fused instance into two, so the
    reconstructed run needs room for `instanceCount + (fused-instance count)`, not just
    `instanceCount`.  The `hBudget` assumption is unrealistic, but it could be replaced by tweaking
    the instance count bounds in the post-fusion host. For example, we could prove that any effects
    from the RHS that have short satisfying asignments can be back-translated.
    -/
theorem vmSoundReplacement_fuse_cons {host : Host p} {c1 c2 : Circuit p} {R : Guest p}
    {pcOut tOut pcIn tIn : Expression p}
    (hBudget : ∀ a' : VmAssignment p (⟨host, c1.fuse c2 pcOut tOut pcIn tIn :: c1 :: c2 :: R⟩ : Vm p),
      VmSat _ a' →
      a'.guestAssignments.instanceCount + (a'.guestAssignments 0).length ≤ host.maxInstances) :
    VmSoundReplacement host (c1 :: c2 :: R) (c1.fuse c2 pcOut tOut pcIn tIn :: c1 :: c2 :: R) := by
  rintro e ⟨a', hsat', rfl⟩
  set fL := a'.guestAssignments 0 with hfL
  set c1L := a'.guestAssignments (Fin.succ (0 : Fin (R.length + 2))) with hc1L
  set c2L := a'.guestAssignments (Fin.succ (Fin.succ (0 : Fin (R.length + 1)))) with hc2L
  -- The unfused guest assignment over `c1 :: c2 :: R`: `c1`'s and `c2`'s slots each keep their
  -- original instances and gain one copy of every fused instance (same assignment, reused as-is);
  -- everything else is untouched.
  set gA : GuestAssignment p (c1 :: c2 :: R) :=
    Fin.cons (c1L ++ fL) (Fin.cons (c2L ++ fL) (fun i => a'.guestAssignments i.succ.succ.succ))
    with hgA
  have hg0 : gA 0 = c1L ++ fL := Fin.cons_zero _ _
  have hg1 : gA (Fin.succ (0 : Fin (R.length + 1))) = c2L ++ fL := by
    rw [hgA, Fin.cons_succ, Fin.cons_zero]
  have hgs : ∀ i : Fin R.length,
      gA (Fin.succ (Fin.succ i)) = a'.guestAssignments i.succ.succ.succ := by
    intro i; rw [hgA, Fin.cons_succ, Fin.cons_succ]
  -- Every new instance satisfies its own chip's algebraic constraints: a subset of what its
  -- source instance (`c1`/`c2` directly, or the fused instance it came from) already satisfied.
  have hsatG : ∀ t : Fin (c1 :: c2 :: R).length, ∀ asg ∈ gA t,
      ((c1 :: c2 :: R).get t).satisfiesAlgebraic asg := by
    intro t
    induction t using Fin.cases with
    | zero =>
      rw [hg0]
      intro asg hasg
      rcases List.mem_append.mp hasg with h | h
      · exact hsat'.satisfiesGuest (Fin.succ (0 : Fin (R.length + 2))) asg h
      · exact Circuit.fuse_satisfiesAlgebraic_left c1 c2 pcOut tOut pcIn tIn
          (hsat'.satisfiesGuest 0 asg h)
    | succ t1 =>
      induction t1 using Fin.cases with
      | zero =>
        rw [hg1]
        intro asg hasg
        rcases List.mem_append.mp hasg with h | h
        · exact hsat'.satisfiesGuest (Fin.succ (Fin.succ (0 : Fin (R.length + 1)))) asg h
        · exact Circuit.fuse_satisfiesAlgebraic_right c1 c2 pcOut tOut pcIn tIn
            (hsat'.satisfiesGuest 0 asg h)
      | succ i =>
        rw [hgs i]
        exact hsat'.satisfiesGuest i.succ.succ.succ
  -- The net bus effect is preserved exactly: unfusing is just regrouping the same interaction
  -- list, one `guestNet_cons` peel at a time on each side.
  have hnet : ∀ m : BusMessage p, gA.busEffect m = a'.guestAssignments.busEffect m := by
    intro m
    have e1 := guestNet_cons (c := c1.fuse c2 pcOut tOut pcIn tIn) (R := c1 :: c2 :: R) (l := fL)
      (gA := fun i => a'.guestAssignments i.succ) (gA' := a'.guestAssignments) rfl (fun _ => rfl) m
    have e2 := guestNet_cons (c := c1) (R := c2 :: R) (l := c1L)
      (gA := fun i => a'.guestAssignments i.succ.succ)
      (gA' := fun i => a'.guestAssignments i.succ) rfl (fun _ => rfl) m
    have e3 := guestNet_cons (c := c2) (R := R) (l := c2L)
      (gA := fun i : Fin R.length => a'.guestAssignments i.succ.succ.succ)
      (gA' := fun i => a'.guestAssignments i.succ.succ) rfl (fun _ => rfl) m
    have f1 := guestNet_cons (c := c1) (R := c2 :: R) (l := c1L ++ fL)
      (gA := fun i => gA i.succ) (gA' := gA) hg0 (fun _ => rfl) m
    have f2 := guestNet_cons (c := c2) (R := R) (l := c2L ++ fL)
      (gA := fun i : Fin R.length => a'.guestAssignments i.succ.succ.succ)
      (gA' := fun i => gA i.succ) hg1 hgs m
    have hsplit1 : ((c1L ++ fL).map (fun asg => c1.allEffects asg m)).sum
        = (c1L.map (fun asg => c1.allEffects asg m)).sum + (fL.map (fun asg => c1.allEffects asg m)).sum := by
      simp [List.map_append, List.sum_append]
    have hsplit2 : ((c2L ++ fL).map (fun asg => c2.allEffects asg m)).sum
        = (c2L.map (fun asg => c2.allEffects asg m)).sum + (fL.map (fun asg => c2.allEffects asg m)).sum := by
      simp [List.map_append, List.sum_append]
    have hfuse := Circuit.fuse_allEffects_sum c1 c2 pcOut tOut pcIn tIn fL m
    rw [f1, f2, hsplit1, hsplit2, e1, e2, e3, hfuse]
    ring
  -- The instance count grows by exactly the number of fused instances (one extra `c1` and one
  -- extra `c2` per fused instance replace it) — the only place unfusing actually costs anything.
  have hcount : gA.instanceCount = a'.guestAssignments.instanceCount + fL.length := by
    have e1 := guestInstanceCount_cons (c := c1.fuse c2 pcOut tOut pcIn tIn) (R := c1 :: c2 :: R)
      (l := fL) (gA := fun i => a'.guestAssignments i.succ) (gA' := a'.guestAssignments) rfl
      (fun _ => rfl)
    have e2 := guestInstanceCount_cons (c := c1) (R := c2 :: R) (l := c1L)
      (gA := fun i => a'.guestAssignments i.succ.succ)
      (gA' := fun i => a'.guestAssignments i.succ) rfl (fun _ => rfl)
    have e3 := guestInstanceCount_cons (c := c2) (R := R) (l := c2L)
      (gA := fun i : Fin R.length => a'.guestAssignments i.succ.succ.succ)
      (gA' := fun i => a'.guestAssignments i.succ.succ) rfl (fun _ => rfl)
    have f1 := guestInstanceCount_cons (c := c1) (R := c2 :: R) (l := c1L ++ fL)
      (gA := fun i => gA i.succ) (gA' := gA) hg0 (fun _ => rfl)
    have f2 := guestInstanceCount_cons (c := c2) (R := R) (l := c2L ++ fL)
      (gA := fun i : Fin R.length => a'.guestAssignments i.succ.succ.succ)
      (gA' := fun i => gA i.succ) hg1 hgs
    rw [f1, f2, List.length_append, List.length_append, e1, e2, e3]
    omega
  have hbudget' : gA.instanceCount ≤ host.maxInstances := by
    rw [hcount]; exact hBudget a' hsat'
  refine ⟨⟨gA, a'.hostAssignment⟩, ⟨hsatG, hsat'.satisfiesHost, ?_, ?_⟩, rfl⟩
  · intro m
    show gA.busEffect m + a'.hostAssignment.busEffect m = 0
    rw [hnet m]
    exact hsat'.balances m
  · exact hbudget'

--------- Completeness: offering the fused chip loses nothing ---------

/-- **Offering the fused chip alongside its ingredients loses nothing.** Any run of `c1`/`c2`/`R`
    alone already fits `fused :: c1 :: c2 :: R`: leave the new slot's instance list empty.
    Unconditional — unlike the sound direction, using *zero* fused instances never touches the
    budget. -/
theorem vmCompleteReplacement_fuse_cons {host : Host p} {c1 c2 : Circuit p} {R : Guest p}
    {pcOut tOut pcIn tIn : Expression p} :
    VmCompleteReplacement host (c1 :: c2 :: R) (c1.fuse c2 pcOut tOut pcIn tIn :: c1 :: c2 :: R) := by
  rintro e ⟨a, hsat, rfl⟩
  set gA : GuestAssignment p (c1.fuse c2 pcOut tOut pcIn tIn :: c1 :: c2 :: R) :=
    Fin.cons [] a.guestAssignments with hgA
  have hg0 : gA 0 = [] := Fin.cons_zero _ _
  have hgs : ∀ i : Fin (c1 :: c2 :: R).length, gA i.succ = a.guestAssignments i :=
    fun i => Fin.cons_succ _ _ i
  have hsatG : ∀ t : Fin (c1.fuse c2 pcOut tOut pcIn tIn :: c1 :: c2 :: R).length, ∀ asg ∈ gA t,
      ((c1.fuse c2 pcOut tOut pcIn tIn :: c1 :: c2 :: R).get t).satisfiesAlgebraic asg := by
    intro t
    induction t using Fin.cases with
    | zero => rw [hg0]; simp
    | succ i => rw [hgs i]; exact hsat.satisfiesGuest i
  have hnet : ∀ m : BusMessage p, gA.busEffect m = a.guestAssignments.busEffect m := by
    intro m
    simpa using guestNet_cons (c := c1.fuse c2 pcOut tOut pcIn tIn) (R := c1 :: c2 :: R)
      (l := ([] : List (ChipAssignment p))) (gA := a.guestAssignments) (gA' := gA) hg0 hgs m
  have hcount : gA.instanceCount = a.guestAssignments.instanceCount := by
    simpa using guestInstanceCount_cons (c := c1.fuse c2 pcOut tOut pcIn tIn) (R := c1 :: c2 :: R)
      (l := ([] : List (ChipAssignment p))) (gA := a.guestAssignments) (gA' := gA) hg0 hgs
  refine ⟨⟨gA, a.hostAssignment⟩, ⟨hsatG, hsat.satisfiesHost, ?_, ?_⟩, rfl⟩
  · intro m
    show gA.busEffect m + a.hostAssignment.busEffect m = 0
    rw [hnet m]
    exact hsat.balances m
  · rw [hcount]; exact hsat.withinBudget

--------- Putting both together ---------

/-- **Offering the fused chip alongside its already-available ingredients is a VM-level
    equivalence**, given room in the budget to unfuse (`hBudget`, `vmSoundReplacement_fuse_cons`'s
    hypothesis) — completeness (`vmCompleteReplacement_fuse_cons`) needs nothing extra. -/
theorem vmEquivalent_fuse_cons {host : Host p} {c1 c2 : Circuit p} {R : Guest p}
    {pcOut tOut pcIn tIn : Expression p}
    (hBudget : ∀ a' : VmAssignment p (⟨host, c1.fuse c2 pcOut tOut pcIn tIn :: c1 :: c2 :: R⟩ : Vm p),
      VmSat _ a' →
      a'.guestAssignments.instanceCount + (a'.guestAssignments 0).length ≤ host.maxInstances) :
    VmEquivalent host (c1 :: c2 :: R) (c1.fuse c2 pcOut tOut pcIn tIn :: c1 :: c2 :: R) :=
  ⟨vmSoundReplacement_fuse_cons hBudget, vmCompleteReplacement_fuse_cons⟩
