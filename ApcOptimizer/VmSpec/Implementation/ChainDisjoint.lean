import ApcOptimizer.VmSpec.Implementation.OpenVmChain

set_option autoImplicit false

/-! # Window disjointness

    The combinatorial ingredient `Host.forcesAdmissible` (see `VmSpec/Legal.lean` for the rest of
    the plan). `Chain.arc_position` places each arc *somewhere* on the run's clock; nothing yet
    says two arcs cannot claim the same stretch. Every remaining completeness obligation needs
    that they cannot.

    ## Why it should be true

    `Chain.balanced` makes the arc multiset a balanced digraph on states, so it decomposes into
    edge-disjoint simple cycles. A cycle avoiding the connector is impossible: going round it
    returns the clock to where it started, so its advances sum to `0` in `ZMod p` while being a
    natural in `[1, p)` — the argument `Chain.lean`'s header already records, and the one
    `Chain.time_conn` is built from. The connector is a *single* arc, so it lies in exactly one
    cycle of the decomposition. Hence there is exactly one cycle, and it carries every arc: the run
    is a single closed walk through the connector.

    From there the clock readings along the walk are `t₀`, `t₀ + a₁`, `t₀ + a₁ + a₂`, … — partial
    sums that strictly increase (`advPos`) and stay below `p` (`totalLt`), so they are distinct as
    naturals, and each arc owns the half-open stretch between its own reading and its successor's.

    ## What is actually proved

    `no_balanced_subset` is the core, and it turned out not to need the cycle at all: summing
    `time (dst e) - time (src e)` over a balanced `A` telescopes to `0` in `ZMod p` by the same
    fibrewise-counting step as `Chain.sum_time_src_eq_dst`, while the same sum is an honest natural
    in `[1, p)`. The cyclic structure is what makes the statement *plausible*; the counting is what
    makes it true. It subsumes `Chain.no_cycle`, which is its special case at a stretch of a walk.

    `cycleArcs_eq_univ` then applies it to `univ \ cycleArcs` — balanced as a difference of
    balanced sets, and avoiding the connector, which lies on the cycle. Every arc is therefore
    `C.walk C.conn j` for a unique `j < C.cycleLen`, and the positions are the walk's running
    advances, which are monotone in `j`. Disjointness falls out of that ordering, so no separate
    injectivity-of-`src` lemma is needed. -/

namespace VmChain

variable {p : ℕ} {E M : Type} [Fintype E] [DecidableEq M]

/-- **Lemma A₀ — a balanced set of arcs avoiding the connector is empty.**

    This is the one genuinely missing primitive, and it *subsumes* `Chain.no_cycle`: that lemma is
    the special case where the set is a stretch of `C.walk`.

    Why the generalization is forced. `no_cycle` reasons about `C.walk e`, which follows the
    globally chosen `C.succ`. The cycle that has to be contradicted in Lemma A lives in the
    **complement** of the main walk and follows different successor choices — ones that avoid arcs
    already used — so `C.walk` cannot express it. What is needed is exactly the ability to say
    "this sub-multiset of arcs is still balanced".

    The proof is `no_cycle`'s own arithmetic, re-run on `A`: if `A` is non-empty pick `e ∈ A`;
    balance inside `A` supplies an arc of `A` consuming `C.dst e`; `A` is finite so following those
    repeats, giving a cycle inside `A`; its advances telescope to `0` in `ZMod p` (`advTime`), are
    positive (`advPos`, available since `conn ∉ A`), and total at most `C.total < p`. -/
theorem Chain.no_balanced_subset (C : Chain p E M) (A : Finset E)
    (hconn : C.conn ∉ A)
    (hbal : ∀ m : M, (A.filter fun e => C.src e = m).card
      = (A.filter fun e => C.dst e = m).card) :
    A = ∅ := by
  classical
  by_contra hne
  obtain ⟨e₀, he₀⟩ := Finset.nonempty_of_ne_empty hne
  have hnotconn : ∀ e ∈ A, e ≠ C.conn := fun e he h => hconn (h ▸ he)
  -- Balance inside `A`, read as an equation between two sums, exactly as
  -- `Chain.sum_time_src_eq_dst` reads `C.balanced`.
  have hsum : ∑ e ∈ A, C.time (C.src e) = ∑ e ∈ A, C.time (C.dst e) := by
    set T : Finset M := (A.image C.src) ∪ (A.image C.dst) with hT
    have hsrcT : ∀ e ∈ A, C.src e ∈ T := fun e he =>
      Finset.mem_union_left _ (Finset.mem_image_of_mem _ he)
    have hdstT : ∀ e ∈ A, C.dst e ∈ T := fun e he =>
      Finset.mem_union_right _ (Finset.mem_image_of_mem _ he)
    rw [← Finset.sum_fiberwise_of_maps_to hsrcT, ← Finset.sum_fiberwise_of_maps_to hdstT]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Finset.sum_congr rfl (fun e he => congrArg C.time (Finset.mem_filter.mp he).2),
      Finset.sum_congr rfl (fun e he => congrArg C.time (Finset.mem_filter.mp he).2),
      Finset.sum_const, Finset.sum_const, hbal m]
  -- So `A`'s advances sum to `0` in the field…
  have hcast : ((∑ e ∈ A, C.adv e : ℕ) : ZMod p) = 0 := by
    have hz : ∑ e ∈ A, (C.time (C.dst e) - C.time (C.src e)) = 0 := by
      rw [Finset.sum_sub_distrib, hsum, sub_self]
    rw [Nat.cast_sum, ← hz]
    refine Finset.sum_congr rfl (fun e he => ?_)
    rw [C.advTime e (hnotconn e he)]
    ring
  -- …while being an honest natural in `[1, p)`.
  have hle : (∑ e ∈ A, C.adv e) ≤ C.total :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ A)
  have hpos : 0 < ∑ e ∈ A, C.adv e :=
    lt_of_lt_of_le (C.advPos e₀ (hnotconn e₀ he₀))
      (Finset.single_le_sum (f := C.adv) (fun e _ => Nat.zero_le _) he₀)
  exact absurd (natCast_eq_zero_of_lt (lt_of_le_of_lt hle C.total_lt) hcast) (by omega)

--------- The run's single cycle ---------

/-- The walk from the connector, one step in, is the walk from the connector's successor. -/
theorem Chain.walk_conn_succ (C : Chain p E M) (j : ℕ) :
    C.walk C.conn (j + 1) = C.walk (C.succ C.conn) j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Chain.walk_succ, ih, Chain.walk_succ]

/-- The walk from the connector returns to it. -/
theorem Chain.exists_pos_return (C : Chain p E M) :
    ∃ k, 0 < k ∧ C.walk C.conn k = C.conn := by
  obtain ⟨k, hk⟩ := C.exists_walk_conn (C.succ C.conn)
  exact ⟨k + 1, Nat.succ_pos _, by rw [C.walk_conn_succ]; exact hk⟩

open Classical in
/-- **The length of the run's cycle**: the first return of the connector's walk to the connector. -/
noncomputable def Chain.cycleLen (C : Chain p E M) : ℕ := Nat.find C.exists_pos_return

open Classical in
theorem Chain.cycleLen_pos (C : Chain p E M) : 0 < C.cycleLen :=
  (Nat.find_spec C.exists_pos_return).1

open Classical in
theorem Chain.walk_cycleLen (C : Chain p E M) : C.walk C.conn C.cycleLen = C.conn :=
  (Nat.find_spec C.exists_pos_return).2

open Classical in
theorem Chain.walk_ne_conn (C : Chain p E M) {j : ℕ} (hj : 0 < j) (hlt : j < C.cycleLen) :
    C.walk C.conn j ≠ C.conn := by
  intro h
  exact absurd ⟨hj, h⟩ (Nat.find_min C.exists_pos_return hlt)

/-- The connector's walk visits distinct arcs before returning. -/
theorem Chain.walk_conn_inj (C : Chain p E M) {a b : ℕ} (ha : a < C.cycleLen)
    (hb : b < C.cycleLen) (hab : C.walk C.conn a = C.walk C.conn b) : a = b := by
  have hstep : ∀ j, j < C.cycleLen - 1 → C.walk (C.succ C.conn) j ≠ C.conn := by
    intro j _
    rw [← C.walk_conn_succ]
    exact C.walk_ne_conn (Nat.succ_pos _) (by omega)
  have key := C.walk_inj (C.succ C.conn) (C.cycleLen - 1) hstep
  rcases a with _ | a <;> rcases b with _ | b
  · rfl
  · exact absurd hab.symm (C.walk_ne_conn (Nat.succ_pos _) hb)
  · exact absurd hab (C.walk_ne_conn (Nat.succ_pos _) ha)
  · rw [C.walk_conn_succ, C.walk_conn_succ] at hab
    have := key a (by omega) b (by omega) hab
    omega

open Classical in
/-- The arcs the connector's walk visits before returning. -/
noncomputable def Chain.cycleArcs (C : Chain p E M) : Finset E :=
  (Finset.range C.cycleLen).image (C.walk C.conn)

open Classical in
theorem Chain.mem_cycleArcs (C : Chain p E M) {e : E} :
    e ∈ C.cycleArcs ↔ ∃ j, j < C.cycleLen ∧ C.walk C.conn j = e := by
  simp [Chain.cycleArcs, Finset.mem_image, Finset.mem_range]

open Classical in
theorem Chain.conn_mem_cycleArcs (C : Chain p E M) : C.conn ∈ C.cycleArcs :=
  C.mem_cycleArcs.mpr ⟨0, C.cycleLen_pos, rfl⟩

open Classical in
/-- Counting a property over the cycle's arcs is counting it over the walk's indices. -/
theorem Chain.card_filter_cycleArcs (C : Chain p E M) (P : E → Prop) [DecidablePred P] :
    (C.cycleArcs.filter P).card
      = ((Finset.range C.cycleLen).filter (fun j => P (C.walk C.conn j))).card := by
  have hset : C.cycleArcs.filter P
      = ((Finset.range C.cycleLen).filter (fun j => P (C.walk C.conn j))).image
          (C.walk C.conn) := by
    ext e
    simp only [Chain.cycleArcs, Finset.mem_filter, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨⟨j, hj, rfl⟩, hP⟩; exact ⟨j, ⟨hj, hP⟩, rfl⟩
    · rintro ⟨j, ⟨hj, hP⟩, rfl⟩; exact ⟨⟨j, hj, rfl⟩, hP⟩
  rw [hset]
  refine Finset.card_image_of_injOn (fun a ha b hb hab => ?_)
  exact C.walk_conn_inj (Finset.mem_range.mp (Finset.mem_filter.mp ha).1)
    (Finset.mem_range.mp (Finset.mem_filter.mp hb).1) hab

/-- The cyclic successor on the walk's indices, and its inverse. -/
noncomputable def Chain.cyc (C : Chain p E M) (j : ℕ) : ℕ :=
  if j + 1 = C.cycleLen then 0 else j + 1

noncomputable def Chain.cycInv (C : Chain p E M) (j : ℕ) : ℕ :=
  if j = 0 then C.cycleLen - 1 else j - 1

open Classical in
/-- **The walk's states shift by one under `cyc`**: what an arc produces, its cyclic successor
    consumes — including at the wrap, where `walk conn cycleLen = conn = walk conn 0`. -/
theorem Chain.src_cyc (C : Chain p E M) {j : ℕ} (_hj : j < C.cycleLen) :
    C.src (C.walk C.conn (C.cyc j)) = C.dst (C.walk C.conn j) := by
  have hstep : C.src (C.walk C.conn (j + 1)) = C.dst (C.walk C.conn j) := by
    rw [Chain.walk_succ]; exact C.succ_spec _
  unfold Chain.cyc
  by_cases h : j + 1 = C.cycleLen
  · rw [if_pos h, Chain.walk_zero, ← hstep, h, C.walk_cycleLen]
  · rw [if_neg h, hstep]

open Classical in
theorem Chain.cyc_lt (C : Chain p E M) {j : ℕ} (hj : j < C.cycleLen) : C.cyc j < C.cycleLen := by
  unfold Chain.cyc
  by_cases h : j + 1 = C.cycleLen
  · rw [if_pos h]; exact C.cycleLen_pos
  · rw [if_neg h]; omega

/-- **The cycle's arcs are balanced.** Its source states are its destination states, reindexed by
    the cyclic successor. -/
theorem Chain.cycleArcs_balanced (C : Chain p E M) (m : M) :
    (C.cycleArcs.filter fun e => C.src e = m).card
      = (C.cycleArcs.filter fun e => C.dst e = m).card := by
  classical
  rw [C.card_filter_cycleArcs (fun e => C.src e = m),
    C.card_filter_cycleArcs (fun e => C.dst e = m)]
  have hcycInv_lt : ∀ j, j < C.cycleLen → C.cycInv j < C.cycleLen := by
    intro j hj
    unfold Chain.cycInv
    by_cases h : j = 0
    · rw [if_pos h]; omega
    · rw [if_neg h]; omega
  have hcyc_cycInv : ∀ j, j < C.cycleLen → C.cyc (C.cycInv j) = j := by
    intro j hj
    unfold Chain.cyc Chain.cycInv
    by_cases h : j = 0
    · rw [if_pos h, if_pos (by omega : C.cycleLen - 1 + 1 = C.cycleLen), h]
    · rw [if_neg h, if_neg (by omega : ¬ (j - 1 + 1 = C.cycleLen)),
        Nat.sub_add_cancel (by omega)]
  have hcycInv_cyc : ∀ j, j < C.cycleLen → C.cycInv (C.cyc j) = j := by
    intro j hj
    unfold Chain.cyc Chain.cycInv
    by_cases h : j + 1 = C.cycleLen
    · rw [if_pos h, if_pos rfl]; omega
    · rw [if_neg h, if_neg (by omega : ¬ (j + 1 = 0))]; omega
  refine (Finset.card_bij' (fun j _ => C.cyc j) (fun j _ => C.cycInv j) ?_ ?_ ?_ ?_).symm
  · intro j hj
    dsimp only
    obtain ⟨hjr, hjP⟩ := Finset.mem_filter.mp hj
    have hjr' := Finset.mem_range.mp hjr
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (C.cyc_lt hjr'),
      by rw [C.src_cyc hjr']; exact hjP⟩
  · intro j hj
    dsimp only
    obtain ⟨hjr, hjP⟩ := Finset.mem_filter.mp hj
    have hjr' := Finset.mem_range.mp hjr
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hcycInv_lt j hjr'), ?_⟩
    rw [← C.src_cyc (hcycInv_lt j hjr'), hcyc_cycInv j hjr']
    exact hjP
  · intro j hj
    dsimp only
    exact hcycInv_cyc j (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)
  · intro j hj
    dsimp only
    exact hcyc_cycInv j (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)

open Classical in
/-- **Lemma A — the run is a single cycle: the connector's walk visits every arc.**

    `no_balanced_subset` applied to the complement: `univ` is balanced by `C.balanced`, the cycle's
    arcs are balanced by `cycleArcs_balanced`, so the difference is balanced too — and it avoids
    the connector, which lies on the cycle. -/
theorem Chain.cycleArcs_eq_univ (C : Chain p E M) : C.cycleArcs = Finset.univ := by
  classical
  have hsplit : ∀ (Q : E → Prop) (_ : DecidablePred Q),
      ((Finset.univ \ C.cycleArcs).filter Q).card
        = (Finset.univ.filter Q).card - (C.cycleArcs.filter Q).card := by
    intro Q _
    have he : (Finset.univ \ C.cycleArcs).filter Q
        = (Finset.univ.filter Q) \ (C.cycleArcs.filter Q) := by
      ext e; simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]; tauto
    rw [he, Finset.card_sdiff,
      Finset.inter_eq_left.mpr (Finset.filter_subset_filter _ (Finset.subset_univ _))]
  have hempty : Finset.univ \ C.cycleArcs = ∅ := by
    refine C.no_balanced_subset _ (by simp [C.conn_mem_cycleArcs]) (fun m => ?_)
    rw [hsplit (fun e => C.src e = m) inferInstance, hsplit (fun e => C.dst e = m) inferInstance,
      C.balanced m, C.cycleArcs_balanced m]
  refine Finset.eq_univ_of_forall (fun e => ?_)
  by_contra he
  have : e ∈ Finset.univ \ C.cycleArcs := Finset.mem_sdiff.mpr ⟨Finset.mem_univ e, he⟩
  rw [hempty] at this
  simp at this

open Classical in
/-- Every arc is the connector's walk at a unique index below `cycleLen`. -/
theorem Chain.exists_index (C : Chain p E M) (e : E) :
    ∃ j, j < C.cycleLen ∧ C.walk C.conn j = e :=
  C.mem_cycleArcs.mp (C.cycleArcs_eq_univ ▸ Finset.mem_univ e)

open Classical in
/-- The index at which the connector's walk reaches `e`. -/
noncomputable def Chain.idx (C : Chain p E M) (e : E) : ℕ := (C.exists_index e).choose

open Classical in
theorem Chain.idx_lt (C : Chain p E M) (e : E) : C.idx e < C.cycleLen :=
  (C.exists_index e).choose_spec.1

open Classical in
theorem Chain.walk_idx (C : Chain p E M) (e : E) : C.walk C.conn (C.idx e) = e :=
  (C.exists_index e).choose_spec.2

open Classical in
theorem Chain.idx_inj (C : Chain p E M) {e e' : E} (h : C.idx e = C.idx e') : e = e' := by
  rw [← C.walk_idx e, ← C.walk_idx e', h]

open Classical in
theorem Chain.idx_pos (C : Chain p E M) {e : E} (he : e ≠ C.conn) : 0 < C.idx e := by
  rcases Nat.eq_zero_or_pos (C.idx e) with h | h
  · exact absurd (by rw [← C.walk_idx e, h]; rfl) he
  · exact h

theorem Chain.walkSum_mono (C : Chain p E M) (e : E) {a b : ℕ} (h : a ≤ b) :
    C.walkSum e a ≤ C.walkSum e b := by
  rw [Chain.walkSum, Chain.walkSum]
  exact Finset.sum_le_sum_of_subset
    (fun x hx => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) h))

/-- Before the walk returns, its running advance never exceeds the run's total. -/
theorem Chain.walkSum_le_total (C : Chain p E M) {k : ℕ} (hk : k < C.cycleLen) :
    C.walkSum (C.succ C.conn) k ≤ C.total := by
  have hconn : ∀ j, j < k → C.walk (C.succ C.conn) j ≠ C.conn := by
    intro j hj
    rw [← C.walk_conn_succ]
    exact C.walk_ne_conn (Nat.succ_pos _) (by omega)
  have hinj := C.walk_inj (C.succ C.conn) k hconn
  have h := C.sum_Ico_le_total (C.succ C.conn) (i := 0) (k := k)
    (fun a ha b hb hab => hinj a (Finset.mem_Ico.mp ha).2 b (Finset.mem_Ico.mp hb).2 hab)
  rw [Chain.walkSum, Finset.range_eq_Ico]
  exact h

open Classical in
/-- **The position of an arc**: how far the connector's walk has advanced when it reaches it. -/
noncomputable def Chain.pos (C : Chain p E M) (e : E) : ℕ :=
  C.walkSum (C.succ C.conn) (C.idx e - 1)

open Classical in
theorem Chain.walk_pred_idx (C : Chain p E M) {e : E} (he : e ≠ C.conn) :
    C.walk (C.succ C.conn) (C.idx e - 1) = e := by
  have h1 : C.idx e - 1 + 1 = C.idx e := by have := C.idx_pos he; omega
  rw [← C.walk_conn_succ, h1, C.walk_idx]

open Classical in
theorem Chain.pos_add_adv (C : Chain p E M) {e : E} (he : e ≠ C.conn) :
    C.pos e + C.adv e = C.walkSum (C.succ C.conn) (C.idx e) := by
  have h1 : C.idx e - 1 + 1 = C.idx e := by have := C.idx_pos he; omega
  have h2 : C.walkSum (C.succ C.conn) (C.idx e - 1 + 1)
      = C.walkSum (C.succ C.conn) (C.idx e - 1)
        + C.adv (C.walk (C.succ C.conn) (C.idx e - 1)) := by
    rw [Chain.walkSum, Chain.walkSum, Finset.sum_range_succ]
  rw [Chain.pos]
  conv_rhs => rw [← h1]
  rw [h2, C.walk_pred_idx he]

/-- **Lemma B — every arc owns its own stretch of the clock.** The positional form of Lemma A,
    strengthening `Chain.arc_position` from "each arc has *a* position" to "distinct arcs have
    non-overlapping windows".

    `pos e` is measured forward from the connector's produced state, exactly as `arc_position`
    measures it, so this is a drop-in strengthening rather than a new coordinate system. -/
theorem Chain.exists_disjoint_positions (C : Chain p E M) :
    ∃ pos : E → ℕ,
      (∀ e, e ≠ C.conn →
        pos e + C.adv e ≤ C.total ∧
        C.time (C.src e) = C.time (C.dst C.conn) + (pos e : ZMod p)) ∧
      (∀ e e', e ≠ C.conn → e' ≠ C.conn → e ≠ e' →
        pos e + C.adv e ≤ pos e' ∨ pos e' + C.adv e' ≤ pos e) := by
  classical
  refine ⟨C.pos, fun e he => ⟨?_, ?_⟩, ?_⟩
  · rw [C.pos_add_adv he]
    exact C.walkSum_le_total (C.idx_lt e)
  · have hconn : ∀ j, j < C.idx e - 1 → C.walk (C.succ C.conn) j ≠ C.conn := by
      intro j hj
      rw [← C.walk_conn_succ]
      exact C.walk_ne_conn (Nat.succ_pos _) (by have := C.idx_lt e; omega)
    have h := C.time_walk (C.succ C.conn) (C.idx e - 1) hconn
    rw [C.walk_pred_idx he] at h
    rw [h, C.succ_spec, Chain.pos]
  · intro e e' he he' hne
    have hidx : C.idx e ≠ C.idx e' := fun h => hne (C.idx_inj h)
    rcases Nat.lt_or_ge (C.idx e) (C.idx e') with h | h
    · left
      rw [C.pos_add_adv he]
      exact C.walkSum_mono _ (by omega)
    · right
      rw [C.pos_add_adv he']
      exact C.walkSum_mono _ (by omega)

end VmChain

namespace ApcOptimizer.OpenVM

variable {p : ℕ} {G : Guest p} {maxWindow : ℕ}

variable (gA : GuestAssignment p G) {n : ℕ}
  (S : ∀ x : ((s : Fin G.length) × Fin (gA s).length),
      StepLayout (G.get x.1) (openVmGuestRules defaultBusMap openVmMemBusId)
        ((gA x.1).get x.2) openVmMemAddress maxWindow openVmTimestampBound)
  (iR : Fin n → InputRead p) (ptrReg : Nat)
  (r : ConnectorBoundary p)

/-- **Lemma C — distinct bridge arcs occupy disjoint timestamp windows.**

    `bridge_chain_bound_arc` with the existential pulled out to a function and disjointness added:
    each realized instance — guest chip *and* input-chip alike, since both are arcs of the same
    bridge — starts at an honest natural `1 + T e`, finishes at `1 + T e + adv e` below the
    connector's range-checked final timestamp, and no two half-open windows
    `[1 + T e, 1 + T e + adv e)` overlap.

    This is the form the memory argument consumes. Together with `legalGuest`'s `sendInWindow`
    — a memory send sits at an offset in `[0, tWindow)` — it gives that no two memory sends in a
    run share a timestamp, which with `sendTimesDistinct` (per address) and `memoryInitHostChip`
    is send-uniqueness at `(address, timestamp)`: the invariant every remaining conjunct of
    `Host.forcesAdmissible` rests on. -/
theorem bridge_windows_disjoint_arc {maxInstances maxInputInstances : ℕ}
    (h2 : (-1 : ZMod p) ≠ 1)
    (hbal : ∀ m : BusMessage p, m.1 = 0 →
      gA.busEffect m + (∑ i : Fin n, busStateOf ((iR i).interactions ptrReg 0 1) m)
        + busStateOf (r.interactions 0) m = 0)
    (hIlt : inputStepWindow < maxWindow)
    (hcount : (∑ s : Fin G.length, (gA s).length) ≤ maxInstances)
    (hcountI : n ≤ maxInputInstances)
    (hp : (maxInstances + maxInputInstances + 1) * (maxWindow + 1) < p) :
    ∃ T : BridgeArc gA n → ℕ,
      (∀ e : BridgeArc gA n, e ≠ none →
        openVmBridgeTimestamp (bridgeSrc gA S iR r e) = ((1 + T e : ℕ) : ZMod p) ∧
        1 + T e + bridgeAdv gA S e ≤ r.finalTimestamp.val) ∧
      (∀ e e' : BridgeArc gA n, e ≠ none → e' ≠ none → e ≠ e' →
        T e + bridgeAdv gA S e ≤ T e' ∨ T e' + bridgeAdv gA S e' ≤ T e) := by
  have hppos : 0 < p := Nat.lt_of_le_of_lt (Nat.zero_le _) hp
  haveI : NeZero p := ⟨by omega⟩
  obtain ⟨N, hN⟩ : ∃ N, (∑ e : BridgeArc gA n, bridgeAdv gA S e) = N := ⟨_, rfl⟩
  have htot : N ≤ (maxInstances + maxInputInstances) * maxWindow :=
    hN ▸ bridge_total_le gA S hIlt hcount hcountI
  have h1N : 1 + N < p := by
    have hp' := hp
    rw [show (maxInstances + maxInputInstances + 1) * (maxWindow + 1)
      = (maxInstances + maxInputInstances) * maxWindow
        + (maxInstances + maxInputInstances + maxWindow + 1) from by ring] at hp'
    obtain ⟨M, hM⟩ : ∃ M, (maxInstances + maxInputInstances) * maxWindow = M := ⟨_, rfl⟩
    rw [hM] at hp' htot
    omega
  have hconn : r.finalTimestamp = 1 + ((N : ℕ) : ZMod p) := by
    have h' : r.finalTimestamp = 1 + ((∑ e : BridgeArc gA n, bridgeAdv gA S e : ℕ) : ZMod p) :=
      (bridgeChain gA S iR ptrReg r h2 hbal hIlt hcount hcountI hp).time_conn
    rwa [hN] at h'
  have hval : r.finalTimestamp.val = 1 + N := by
    have hcast : (1 : ZMod p) + ((N : ℕ) : ZMod p) = ((1 + N : ℕ) : ZMod p) := by push_cast; ring
    rw [hconn, hcast, ZMod.val_cast_of_lt h1N]
  obtain ⟨pos, hpos, hdisj⟩ :=
    (bridgeChain gA S iR ptrReg r h2 hbal hIlt hcount hcountI hp).exists_disjoint_positions
  refine ⟨pos, fun e he => ?_, hdisj⟩
  obtain ⟨hT1, hT2⟩ := hpos e he
  have hT1' : pos e + bridgeAdv gA S e ≤ ∑ e : BridgeArc gA n, bridgeAdv gA S e := hT1
  rw [hN] at hT1'
  have hT2' : openVmBridgeTimestamp (bridgeSrc gA S iR r e) = 1 + ((pos e : ℕ) : ZMod p) := hT2
  refine ⟨?_, by rw [hval]; omega⟩
  rw [hT2']
  push_cast
  ring

/-- The guest-only reading of `bridge_windows_disjoint_arc`, in the coordinates
    `StepLayout` states its window in. -/
theorem bridge_windows_disjoint {maxInstances maxInputInstances : ℕ}
    (h2 : (-1 : ZMod p) ≠ 1)
    (hbal : ∀ m : BusMessage p, m.1 = 0 →
      gA.busEffect m + (∑ i : Fin n, busStateOf ((iR i).interactions ptrReg 0 1) m)
        + busStateOf (r.interactions 0) m = 0)
    (hIlt : inputStepWindow < maxWindow)
    (hcount : (∑ s : Fin G.length, (gA s).length) ≤ maxInstances)
    (hcountI : n ≤ maxInputInstances)
    (hp : (maxInstances + maxInputInstances + 1) * (maxWindow + 1) < p) :
    ∃ T : GuestArc gA → ℕ,
      (∀ y : GuestArc gA, (S y).tStart = ((1 + T y : ℕ) : ZMod p) ∧
        1 + T y + (S y).tWindow ≤ r.finalTimestamp.val) ∧
      (∀ y y' : GuestArc gA, y ≠ y' →
        T y + (S y).tWindow ≤ T y' ∨ T y' + (S y').tWindow ≤ T y) := by
  obtain ⟨T, hT, hdisj⟩ :=
    bridge_windows_disjoint_arc gA S iR ptrReg r h2 hbal hIlt hcount hcountI hp
  exact ⟨fun y => T (some (.inl y)), fun y => hT (some (.inl y)) (Option.some_ne_none _),
    fun y y' hne => hdisj (some (.inl y)) (some (.inl y')) (Option.some_ne_none _)
      (Option.some_ne_none _) (by simpa using hne)⟩

end ApcOptimizer.OpenVM
