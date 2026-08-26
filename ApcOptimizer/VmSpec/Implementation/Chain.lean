import ApcOptimizer.VmSpec.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Sigma

set_option autoImplicit false

/-! **Ordering a run's clock by walking the execution bridge.** Nothing here is audited, and
    nothing here mentions a `Circuit`, a `Host` or a bus: it is the combinatorics the rank-window
    argument runs on, stated abstractly so that the OpenVM plumbing can be kept separate.

    A `Chain` is a finite multiset of *arcs*, each consuming one state and producing another, in
    which every state is produced exactly as often as it is consumed. One arc — the `conn`ector —
    is distinguished; all the others advance a `ZMod p`-valued clock by a positive natural number,
    and the advances total less than `p`.

    From that alone: every arc lies on a directed path that ends at the connector, and the clock
    reading it consumes is the connector's own minus the advances along that path. Since the
    advances are naturals summing below `p`, that is an honest ordering rather than a statement
    about field elements, which is what lets `openVmHost_ordersRanks` turn one range-checked
    boundary timestamp into a bound on every timestamp in the run.

    The only thing that rules out a run whose arcs form a cycle avoiding the connector is the
    advance total: going once around such a cycle returns the clock to where it started, so the
    advances sum to `0` in `ZMod p` while being a natural in `[1, p)`. -/

namespace VmChain

variable {p : ℕ} {E M : Type} [Fintype E] [DecidableEq M]

open Classical in
/-- A balanced multiset of clock-advancing arcs with one distinguished arc.

    `E` indexes the arcs and `M` the states they carry (for OpenVM: guest instances plus the
    connector, and execution-bridge messages). `src e` is the state arc `e` consumes, `dst e` the
    state it produces. -/
structure Chain (p : ℕ) (E M : Type) [Fintype E] [DecidableEq M] where
  /-- The state this arc consumes. -/
  src : E → M
  /-- The state this arc produces. -/
  dst : E → M
  /-- The clock reading a state carries. -/
  time : M → ZMod p
  /-- The distinguished arc — the one that need not advance the clock. -/
  conn : E
  /-- How far each arc advances the clock. -/
  adv : E → ℕ
  /-- Every state is consumed exactly as often as it is produced. -/
  balanced : ∀ m : M, (Finset.univ.filter fun e => src e = m).card
    = (Finset.univ.filter fun e => dst e = m).card
  /-- Every arc but the connector advances the clock. -/
  advPos : ∀ e, e ≠ conn → 0 < adv e
  /-- …by exactly `adv e`, as a natural number: no field wraparound can spoof this. -/
  advTime : ∀ e, e ≠ conn → time (dst e) = time (src e) + (adv e : ZMod p)
  /-- The connector's own advance is not counted. -/
  advConn : adv conn = 0
  /-- The whole run advances the clock by less than `p` — the anti-wraparound budget. -/
  totalLt : (∑ e, adv e) < p

variable {C : Chain p E M}

/-- How far the whole run advances the clock. -/
def Chain.total (C : Chain p E M) : ℕ := ∑ e, C.adv e

theorem Chain.total_lt (C : Chain p E M) : C.total < p := C.totalLt

theorem Chain.p_pos (C : Chain p E M) : 0 < p := Nat.lt_of_le_of_lt (Nat.zero_le _) C.totalLt

/-- A natural below `p` that casts to `0` is `0` — the shape every wraparound-freedom step here
    takes. -/
theorem natCast_eq_zero_of_lt {n : ℕ} (hlt : n < p) (h : (n : ZMod p) = 0) : n = 0 := by
  haveI : NeZero p := ⟨by omega⟩
  have hval := ZMod.val_cast_of_lt hlt
  rw [h, ZMod.val_zero] at hval
  exact hval.symm

--------- The successor arc ---------

/-- Balance gives every arc a successor: something consumes what it produced. -/
theorem Chain.exists_succ (C : Chain p E M) (e : E) : ∃ e', C.src e' = C.dst e := by
  have hpos : 0 < (Finset.univ.filter fun x => C.dst x = C.dst e).card :=
    Finset.card_pos.mpr ⟨e, by simp⟩
  rw [← C.balanced] at hpos
  obtain ⟨e', he'⟩ := Finset.card_pos.mp hpos
  exact ⟨e', (Finset.mem_filter.mp he').2⟩

open Classical in
/-- Some arc consuming what `e` produced. Which one is irrelevant — the walk below never needs it
    to be canonical, only to exist. -/
noncomputable def Chain.succ (C : Chain p E M) (e : E) : E := (C.exists_succ e).choose

theorem Chain.succ_spec (C : Chain p E M) (e : E) : C.src (C.succ e) = C.dst e :=
  (C.exists_succ e).choose_spec

/-- Following successors from `e`. -/
noncomputable def Chain.walk (C : Chain p E M) (e : E) : ℕ → E
  | 0 => e
  | k + 1 => C.succ (C.walk e k)

theorem Chain.walk_zero (C : Chain p E M) (e : E) : C.walk e 0 = e := rfl

theorem Chain.walk_succ (C : Chain p E M) (e : E) (k : ℕ) :
    C.walk e (k + 1) = C.succ (C.walk e k) := rfl

/-- The advances accumulated over the first `k` steps of the walk. -/
noncomputable def Chain.walkSum (C : Chain p E M) (e : E) (k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range k, C.adv (C.walk e j)

/-- **The clock reading after `k` steps**, provided the connector has not been reached — which is
    the whole point of excluding it, since the connector is the one arc that need not advance. -/
theorem Chain.time_walk (C : Chain p E M) (e : E) :
    ∀ k, (∀ j < k, C.walk e j ≠ C.conn) →
      C.time (C.src (C.walk e k)) = C.time (C.src e) + (C.walkSum e k : ZMod p) := by
  intro k
  induction k with
  | zero => simp [Chain.walkSum, Chain.walk_zero]
  | succ k ih =>
    intro h
    have hk : C.walk e k ≠ C.conn := h k (by omega)
    have hprev := ih (fun j hj => h j (by omega))
    rw [Chain.walk_succ, C.succ_spec, C.advTime _ hk, hprev]
    simp only [Chain.walkSum, Finset.sum_range_succ]
    push_cast
    rw [add_assoc]

/-- The advances over the arcs `i, …, k-1` of the walk. -/
theorem Chain.walkSum_add (C : Chain p E M) (e : E) {i k : ℕ} (hik : i ≤ k) :
    C.walkSum e i + ∑ j ∈ Finset.Ico i k, C.adv (C.walk e j) = C.walkSum e k := by
  simp only [Chain.walkSum]
  exact Finset.sum_range_add_sum_Ico _ hik

/-- A stretch of the walk with distinct arcs, none of them the connector, advances the clock by at
    most the run's total. -/
theorem Chain.sum_Ico_le_total (C : Chain p E M) (e : E) {i k : ℕ}
    (hinj : ∀ a ∈ Finset.Ico i k, ∀ b ∈ Finset.Ico i k, C.walk e a = C.walk e b → a = b) :
    ∑ j ∈ Finset.Ico i k, C.adv (C.walk e j) ≤ C.total := by
  classical
  rw [← Finset.sum_image (f := C.adv) (g := C.walk e) hinj]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

/-- **No cycle avoids the connector.** A stretch of the walk returning to where it started would
    advance the clock by a natural in `[1, p)` while returning it to its original value. -/
theorem Chain.no_cycle (C : Chain p E M) (e : E) {i k : ℕ} (hik : i < k)
    (hconn : ∀ j < k, C.walk e j ≠ C.conn)
    (hinj : ∀ a < k, ∀ b < k, C.walk e a = C.walk e b → a = b)
    (hrepeat : C.walk e i = C.walk e k) : False := by
  set S : ℕ := ∑ j ∈ Finset.Ico i k, C.adv (C.walk e j) with hS
  have hsplit := C.walkSum_add e (le_of_lt hik)
  have htk := C.time_walk e k hconn
  have hti := C.time_walk e i (fun j hj => hconn j (by omega))
  have hzero : (S : ZMod p) = 0 := by
    have : C.time (C.src e) + (C.walkSum e i : ZMod p) + (S : ZMod p)
        = C.time (C.src e) + (C.walkSum e k : ZMod p) := by
      rw [add_assoc, ← Nat.cast_add, hsplit]
    rw [← hti, ← htk, hrepeat] at this
    exact add_eq_left.mp this
  have hle : S ≤ C.total :=
    C.sum_Ico_le_total e (fun a ha b hb hab =>
      hinj a (Finset.mem_Ico.mp ha).2 b (Finset.mem_Ico.mp hb).2 hab)
  have hpos : 0 < S := by
    refine lt_of_lt_of_le (C.advPos (C.walk e i) (hconn i hik)) ?_
    exact Finset.single_le_sum (f := fun j => C.adv (C.walk e j)) (fun j _ => Nat.zero_le _)
      (Finset.mem_Ico.mpr ⟨le_refl i, hik⟩)
  exact absurd (natCast_eq_zero_of_lt (lt_of_le_of_lt hle C.total_lt) hzero) (by omega)

/-- The walk is injective until it reaches the connector. -/
theorem Chain.walk_inj (C : Chain p E M) (e : E) :
    ∀ k, (∀ j < k, C.walk e j ≠ C.conn) → ∀ a < k, ∀ b < k, C.walk e a = C.walk e b → a = b := by
  intro k
  induction k with
  | zero => intro _ a ha; omega
  | succ k ih =>
    intro hconn a ha b hb hab
    have ihk := ih (fun j hj => hconn j (by omega))
    rcases Nat.lt_or_ge a k with hak | hak
    · rcases Nat.lt_or_ge b k with hbk | hbk
      · exact ihk a hak b hbk hab
      · have hbk' : b = k := by omega
        subst hbk'
        exact (C.no_cycle e hak (fun j hj => hconn j (by omega)) ihk hab).elim
    · have hak' : a = k := by omega
      subst hak'
      rcases Nat.lt_or_ge b a with hba | hba
      · exact (C.no_cycle e hba (fun j hj => hconn j (by omega)) ihk hab.symm).elim
      · omega

/-- The walk reaches the connector: a walk that never did would be an injection from an
    unbounded index set into the finitely many arcs. -/
theorem Chain.exists_walk_conn (C : Chain p E M) (e : E) : ∃ k, C.walk e k = C.conn := by
  by_contra hcon
  have hinj := C.walk_inj e (Fintype.card E + 1) (fun j _ hj => hcon ⟨j, hj⟩)
  have : Function.Injective (fun j : Fin (Fintype.card E + 1) => C.walk e j) := by
    intro a b hab
    exact Fin.ext (hinj a a.isLt b b.isLt hab)
  have := Fintype.card_le_of_injective _ this
  simp at this

/-- **Every arc sits at a known distance before the connector.** The clock reading the arc
    consumes, plus the advances along the path from it to the connector, is the reading the
    connector consumes — and that path's advances are a natural number between the arc's own
    advance and the run's total.

    This is the whole output of the file: it converts "somewhere in a balanced run" into a
    position on a single line of length `C.total`. -/
theorem Chain.exists_prefix (C : Chain p E M) (e : E) (he : e ≠ C.conn) :
    ∃ S : ℕ, C.adv e ≤ S ∧ S ≤ C.total ∧
      C.time (C.src C.conn) = C.time (C.src e) + (S : ZMod p) := by
  classical
  have hex := C.exists_walk_conn e
  set k := Nat.find hex with hk
  have hfind : C.walk e k = C.conn := Nat.find_spec hex
  have hbefore : ∀ j < k, C.walk e j ≠ C.conn := fun j hj => Nat.find_min hex hj
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h; · exact absurd (h0 ▸ hfind) (by simpa using he)
    exact h
  refine ⟨C.walkSum e k, ?_, ?_, ?_⟩
  · have h0 : C.adv (C.walk e 0) ≤ C.walkSum e k :=
      Finset.single_le_sum (f := fun j => C.adv (C.walk e j)) (fun j _ => Nat.zero_le _)
        (Finset.mem_range.mpr hkpos)
    rwa [Chain.walk_zero] at h0
  · rw [Chain.walkSum, Finset.range_eq_Ico]
    exact C.sum_Ico_le_total e (fun a ha b hb hab =>
      C.walk_inj e k hbefore a (Finset.mem_Ico.mp ha).2 b (Finset.mem_Ico.mp hb).2 hab)
  · rw [← hfind]; exact C.time_walk e k hbefore

--------- The connector closes the loop ---------

/-- Balance, read as an equation between two sums over the arcs: what they consume and what they
    produce carry the same total clock reading. -/
theorem Chain.sum_time_src_eq_dst (C : Chain p E M) :
    ∑ e, C.time (C.src e) = ∑ e, C.time (C.dst e) := by
  classical
  set T : Finset M := (Finset.univ.image C.src) ∪ (Finset.univ.image C.dst) with hT
  have hsrcT : ∀ e ∈ (Finset.univ : Finset E), C.src e ∈ T := fun e _ =>
    Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ e))
  have hdstT : ∀ e ∈ (Finset.univ : Finset E), C.dst e ∈ T := fun e _ =>
    Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ e))
  rw [← Finset.sum_fiberwise_of_maps_to hsrcT, ← Finset.sum_fiberwise_of_maps_to hdstT]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Finset.sum_congr rfl (fun e he => congrArg C.time (Finset.mem_filter.mp he).2),
    Finset.sum_congr rfl (fun e he => congrArg C.time (Finset.mem_filter.mp he).2),
    Finset.sum_const, Finset.sum_const, C.balanced m]

/-- **The connector's own reading is the whole run's advance.** Its produced state starts the
    clock; its consumed state is where the run left it. -/
theorem Chain.time_conn (C : Chain p E M) :
    C.time (C.src C.conn) = C.time (C.dst C.conn) + (C.total : ZMod p) := by
  classical
  have hdiff : ∑ e, (C.time (C.dst e) - C.time (C.src e)) = 0 := by
    rw [Finset.sum_sub_distrib, C.sum_time_src_eq_dst, sub_self]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ C.conn)] at hdiff
  have hstep : ∀ e ∈ Finset.univ.erase C.conn,
      C.time (C.dst e) - C.time (C.src e) = (C.adv e : ZMod p) := by
    intro e he
    rw [C.advTime e (Finset.mem_erase.mp he).1]
    ring
  have hrest : ∑ e ∈ Finset.univ.erase C.conn, (C.time (C.dst e) - C.time (C.src e))
      = (C.total : ZMod p) := by
    rw [Finset.sum_congr rfl hstep, ← Nat.cast_sum, Chain.total,
      ← Finset.add_sum_erase _ _ (Finset.mem_univ C.conn), C.advConn, Nat.zero_add]
  rw [hrest] at hdiff
  refine (sub_eq_zero.mp ?_).symm
  rw [← hdiff]
  ring

/-- **Where an arc sits on the line from the connector.** Combining `Chain.exists_prefix` with
    `Chain.time_conn`: the clock reading an arc consumes is the connector's starting reading plus an
    honest natural `T`, and `T` plus the arc's own advance still fits inside the run's total.

    This is the form the caller wants — everything measured forward from the start, so that one
    range check on the connector bounds the whole run. -/
theorem Chain.arc_position (C : Chain p E M) (e : E) (he : e ≠ C.conn) :
    ∃ T : ℕ, T + C.adv e ≤ C.total ∧
      C.time (C.src e) = C.time (C.dst C.conn) + (T : ZMod p) := by
  obtain ⟨Sm, h1, h2, h3⟩ := C.exists_prefix e he
  refine ⟨C.total - Sm, by omega, ?_⟩
  have hcancel : C.time (C.dst C.conn) + ((C.total - Sm : ℕ) : ZMod p) + (Sm : ZMod p)
      = C.time (C.src e) + (Sm : ZMod p) := by
    rw [← h3, C.time_conn, add_assoc, ← Nat.cast_add, Nat.sub_add_cancel h2]
  exact (add_right_cancel hcancel).symm

/-! **The chain is a simple cycle: no two non-connector arcs ever share a state.**

    `Chain.arc_position` places every arc at a *distance* from the connector; it says nothing about
    whether two arcs can land at the same *state*. They cannot — `Chain.src_injOn` below is the
    proof. This is a purely combinatorial fact about `balanced`/`no_cycle`, unrelated to how OpenVM
    instantiates a `Chain`.

    The argument: a state with two producers (or two consumers) forces the graph to branch, and a
    branch anywhere has to reconnect somewhere — closing a cycle that avoids the connector. That is
    exactly what `Chain.no_cycle` already rules out. `no_selfBalanced_of_not_mem_conn` makes this
    precise for an arbitrary subset of arcs (`Chain.SelfBalanced`), not just the canonical walk:
    any nonempty self-balanced set of arcs that avoids the connector is impossible. Applying it to
    the complement of the connector's own walk (`Chain.cycleSet`, self-balanced by
    `cycleSet_selfBalanced` via a cyclic index shift) forces that walk to cover every arc
    (`cycleSet_eq_univ`) — so distances-from-connector, hence states, are injective on it. -/

theorem mod_pred_succ (n i : ℕ) (hn : 0 < n) (hi : i < n) :
    ((i + n - 1) % n + 1) % n = i := by
  rcases Nat.eq_zero_or_pos i with hi0 | hi0
  · subst hi0
    have h1 : 0 + n - 1 = n - 1 := by omega
    have h2 : n - 1 < n := by omega
    rw [h1, Nat.mod_eq_of_lt h2]
    have h3 : n - 1 + 1 = n := by omega
    rw [h3, Nat.mod_self]
  · have h1 : i + n - 1 = (i - 1) + n := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : i - 1 < n)]
    have h2 : i - 1 + 1 = i := by omega
    rw [h2, Nat.mod_eq_of_lt hi]

theorem mod_succ_pred (n i : ℕ) (hn : 0 < n) (hi : i < n) :
    ((i + 1) % n + n - 1) % n = i := by
  rcases Nat.eq_zero_or_pos (i + 1 - n) with h | h
  · have hlt : i + 1 < n ∨ i + 1 = n := by omega
    rcases hlt with hlt | heq
    · rw [Nat.mod_eq_of_lt hlt]
      have : i + 1 + n - 1 = i + n := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
    · rw [heq, Nat.mod_self]
      have h1 : 0 + n - 1 = n - 1 := by omega
      rw [h1, Nat.mod_eq_of_lt (by omega : n - 1 < n)]
      omega
  · omega

/-- A finite set of arcs that is balanced *on its own*: within `S`, every state is produced
    exactly as often as it is consumed. `no_selfBalanced_of_not_mem_conn` is the fact this exists
    to state — a nonempty one avoiding the connector is impossible. -/
def Chain.SelfBalanced (C : Chain p E M) (S : Finset E) : Prop :=
  ∀ m : M, (S.filter fun e => C.src e = m).card = (S.filter fun e => C.dst e = m).card

/-- **Any nonempty self-balanced set of arcs avoiding the connector is impossible.** Walking
    within `S` (a valid move: balance gives every state in `S` a producer *and* a consumer inside
    `S`, mirroring `Chain.exists_succ`) never runs out of room, since `S` is finite — so it must
    repeat an arc. That repeat is a cycle avoiding the connector, forbidden by the same
    positive-advance/wraparound argument `Chain.no_cycle` runs, adapted here to a walk that need
    not be `Chain.walk`'s own (that one is anchored to the connector; this one has none to anchor
    to). -/
theorem no_selfBalanced_of_not_mem_conn {S : Finset E} (hconn : C.conn ∉ S)
    (hbal : C.SelfBalanced S) (hne : S.Nonempty) : False := by
  classical
  obtain ⟨e0, he0⟩ := hne
  have hsucc_ex : ∀ e ∈ S, ∃ e' ∈ S, C.src e' = C.dst e := by
    intro e he
    have h1 : e ∈ S.filter (fun x => C.dst x = C.dst e) := Finset.mem_filter.mpr ⟨he, rfl⟩
    have h2 : 0 < (S.filter (fun x => C.dst x = C.dst e)).card := Finset.card_pos.mpr ⟨e, h1⟩
    rw [← hbal (C.dst e)] at h2
    obtain ⟨e', he'⟩ := Finset.card_pos.mp h2
    obtain ⟨he'S, he'eq⟩ := Finset.mem_filter.mp he'
    exact ⟨e', he'S, he'eq⟩
  choose! succS hsuccS_mem hsuccS_spec using hsucc_ex
  have hsuccS_ne_conn : ∀ e ∈ S, succS e ≠ C.conn := fun e he h => hconn (h ▸ hsuccS_mem e he)
  let walkS : ℕ → E := fun k => Nat.rec e0 (fun _ e => succS e) k
  have hwalkS0 : walkS 0 = e0 := rfl
  have hwalkS_succ : ∀ k, walkS (k+1) = succS (walkS k) := fun k => rfl
  have hwalkS_mem : ∀ k, walkS k ∈ S := by
    intro k; induction k with
    | zero => exact hwalkS0 ▸ he0
    | succ k ih => rw [hwalkS_succ]; exact hsuccS_mem _ ih
  have hwalkS_ne_conn : ∀ k, walkS k ≠ C.conn := fun k h => hconn (h ▸ hwalkS_mem k)
  -- The first point of non-injectivity.
  have hex : ∃ k : ℕ, ¬ Function.Injective (fun i : Fin (k+1) => walkS i) := by
    refine ⟨Fintype.card E, fun hinj => ?_⟩
    have := Fintype.card_le_of_injective _ hinj
    simp only [Fintype.card_fin] at this
    omega
  set k0 := Nat.find hex with hk0
  have hk0spec : ¬ Function.Injective (fun i : Fin (k0+1) => walkS i) := Nat.find_spec hex
  have hk0min : ∀ k, k < k0 → Function.Injective (fun i : Fin (k+1) => walkS i) :=
    fun k hk => not_not.mp (Nat.find_min hex hk)
  -- walkS is injective on [0,k0); walkS k0 must equal exactly one earlier value.
  have hinj0 : ∀ a < k0, ∀ b < k0, walkS a = walkS b → a = b := by
    intro a ha b hb hab
    have hklt : max a b < k0 := by omega
    have hinjk := hk0min (max a b) hklt
    have heq : (fun i : Fin (max a b + 1) => walkS i) ⟨a, by omega⟩
        = (fun i : Fin (max a b + 1) => walkS i) ⟨b, by omega⟩ := hab
    exact congrArg Fin.val (hinjk heq)
  have hex_repeat : ∃ a < k0, walkS a = walkS k0 := by
    by_contra hc
    push Not at hc
    apply hk0spec
    intro x y hxy0
    have hxy : walkS (x : ℕ) = walkS (y : ℕ) := hxy0
    by_cases hx : (x : ℕ) = k0
    · by_cases hy : (y : ℕ) = k0
      · exact Fin.ext (hx.trans hy.symm)
      · have hylt : (y : ℕ) < k0 := by omega
        rw [hx] at hxy
        exact absurd hxy (fun h => hc y hylt h.symm)
    · have hxlt : (x : ℕ) < k0 := by omega
      by_cases hy : (y : ℕ) = k0
      · rw [hy] at hxy
        exact absurd hxy (hc x hxlt)
      · have hylt : (y : ℕ) < k0 := by omega
        exact Fin.ext (hinj0 x hxlt y hylt hxy)
  obtain ⟨a0, ha0, harepeat⟩ := hex_repeat
  -- Telescoping `advTime` over the repeat [a0, k0).
  set S' : ℕ := ∑ k ∈ Finset.Ico a0 k0, C.adv (walkS k) with hS'
  have hwalkSum : ∀ k, C.time (C.src (walkS k)) = C.time (C.src e0) +
      ((∑ l ∈ Finset.range k, C.adv (walkS l) : ℕ) : ZMod p) := by
    intro k
    induction k with
    | zero => rw [hwalkS0]; simp
    | succ k ih =>
      rw [hwalkS_succ, hsuccS_spec _ (hwalkS_mem k), C.advTime _ (hwalkS_ne_conn k), ih]
      simp only [Finset.sum_range_succ]
      push_cast
      rw [add_assoc]
  have hsplit : (∑ l ∈ Finset.range a0, C.adv (walkS l)) + S'
      = (∑ l ∈ Finset.range k0, C.adv (walkS l)) := by
    rw [hS']
    exact Finset.sum_range_add_sum_Ico _ (le_of_lt ha0)
  have hzero : (S' : ZMod p) = 0 := by
    have h1 := hwalkSum a0
    have h2 := hwalkSum k0
    rw [harepeat] at h1
    rw [← hsplit] at h2
    push_cast at h1 h2
    linear_combination h1 - h2
  have hSle : S' ≤ C.total := by
    have hinjIco : ∀ a ∈ Finset.Ico a0 k0, ∀ b ∈ Finset.Ico a0 k0, walkS a = walkS b → a = b := by
      intro a ha b hb hab
      exact hinj0 a (Finset.mem_Ico.mp ha).2 b (Finset.mem_Ico.mp hb).2 hab
    have hsub : (Finset.Ico a0 k0).image walkS ⊆ Finset.univ.erase C.conn := by
      intro x hx
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_erase.mpr ⟨hwalkS_ne_conn k, Finset.mem_univ _⟩
    calc S' = ∑ x ∈ (Finset.Ico a0 k0).image walkS, C.adv x := by
          rw [hS', Finset.sum_image hinjIco]
      _ ≤ ∑ x ∈ Finset.univ.erase C.conn, C.adv x := Finset.sum_le_sum_of_subset hsub
      _ = C.total := by
          rw [Chain.total, ← Finset.add_sum_erase _ _ (Finset.mem_univ C.conn), C.advConn]; ring
  have hSpos : 0 < S' := by
    refine lt_of_lt_of_le (C.advPos (walkS a0) (hwalkS_ne_conn a0)) ?_
    rw [hS']
    exact Finset.single_le_sum (f := fun k => C.adv (walkS k)) (fun k _ => Nat.zero_le _)
      (Finset.mem_Ico.mpr ⟨le_refl a0, ha0⟩)
  exact absurd (natCast_eq_zero_of_lt (lt_of_le_of_lt hSle C.total_lt) hzero) (by omega)

open Classical in
/-- How many steps the connector's own walk takes to return to itself: `succ conn`'s distance to
    `conn` (`Chain.exists_walk_conn`), plus the one step from `conn` to `succ conn`. Not `0`, so
    `0 < C.cycleLen` always. -/
noncomputable def Chain.cycleLen (C : Chain p E M) : ℕ :=
  (Nat.find (C.exists_walk_conn (C.succ C.conn))) + 1

theorem walk_conn_shift (j : ℕ) : C.walk C.conn (j + 1) = C.walk (C.succ C.conn) j := by
  induction j with
  | zero => rfl
  | succ n ih => rw [Chain.walk_succ, ih]; rfl

open Classical in
theorem walk_conn_cycleLen : C.walk C.conn (C.cycleLen) = C.conn := by
  unfold Chain.cycleLen
  rw [walk_conn_shift]
  exact Nat.find_spec (C.exists_walk_conn (C.succ C.conn))

open Classical in
theorem walk_conn_ne_conn_of_pos_lt {i : ℕ} (h0 : 0 < i) (hi : i < C.cycleLen) :
    C.walk C.conn i ≠ C.conn := by
  unfold Chain.cycleLen at hi
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := i) (by omega)
  rw [Nat.succ_eq_add_one, walk_conn_shift]
  have hj : j < Nat.find (C.exists_walk_conn (C.succ C.conn)) := by
    rw [Nat.succ_eq_add_one] at hi
    omega
  exact Nat.find_min (C.exists_walk_conn (C.succ C.conn)) hj

open Classical in
/-- The walk from the connector never repeats a state before completing one lap. -/
theorem walk_conn_injOn : Set.InjOn (C.walk C.conn) (Set.Iio C.cycleLen) := by
  intro a ha b hb hab
  simp only [Set.mem_Iio] at ha hb
  rcases Nat.eq_zero_or_pos a with ha0 | ha0
  · rcases Nat.eq_zero_or_pos b with hb0 | hb0
    · omega
    · exact absurd hab (by rw [ha0]; exact Ne.symm (walk_conn_ne_conn_of_pos_lt hb0 hb))
  · rcases Nat.eq_zero_or_pos b with hb0 | hb0
    · exact absurd hab.symm (by rw [hb0]; exact Ne.symm (walk_conn_ne_conn_of_pos_lt ha0 ha))
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := a) (by omega)
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := b) (by omega)
      rw [Nat.succ_eq_add_one, walk_conn_shift] at hab
      rw [Nat.succ_eq_add_one] at hab ⊢
      have hj : j < Nat.find (C.exists_walk_conn (C.succ C.conn)) := by
        unfold Chain.cycleLen at ha; rw [Nat.succ_eq_add_one] at ha; omega
      have hk : k < Nat.find (C.exists_walk_conn (C.succ C.conn)) := by
        unfold Chain.cycleLen at hb; rw [Nat.succ_eq_add_one] at hb; omega
      rw [walk_conn_shift] at hab
      have := C.walk_inj (C.succ C.conn) (Nat.find (C.exists_walk_conn (C.succ C.conn)))
        (fun l hl => Nat.find_min (C.exists_walk_conn (C.succ C.conn)) hl) j hj k hk hab
      omega

theorem walk_conn_periodic (i : ℕ) : C.walk C.conn (i + C.cycleLen) = C.walk C.conn i := by
  induction i with
  | zero => simpa using walk_conn_cycleLen
  | succ n ih => rw [show n + 1 + C.cycleLen = (n + C.cycleLen) + 1 from by ring,
      Chain.walk_succ, Chain.walk_succ, ih]

theorem walk_conn_mod (i : ℕ) : C.walk C.conn (i % C.cycleLen) = C.walk C.conn i := by
  classical
  have hpos : 0 < C.cycleLen := by unfold Chain.cycleLen; omega
  conv_rhs => rw [← Nat.mod_add_div i C.cycleLen]
  induction (i / C.cycleLen) with
  | zero => simp
  | succ n ih =>
    rw [show i % C.cycleLen + C.cycleLen * (n+1) = (i % C.cycleLen + C.cycleLen * n) + C.cycleLen
      from by ring, walk_conn_periodic, ih]

open Classical in
/-- What one arc produces is exactly what the next one (one lap position later) consumes — the
    per-message shape `Chain.balanced` demands, read off the connector's own walk instead of an
    arbitrary satisfying assignment. -/
theorem walk_conn_dst_eq_src_succ (i : ℕ) :
    C.dst (C.walk C.conn i) = C.src (C.walk C.conn ((i + 1) % C.cycleLen)) := by
  rw [walk_conn_mod, Chain.walk_succ, C.succ_spec]

open Classical in
/-- The arcs the connector's own walk visits in one lap. `cycleSet_eq_univ` is why this is
    every arc there is. -/
noncomputable def Chain.cycleSet (C : Chain p E M) : Finset E :=
  (Finset.range C.cycleLen).image (C.walk C.conn)

open Classical in
/-- **The connector's lap is self-balanced.** The backward shift `i ↦ (i + cycleLen - 1) % cycleLen`
    on lap positions carries a src-match to the dst-match one position earlier — exactly
    `walk_conn_dst_eq_src_succ`, run backward — giving a bijection between the two filtered index
    sets and hence equal counts. True of *any* single closed walk, independent of whether it visits
    every arc. -/
theorem cycleSet_selfBalanced : C.SelfBalanced C.cycleSet := by
  classical
  have hpos : 0 < C.cycleLen := by unfold Chain.cycleLen; omega
  intro m
  unfold Chain.cycleSet
  rw [Finset.filter_image, Finset.filter_image]
  have hinj_range : Set.InjOn (C.walk C.conn) (Finset.range C.cycleLen) := by
    intro x hx y hy
    exact walk_conn_injOn (by simpa using hx) (by simpa using hy)
  rw [Finset.card_image_of_injOn
      (hinj_range.mono (by intro x hx; simpa using (Finset.mem_filter.mp hx).1)),
    Finset.card_image_of_injOn
      (hinj_range.mono (by intro x hx; simpa using (Finset.mem_filter.mp hx).1))]
  apply Finset.card_bij (fun i _ => (i + C.cycleLen - 1) % C.cycleLen)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
    refine ⟨Nat.mod_lt _ hpos, ?_⟩
    have hkey := walk_conn_dst_eq_src_succ (C := C) ((i + C.cycleLen - 1) % C.cycleLen)
    rw [mod_pred_succ C.cycleLen i hpos hi.1] at hkey
    rw [hkey, hi.2]
  · intro i hi j hj hij
    simp only [Finset.mem_filter, Finset.mem_range] at hi hj
    have := congrArg (fun x => (x + 1) % C.cycleLen) hij
    simp only [mod_pred_succ C.cycleLen i hpos hi.1, mod_pred_succ C.cycleLen j hpos hj.1] at this
    exact this
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj
    refine ⟨(j + 1) % C.cycleLen, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨Nat.mod_lt _ hpos, ?_⟩
      have hkey := walk_conn_dst_eq_src_succ (C := C) j
      rw [← hkey, hj.2]
    · exact mod_succ_pred C.cycleLen j hpos hj.1

open Classical in
/-- **The connector's lap visits every arc.** If it missed some, the leftover arcs would be
    self-balanced too — `Chain.balanced` minus a self-balanced piece (`cycleSet_selfBalanced`) is
    self-balanced — and avoid the connector by construction, which
    `no_selfBalanced_of_not_mem_conn` forbids. -/
theorem cycleSet_eq_univ : C.cycleSet = Finset.univ := by
  classical
  refine Finset.Subset.antisymm (Finset.subset_univ _) (Finset.sdiff_eq_empty_iff_subset.mp ?_)
  by_contra hne
  apply no_selfBalanced_of_not_mem_conn (C := C) (S := Finset.univ \ C.cycleSet) ?_ ?_
    (Finset.nonempty_iff_ne_empty.mpr hne)
  · intro hmem
    have := (Finset.mem_sdiff.mp hmem).2
    apply this
    have h0 : (0:ℕ) < C.cycleLen := by unfold Chain.cycleLen; omega
    unfold Chain.cycleSet
    exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr h0, Chain.walk_zero C C.conn⟩
  · intro m
    have hfilter : ∀ f : E → M, (Finset.univ \ C.cycleSet).filter (fun e => f e = m)
        = Finset.univ.filter (fun e => f e = m) \ C.cycleSet.filter (fun e => f e = m) := by
      intro f
      ext e
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
      tauto
    rw [hfilter C.src, hfilter C.dst, Finset.card_sdiff, Finset.card_sdiff]
    have hi1 : C.cycleSet.filter (fun e => C.src e = m) ∩ Finset.univ.filter (fun e => C.src e = m)
        = C.cycleSet.filter (fun e => C.src e = m) := by
      rw [Finset.inter_eq_left]
      exact Finset.filter_subset_filter _ (Finset.subset_univ _)
    have hi2 : C.cycleSet.filter (fun e => C.dst e = m) ∩ Finset.univ.filter (fun e => C.dst e = m)
        = C.cycleSet.filter (fun e => C.dst e = m) := by
      rw [Finset.inter_eq_left]
      exact Finset.filter_subset_filter _ (Finset.subset_univ _)
    rw [hi1, hi2, C.balanced m, cycleSet_selfBalanced m]

open Classical in
theorem exists_index_of_ne_conn {e : E} (he : e ≠ C.conn) :
    ∃ i, 0 < i ∧ i < C.cycleLen ∧ C.walk C.conn i = e := by
  classical
  have hmem : e ∈ C.cycleSet := by rw [cycleSet_eq_univ]; exact Finset.mem_univ e
  unfold Chain.cycleSet at hmem
  obtain ⟨i, hi, hie⟩ := Finset.mem_image.mp hmem
  refine ⟨i, ?_, Finset.mem_range.mp hi, hie⟩
  rcases Nat.eq_zero_or_pos i with hi0 | hi0
  · subst hi0
    rw [Chain.walk_zero] at hie
    exact absurd hie.symm he
  · exact hi0

open Classical in
/-- **Full clock distinctness.** No two different non-connector arcs ever consume a state with the
    same clock reading — a fortiori (via `congrArg C.time`) `Chain.src_injOn` below, but this is
    the form `VmAssignment.effects`' input order actually needs: it sorts by `Host.getInputTime`
    alone, not by a whole bridge state, so ties there would be ties here first.

    Every `e ≠ conn` sits at a unique lap position `i` (`exists_index_of_ne_conn`,
    `walk_conn_injOn`), and `Chain.time_walk` reads `src e`'s clock off that position via a sum of
    positive advances that stays below `p` (bounded exactly as `Chain.arc_position` bounds it) — so
    equal clock readings force equal accumulated advance, and the advances are strictly increasing
    in `i`, forcing equal `i`. -/
theorem Chain.time_injOn : Set.InjOn (fun e => C.time (C.src e)) {e | e ≠ C.conn} := by
  intro e1 he1 e2 he2 heq
  simp only [Set.mem_setOf_eq] at he1 he2
  simp only at heq
  obtain ⟨i1, hi1pos, hi1lt, hi1eq⟩ := exists_index_of_ne_conn he1
  obtain ⟨i2, hi2pos, hi2lt, hi2eq⟩ := exists_index_of_ne_conn he2
  obtain ⟨j1, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := i1) (by omega)
  obtain ⟨j2, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := i2) (by omega)
  rw [Nat.succ_eq_add_one] at hi1eq hi2eq hi1lt hi2lt
  rw [walk_conn_shift] at hi1eq hi2eq
  have hj1 : j1 < Nat.find (C.exists_walk_conn (C.succ C.conn)) := by
    unfold Chain.cycleLen at hi1lt; omega
  have hj2 : j2 < Nat.find (C.exists_walk_conn (C.succ C.conn)) := by
    unfold Chain.cycleLen at hi2lt; omega
  have hconn' : ∀ l < Nat.find (C.exists_walk_conn (C.succ C.conn)),
      C.walk (C.succ C.conn) l ≠ C.conn :=
    fun l hl => Nat.find_min (C.exists_walk_conn (C.succ C.conn)) hl
  have ht1 := C.time_walk (C.succ C.conn) j1 (fun l hl => hconn' l (by omega))
  have ht2 := C.time_walk (C.succ C.conn) j2 (fun l hl => hconn' l (by omega))
  rw [← hi1eq, ← hi2eq] at heq
  rw [heq, ht2] at ht1
  have hsum_eq : (C.walkSum (C.succ C.conn) j1 : ZMod p) = (C.walkSum (C.succ C.conn) j2 : ZMod p) :=
    (add_left_cancel ht1).symm
  have hinjIco : ∀ a ∈ Finset.Ico 0 j1, ∀ b ∈ Finset.Ico 0 j1,
      C.walk (C.succ C.conn) a = C.walk (C.succ C.conn) b → a = b :=
    fun a ha b hb => C.walk_inj (C.succ C.conn) j1 (fun l hl => hconn' l (by omega))
      a (Finset.mem_Ico.mp ha).2 b (Finset.mem_Ico.mp hb).2
  have hinjIco2 : ∀ a ∈ Finset.Ico 0 j2, ∀ b ∈ Finset.Ico 0 j2,
      C.walk (C.succ C.conn) a = C.walk (C.succ C.conn) b → a = b :=
    fun a ha b hb => C.walk_inj (C.succ C.conn) j2 (fun l hl => hconn' l (by omega))
      a (Finset.mem_Ico.mp ha).2 b (Finset.mem_Ico.mp hb).2
  have hb1 : C.walkSum (C.succ C.conn) j1 ≤ C.total := by
    have hthis := C.sum_Ico_le_total (C.succ C.conn) (i := 0) (k := j1) hinjIco
    rw [Chain.walkSum, Finset.range_eq_Ico]
    exact hthis
  have hb2 : C.walkSum (C.succ C.conn) j2 ≤ C.total := by
    have hthis := C.sum_Ico_le_total (C.succ C.conn) (i := 0) (k := j2) hinjIco2
    rw [Chain.walkSum, Finset.range_eq_Ico]
    exact hthis
  have hsum_nat : C.walkSum (C.succ C.conn) j1 = C.walkSum (C.succ C.conn) j2 :=
    (ZMod.val_cast_of_lt (lt_of_le_of_lt hb1 C.total_lt)).symm.trans
      ((congrArg ZMod.val hsum_eq).trans (ZMod.val_cast_of_lt (lt_of_le_of_lt hb2 C.total_lt)))
  -- `walkSum` is strictly increasing before reaching the connector, so equal sums force j1 = j2.
  have hmono : ∀ a b, a < b → (∀ l < b, C.walk (C.succ C.conn) l ≠ C.conn) →
      C.walkSum (C.succ C.conn) a < C.walkSum (C.succ C.conn) b := by
    intro a b hab hbconn
    have hsplit := C.walkSum_add (C.succ C.conn) (le_of_lt hab)
    have hpos : 0 < ∑ l ∈ Finset.Ico a b, C.adv (C.walk (C.succ C.conn) l) := by
      refine lt_of_lt_of_le (C.advPos (C.walk (C.succ C.conn) a) (hbconn a (by omega))) ?_
      exact Finset.single_le_sum (f := fun l => C.adv (C.walk (C.succ C.conn) l))
        (fun l _ => Nat.zero_le _) (Finset.mem_Ico.mpr ⟨le_refl a, hab⟩)
    omega
  have hji : j1 = j2 := by
    rcases lt_trichotomy j1 j2 with hlt | heq' | hgt
    · exact absurd hsum_nat (ne_of_lt (hmono j1 j2 hlt (fun l hl => hconn' l (by omega))))
    · exact heq'
    · exact absurd hsum_nat.symm (ne_of_lt (hmono j2 j1 hgt (fun l hl => hconn' l (by omega))))
  rw [← hi1eq, ← hi2eq, hji]

open Classical in
/-- **Full state distinctness**, as a corollary of `Chain.time_injOn`: no two different
    non-connector arcs ever consume the same state (a fortiori not just the same clock reading). -/
theorem Chain.src_injOn : Set.InjOn C.src {e | e ≠ C.conn} :=
  fun _ he1 _ he2 heq => Chain.time_injOn he1 he2 (congrArg C.time heq)

end VmChain
