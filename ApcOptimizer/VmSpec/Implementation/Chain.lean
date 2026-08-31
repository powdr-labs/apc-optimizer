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

end VmChain
