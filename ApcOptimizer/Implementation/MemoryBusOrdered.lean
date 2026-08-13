import ApcOptimizer.Implementation.MemoryBusMultiset

set_option autoImplicit false

/-! # A bus list that is already in canonical access order

`interleaveAccesses_admissibleMemoryBus_of_M` (`MemoryBusMultiset.lean`) derives the *positional*
discipline for the canonical order — receives and sends alternating, accesses ordered by send
timestamp — from the order-free rely. This file connects it to a list a pass actually holds: if the
bus's evaluated messages alternate `recv, send, recv, send, …` and the timestamps increase along
them, that list *is* the canonical order, so the positional discipline holds of it as a theorem.

That is what lets the consecutive-match sweep (`OptimizerPasses/BusUnify.lean`) run unchanged: it
walks the list left to right keeping the open sends, and its "nothing at this address in between"
test is exactly the positional hypothesis. Where the old rely *assumed* left-to-right = time order,
the pass now checks it — and where the check fails the sweep simply does not fire.

`pairUp` is the chunking; `pairUp_interleave` identifies the chunked list with `interleaveAccesses`;
`admissibleMemoryBus_of_pairUp` is the packaged bridge. -/

variable {p : ℕ}

/-! ## Chunking a list into consecutive pairs -/

/-- Split a list into consecutive `(receive, send)` pairs; `none` on an odd length. -/
def pairUp {α : Type*} : List α → Option (List (α × α))
  | [] => some []
  | [_] => none
  | a :: b :: rest => (pairUp rest).map (fun ps => (a, b) :: ps)

theorem pairUp_length {α : Type*} :
    ∀ {l : List α} {ps : List (α × α)}, pairUp l = some ps → l.length = 2 * ps.length
  | [], ps, h => by simp only [pairUp, Option.some.injEq] at h; rw [← h]; rfl
  | [_], ps, h => by simp [pairUp] at h
  | a :: b :: rest, ps, h => by
      cases hrec : pairUp rest with
      | none => rw [pairUp, hrec] at h; simp at h
      | some ps' =>
          rw [pairUp, hrec] at h
          simp only [Option.map_some, Option.some.injEq] at h
          rw [← h]
          simp only [List.length_cons]
          rw [pairUp_length hrec]
          omega

theorem pairUp_getElem_fst {α : Type*} :
    ∀ {l : List α} {ps : List (α × α)}, pairUp l = some ps →
      ∀ (i : Nat) (hi : i < ps.length), l[2 * i]? = some (ps[i]'hi).1
  | [], ps, h, i, hi => by
      simp only [pairUp, Option.some.injEq] at h
      rw [← h] at hi; simp at hi
  | [_], ps, h, _, _ => by simp [pairUp] at h
  | a :: b :: rest, ps, h, i, hi => by
      cases hrec : pairUp rest with
      | none => rw [pairUp, hrec] at h; simp at h
      | some ps' =>
          rw [pairUp, hrec] at h
          simp only [Option.map_some, Option.some.injEq] at h
          subst h
          cases i with
          | zero => simp
          | succ j =>
              have hj : j < ps'.length := by simp only [List.length_cons] at hi; omega
              have := pairUp_getElem_fst hrec j hj
              have h2 : 2 * (j + 1) = (2 * j) + 1 + 1 := by omega
              rw [h2]
              simpa using this

theorem pairUp_getElem_snd {α : Type*} :
    ∀ {l : List α} {ps : List (α × α)}, pairUp l = some ps →
      ∀ (i : Nat) (hi : i < ps.length), l[2 * i + 1]? = some (ps[i]'hi).2
  | [], ps, h, i, hi => by
      simp only [pairUp, Option.some.injEq] at h
      rw [← h] at hi; simp at hi
  | [_], ps, h, _, _ => by simp [pairUp] at h
  | a :: b :: rest, ps, h, i, hi => by
      cases hrec : pairUp rest with
      | none => rw [pairUp, hrec] at h; simp at h
      | some ps' =>
          rw [pairUp, hrec] at h
          simp only [Option.map_some, Option.some.injEq] at h
          subst h
          cases i with
          | zero => simp
          | succ j =>
              have hj : j < ps'.length := by simp only [List.length_cons] at hi; omega
              have := pairUp_getElem_snd hrec j hj
              have h2 : 2 * (j + 1) + 1 = (2 * j + 1) + 1 + 1 := by omega
              rw [h2]
              simpa using this

/-- A list that chunks into pairs *is* the canonical interleaving of those pairs' components. -/
theorem pairUp_interleave {α : Type*} {l : List α} {ps : List (α × α)} (h : pairUp l = some ps) :
    l = interleaveAccesses (fun i : Fin ps.length => (ps[i.val]'i.isLt).1)
      (fun i : Fin ps.length => (ps[i.val]'i.isLt).2) := by
  have hlen : l.length = (interleaveAccesses (fun i : Fin ps.length => (ps[i.val]'i.isLt).1)
      (fun i : Fin ps.length => (ps[i.val]'i.isLt).2)).length := by
    rw [interleaveAccesses_length]
    exact pairUp_length h
  refine List.ext_getElem hlen ?_
  intro m hm hm'
  have hmlt : m < 2 * ps.length := by rw [pairUp_length h] at hm; exact hm
  rcases interleaveAccesses_getElem?_cases (fun i : Fin ps.length => (ps[i.val]'i.isLt).1)
      (fun i : Fin ps.length => (ps[i.val]'i.isLt).2) m hmlt with
    ⟨i, hma, hget⟩ | ⟨i, hma, hget⟩
  · have hl : l[m]? = some (ps[i.val]'i.isLt).1 := by
      rw [hma]; exact pairUp_getElem_fst h i.val i.isLt
    have h1 := List.getElem?_eq_getElem hm
    have h2 := List.getElem?_eq_getElem hm'
    rw [h1] at hl; rw [h2] at hget
    exact (Option.some.inj hl).trans (Option.some.inj hget).symm
  · have hl : l[m]? = some (ps[i.val]'i.isLt).2 := by
      rw [hma]; exact pairUp_getElem_snd h i.val i.isLt
    have h1 := List.getElem?_eq_getElem hm
    have h2 := List.getElem?_eq_getElem hm'
    rw [h1] at hl; rw [h2] at hget
    exact (Option.some.inj hl).trans (Option.some.inj hget).symm

/-! ## The fibers of a chunked list -/

/-- The send fiber of a chunked list: the pairs' second components, given that exactly the second
    component of each pair passes the test. -/
theorem pairUp_filter_snd {α : Type*} (P : α → Bool) :
    ∀ {l : List α} {ps : List (α × α)}, pairUp l = some ps →
      (∀ q ∈ ps, P q.1 = false ∧ P q.2 = true) →
      l.filter P = ps.map Prod.snd
  | [], ps, h, _ => by
      simp only [pairUp, Option.some.injEq] at h
      rw [← h]; rfl
  | [_], ps, h, _ => by simp [pairUp] at h
  | a :: b :: rest, ps, h, hP => by
      cases hrec : pairUp rest with
      | none => rw [pairUp, hrec] at h; simp at h
      | some ps' =>
          rw [pairUp, hrec] at h
          simp only [Option.map_some, Option.some.injEq] at h
          subst h
          obtain ⟨hpa, hpb⟩ := hP (a, b) (List.mem_cons_self ..)
          rw [List.filter_cons_of_neg (by simp [hpa]), List.filter_cons_of_pos (by simp [hpb]),
            List.map_cons]
          exact congrArg _ (pairUp_filter_snd P hrec (fun q hq => hP q (List.mem_cons_of_mem _ hq)))

/-- The receive fiber of a chunked list: the pairs' first components. -/
theorem pairUp_filter_fst {α : Type*} (P : α → Bool) :
    ∀ {l : List α} {ps : List (α × α)}, pairUp l = some ps →
      (∀ q ∈ ps, P q.1 = true ∧ P q.2 = false) →
      l.filter P = ps.map Prod.fst
  | [], ps, h, _ => by
      simp only [pairUp, Option.some.injEq] at h
      rw [← h]; rfl
  | [_], ps, h, _ => by simp [pairUp] at h
  | a :: b :: rest, ps, h, hP => by
      cases hrec : pairUp rest with
      | none => rw [pairUp, hrec] at h; simp at h
      | some ps' =>
          rw [pairUp, hrec] at h
          simp only [Option.map_some, Option.some.injEq] at h
          subst h
          obtain ⟨hpa, hpb⟩ := hP (a, b) (List.mem_cons_self ..)
          rw [List.filter_cons_of_pos (by simp [hpa]), List.filter_cons_of_neg (by simp [hpb]),
            List.map_cons]
          exact congrArg _ (pairUp_filter_fst P hrec (fun q hq => hP q (List.mem_cons_of_mem _ hq)))

/-! ## The bridge -/

/-- A bus list in canonical access order satisfies the *positional* discipline.

    The hypotheses are what a pass can check on the syntax: the messages alternate receive/send
    (`hmults`), each access's two halves share an address (`haddr`), each receive's timestamp is
    below its own send's (`hlt`), and the send timestamps increase along the list (`hmono`). The
    order-free rely does the rest. -/
theorem admissibleMemoryBus_of_pairUp (shape : MemoryBusShape)
    {L : List (BusInteraction (ZMod p))} {ps : List (BusInteraction (ZMod p) × BusInteraction (ZMod p))}
    (hpair : pairUp L = some ps)
    (hM : admissibleMemoryBusM shape (↑L : Multiset (BusInteraction (ZMod p))))
    (hmne : -shape.setNewMult ≠ (shape.setNewMult : ZMod p))
    (hmults : ∀ q ∈ ps, q.1.multiplicity = -shape.setNewMult ∧ q.2.multiplicity = shape.setNewMult)
    (haddr : ∀ q ∈ ps, shape.address q.1 = shape.address q.2)
    (tsVal : BusInteraction (ZMod p) → ℕ)
    (hpay : ∀ m m', m.payload = m'.payload → tsVal m = tsVal m')
    (hlt : ∀ q ∈ ps, tsVal q.1 < tsVal q.2)
    (hmono : ∀ (i j : Nat) (hi : i < ps.length) (hj : j < ps.length), i < j →
      tsVal (ps[i]'hi).2 < tsVal (ps[j]'hj).2) :
    admissibleMemoryBus shape L := by
  set n := ps.length with hn
  set recv : Fin n → BusInteraction (ZMod p) := fun i => (ps[i.val]'i.isLt).1 with hrecvf
  set send : Fin n → BusInteraction (ZMod p) := fun i => (ps[i.val]'i.isLt).2 with hsendf
  -- the list is the canonical interleaving
  have hL : L = interleaveAccesses recv send := pairUp_interleave hpair
  -- the fibers, read off the chunking
  have hfil_snd : L.filter (fun m => m.multiplicity = shape.setNewMult) = ps.map Prod.snd :=
    pairUp_filter_snd _ hpair (fun q hq => by
      obtain ⟨h1, h2⟩ := hmults q hq
      refine ⟨?_, by simp [h2]⟩
      simp only [h1, decide_eq_false_iff_not]
      exact hmne)
  have hfil_fst : L.filter (fun m => m.multiplicity = -shape.setNewMult) = ps.map Prod.fst :=
    pairUp_filter_fst _ hpair (fun q hq => by
      obtain ⟨h1, h2⟩ := hmults q hq
      refine ⟨by simp [h1], ?_⟩
      simp only [h2, decide_eq_false_iff_not]
      exact fun h => hmne h.symm)
  have hMsends : Multiset.filter (fun m => m.multiplicity = shape.setNewMult)
      (↑L : Multiset (BusInteraction (ZMod p))) = Multiset.map send ↑(List.finRange n) := by
    rw [Multiset.filter_coe, hfil_snd]
    have : (↑(ps.map Prod.snd) : Multiset (BusInteraction (ZMod p)))
        = Multiset.map (fun q : BusInteraction (ZMod p) × BusInteraction (ZMod p) => q.2) ↑ps := rfl
    rw [this, hsendf]
    have hps : (↑ps : Multiset _) = Multiset.map (fun i : Fin n => ps[i.val]'i.isLt)
        ↑(List.finRange n) := by
      calc (↑ps : Multiset _) = (↑((List.finRange n).map ps.get) : Multiset _) := by
            rw [← List.ofFn_eq_map, List.ofFn_get]
        _ = Multiset.map (fun i : Fin n => ps[i.val]'i.isLt) ↑(List.finRange n) := rfl
    rw [hps, Multiset.map_map]
    rfl
  have hMrecvs : Multiset.filter (fun m => m.multiplicity = -shape.setNewMult)
      (↑L : Multiset (BusInteraction (ZMod p))) = Multiset.map recv ↑(List.finRange n) := by
    rw [Multiset.filter_coe, hfil_fst]
    have : (↑(ps.map Prod.fst) : Multiset (BusInteraction (ZMod p)))
        = Multiset.map (fun q : BusInteraction (ZMod p) × BusInteraction (ZMod p) => q.1) ↑ps := rfl
    rw [this, hrecvf]
    have hps : (↑ps : Multiset _) = Multiset.map (fun i : Fin n => ps[i.val]'i.isLt)
        ↑(List.finRange n) := by
      calc (↑ps : Multiset _) = (↑((List.finRange n).map ps.get) : Multiset _) := by
            rw [← List.ofFn_eq_map, List.ofFn_get]
        _ = Multiset.map (fun i : Fin n => ps[i.val]'i.isLt) ↑(List.finRange n) := rfl
    rw [hps, Multiset.map_map]
    rfl
  rw [hL]
  exact interleaveAccesses_admissibleMemoryBus_of_M shape (↑L) recv send hM hMsends hMrecvs hmne
    (fun i => haddr _ (List.getElem_mem i.isLt)) tsVal hpay
    (fun i j hij => hmono i.val j.val i.isLt j.isLt hij)
    (fun i => hlt _ (List.getElem_mem i.isLt))
