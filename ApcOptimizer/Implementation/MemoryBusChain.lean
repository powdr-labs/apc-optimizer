import ApcOptimizer.MemoryBus

set_option autoImplicit false

/-! # The forced chain of a designated-entry bus

Consequences of `entryKeyed` (`ApcOptimizer/MemoryBus.lean`) for a bus whose records form a
*chain*: an execution bridge, where access `i` receives the CPU state `(pc i, ts i)` and sends
`(pc (i+1), ts i + δ)`. `chain_pinned` is the combinatorial core and `entryKeyed_chain_copies` the
pass-facing package: presenting one address group as `n` accesses whose key slots chain (`send i`
carries `recv (i+1)`'s key) with pairwise distinct receive keys, every receive but the entry one
copies the previous send's payload.

Two facts do the work, and neither trusts the interaction order:

* ENTRY_KEY makes every non-entry receive *matched* — its payload is some send's payload
  (`payload_matched_of_entryKeyed`, pure counting; the excess-cardinality half of the discipline
  is not even needed).
* the matching is strictly *decreasing* in receive timestamps (a receive's own send is later,
  `hlt`), so it cannot cycle. That is what excludes the exit send — whose key slot is a jump target
  and generally unknown — from stealing an interior receive: the steal closes a cycle through the
  chain, and the timestamps along it would have to return to their start.
-/

variable {p : ℕ}

/-- With the entry record designated, every *other* receive is matched: its payload is the payload
    of a send at the same address. Counting only — the excess multiset holds entry-keyed payloads,
    so a receive keyed otherwise cannot be in it, hence the sends cover it. -/
theorem payload_matched_of_entryKeyed (shape : MemoryBusShape)
    {M : Multiset (BusInteraction (ZMod p))} {addr : List (Option (ZMod p))}
    {slot : Nat} {key : ZMod p} (hkey : entryKeyed shape slot key M)
    {R : BusInteraction (ZMod p)} (hR : R ∈ recvsAt shape addr M)
    (hne : R.payload[slot]? ≠ some key) :
    ∃ S ∈ sendsAt shape addr M, S.payload = R.payload := by
  set A := (recvsAt shape addr M).map BusInteraction.payload with hA
  set B := (sendsAt shape addr M).map BusInteraction.payload with hB
  have hcountA : 1 ≤ Multiset.count R.payload A :=
    Multiset.count_pos.mpr (Multiset.mem_map.mpr ⟨R, hR, rfl⟩)
  have hexcess : Multiset.count R.payload (A - B) = 0 := by
    by_contra hpos
    exact hne (hkey addr R.payload (Multiset.count_pos.mp (Nat.pos_of_ne_zero hpos)))
  rw [Multiset.count_sub] at hexcess
  have hcountB : 1 ≤ Multiset.count R.payload B := by omega
  obtain ⟨S, hS, hSp⟩ := Multiset.mem_map.mp (Multiset.count_pos.mp hcountB)
  exact ⟨S, hS, hSp⟩

/-- The combinatorial core. `n` accesses of one group, access `i` receiving `recv i` and sending
    `send i` at a strictly later timestamp; the receives' key slots are pairwise distinct and
    `send i` carries `recv (i+1)`'s key (the chain). If every receive but the first is matched by
    some send, the matching is forced to be the chain: receive `i` copies `send (i - 1)`.

    The last send is unconstrained — its key slot may be anything, so a priori it could be the
    partner of any receive. Timestamps exclude it: the partner relation strictly decreases the
    receive timestamp, and a steal by the last send would close a cycle back up the chain. -/
theorem chain_pinned {n : ℕ} (send recv : Fin n → BusInteraction (ZMod p)) (slot : Nat)
    (tsVal : BusInteraction (ZMod p) → ℕ)
    (hts : ∀ m m', m.payload = m'.payload → tsVal m = tsVal m')
    (hlt : ∀ i, tsVal (recv i) < tsVal (send i))
    (hdistinct : ∀ i j : Fin n, (recv i).payload[slot]? = (recv j).payload[slot]? → i = j)
    (hchain : ∀ (i : Fin n) (h : i.val + 1 < n),
      (send i).payload[slot]? = (recv ⟨i.val + 1, h⟩).payload[slot]?)
    (hmatched : ∀ j : Fin n, 0 < j.val → ∃ i, (recv j).payload = (send i).payload) :
    ∀ j : Fin n, 0 < j.val →
      (recv j).payload
        = (send ⟨j.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le j.val 1) j.isLt⟩).payload := by
  -- A matched receive whose partner is not the last send is the partner's chain successor.
  have hsucc : ∀ (j i : Fin n), (recv j).payload = (send i).payload → (h : i.val + 1 < n) →
      j.val = i.val + 1 := by
    intro j i hij h
    have hslot : (recv j).payload[slot]? = (recv ⟨i.val + 1, h⟩).payload[slot]? := by
      rw [show (recv j).payload[slot]? = (send i).payload[slot]? from by rw [hij], hchain i h]
    exact congrArg Fin.val (hdistinct j ⟨i.val + 1, h⟩ hslot)
  intro j hj
  obtain ⟨i, hij⟩ := hmatched j hj
  by_cases hlast : i.val + 1 < n
  · -- the partner is an interior send: `j` is its chain successor
    have hjv : j.val = i.val + 1 := hsucc j i hij hlast
    rw [show (⟨j.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le j.val 1) j.isLt⟩ : Fin n) = i from
      Fin.ext (show j.val - 1 = i.val by omega)]
    exact hij
  -- the partner is the last send: walk the chain up from `j` and contradict its timestamp
  exfalso
  have hin : i.val + 1 = n := by have := i.isLt; omega
  have hji : j.val ≤ i.val := by have := j.isLt; omega
  -- along the chain, receive timestamps increase; `j`'s is at most `i`'s
  have hmono : ∀ m : ℕ, ∀ hm : m < n, j.val ≤ m → tsVal (recv j) ≤ tsVal (recv ⟨m, hm⟩) := by
    intro m
    induction m with
    | zero =>
      intro hm hjm
      rw [show (⟨0, hm⟩ : Fin n) = j from Fin.ext (show 0 = j.val by omega)]
    | succ m ih =>
      intro hm hjm
      rcases Nat.lt_or_ge j.val (m + 1) with hlt1 | hge
      · -- `j ≤ m`: extend the chain by one step
        have hmn : m < n := by omega
        have hIH := ih hmn (by omega)
        obtain ⟨i', hi'⟩ := hmatched ⟨m + 1, hm⟩ (Nat.succ_pos m)
        by_cases hlast' : i'.val + 1 < n
        · -- an interior partner: it is `m`, so `recv m`'s timestamp is below `recv (m+1)`'s
          have him : i'.val = m := by
            have h : m + 1 = i'.val + 1 := hsucc ⟨m + 1, hm⟩ i' hi' hlast'
            omega
          have hrec : recv i' = recv ⟨m, hmn⟩ := by congr 1; exact Fin.ext him
          have h1 : tsVal (recv ⟨m + 1, hm⟩) = tsVal (send i') := hts _ _ hi'
          have h2 : tsVal (recv i') < tsVal (send i') := hlt i'
          rw [hrec] at h2
          omega
        · -- the last send again: it would give `recv (m+1)` and `recv j` equal keys
          have hii : i' = i := Fin.ext (by have := i'.isLt; omega)
          rw [hii] at hi'
          have hslot : (recv ⟨m + 1, hm⟩).payload[slot]? = (recv j).payload[slot]? := by
            rw [show (recv ⟨m + 1, hm⟩).payload[slot]? = (send i).payload[slot]? from by rw [hi'],
              show (send i).payload[slot]? = (recv j).payload[slot]? from by rw [hij]]
          have hcontra : m + 1 = j.val := congrArg Fin.val (hdistinct ⟨m + 1, hm⟩ j hslot)
          omega
      · -- `j = m + 1`
        rw [show (⟨m + 1, hm⟩ : Fin n) = j from Fin.ext (show m + 1 = j.val by omega)]
  have hjle := hmono i.val i.isLt hji
  have hii : (⟨i.val, i.isLt⟩ : Fin n) = i := Fin.ext rfl
  rw [hii] at hjle
  have h1 : tsVal (recv j) = tsVal (send i) := hts _ _ hij
  have h2 : tsVal (recv i) < tsVal (send i) := hlt i
  omega

/-- The pass-facing package: an order-free `entryKeyed` group presented as `n` chained accesses
    forces every non-entry receive to copy the previous send's payload. `hentry` is what the pass
    checks per receive — its key slot is not the entry key — and `hchain`/`hdistinct` are the
    syntactic chain conditions on the key slot. -/
theorem entryKeyed_chain_copies {n : ℕ} (shape : MemoryBusShape)
    (M : Multiset (BusInteraction (ZMod p))) (addr : List (Option (ZMod p)))
    (slot : Nat) (key : ZMod p) (hkey : entryKeyed shape slot key M)
    (send recv : Fin n → BusInteraction (ZMod p))
    (hsend : sendsAt shape addr M = Multiset.map send ↑(List.finRange n))
    (hrecv : recvsAt shape addr M = Multiset.map recv ↑(List.finRange n))
    (tsVal : BusInteraction (ZMod p) → ℕ)
    (hts : ∀ m m', m.payload = m'.payload → tsVal m = tsVal m')
    (hlt : ∀ i, tsVal (recv i) < tsVal (send i))
    (hdistinct : ∀ i j : Fin n, (recv i).payload[slot]? = (recv j).payload[slot]? → i = j)
    (hchain : ∀ (i : Fin n) (h : i.val + 1 < n),
      (send i).payload[slot]? = (recv ⟨i.val + 1, h⟩).payload[slot]?)
    (hentry : ∀ j : Fin n, 0 < j.val → (recv j).payload[slot]? ≠ some key) :
    ∀ j : Fin n, 0 < j.val →
      (recv j).payload
        = (send ⟨j.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le j.val 1) j.isLt⟩).payload := by
  refine chain_pinned send recv slot tsVal hts hlt hdistinct hchain ?_
  intro j hj
  have hmem : recv j ∈ recvsAt shape addr M := by
    rw [hrecv]
    exact Multiset.mem_map.mpr ⟨j, by rw [Multiset.mem_coe]; exact List.mem_finRange j, rfl⟩
  obtain ⟨S, hS, hSp⟩ := payload_matched_of_entryKeyed shape hkey hmem (hentry j hj)
  rw [hsend] at hS
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hS
  exact ⟨i, hSp.symm⟩
