import ApcOptimizer.VmSpec.Legal

set_option autoImplicit false

/-! **The soundness argument's ordering on stateful state.** Nothing here is audited.

    `maintains_of_stateful_active` derives the memory byte invariant by strong induction, and an
    induction needs something to descend on. A `RankModel` is that something: a natural-number rank
    on bus messages.

    It is *not* part of the VM. No field of `Host` mentions it, and neither does `VmSat`,
    `CanProduce`, `VmEquivalent` — nor, since the layout redesign, `Circuit.legalGuest`. A reader
    checking what the correctness theorem *says*, or what it requires of a guest chip, never meets
    it. It appears only as a parameter of `Host.realizes`, which the argument discharges once per
    VM, and is inferred rather than written at every use site.

    What a chip promises is stated in `StepLayout`'s own coordinates: every stateful interaction
    sits at an integer offset from its step's base, and a send comes after everything it is
    justified by. Turning that into a rank order is this file's job and the VM's — see
    `Host.ordersRanks` — because only the VM knows where a step's base sits on the global clock. -/

variable {p : ℕ}

/-- A rank on stateful bus messages.

    For OpenVM: a message's timestamp, shifted into the naturals by the maximum lookback
    (`openVmRank`). A rank reads a field element as a natural number, so "the rank went up" is the
    order it looks like only while ranks stay inside a window too narrow to wrap — which is what
    `bound` records. -/
structure RankModel (p : ℕ) where
  /-- How the argument orders stateful state — for OpenVM, a shifted timestamp. -/
  rank : BusMessage p → ℕ
  /-- How far `rank` may reach in a run the VM will accept. -/
  bound : ℕ

/-- **Offsets order ranks.** Within one guest instance, an interaction placed earlier in its
    step's window has the smaller rank.

    This is the whole of what the soundness induction needs from the VM, and it is what replaced a
    *bound* on every rank: `StepLayout.sendsOk` hands a chip the interactions before its send, and
    the induction can only supply those at a strictly smaller rank.

    It is a genuinely multi-chip fact, which is why it is not a conjunct of `VmSat` and not a
    clause of legality: a step's offsets are relative to its own `base`, and only the execution
    bridge — walked across the whole run — says where that base sits on the global clock. See
    `Host.ordersRanks` and, for OpenVM, `openVmHost_ordersRanks`. -/
def VmAssignment.ordersRanks {vm : Vm p} (a : VmAssignment p vm) (rm : RankModel p)
    (r : GuestBusRules p) (maxWindow maxLookback : ℕ) : Prop :=
  ∀ (t : Fin vm.guest.length) (asg : ChipAssignment p), asg ∈ a.guestAssignments t →
    ∀ L : StepLayout (vm.guest.get t) r asg maxWindow maxLookback,
      ∀ i j : Fin (vm.guest.get t).busInteractions.length,
        (vm.guest.get t).activeStateful r asg i → (vm.guest.get t).activeStateful r asg j →
          L.tOffset j < L.tOffset i →
            rm.rank ((vm.guest.get t).msgAt asg j) < rm.rank ((vm.guest.get t).msgAt asg i)
