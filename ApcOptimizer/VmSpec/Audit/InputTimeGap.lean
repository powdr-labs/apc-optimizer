import ApcOptimizer.VmSpec.OpenVm
import ApcOptimizer.VmSpec.Legal

set_option autoImplicit false

/-! # An input-chip instance may not read a record from its own future

    §4.6.1 says a memory access "adds a message `(addr_space, ptr, ·, t_prev)` to the receive set
    and a message `(addr_space, ptr, ·, t)` to the send set", with the AIR constraining
    `t_prev < t`. `StepLayout.memPartner_time` states that for a guest chip.

    `InputRead` — the host's `HINT_STOREW` witness — makes exactly two memory accesses, writing
    the peeked register back at `base + 1` and the hinted word at `base + 2`
    (`InputRead.interactions`). It used to say **nothing** about the `ptrTime`/`wordTime` its two
    receives carry, even though its own docstring described them as set by an *earlier*
    instruction. `InputRead.ptrOffsetOk`/`wordOffsetOk` close that gap, and this file is the audit
    of those two clauses: each access's receive really is placed strictly before its own send.

    ## Why the clause is load-bearing

    `Implementation/Forces.lean` bounds the records entering a block at one address by the
    counting identity `X(τ) + fin(τ) = init(τ) ≤ 1`, where `X(τ)` counts the access pairs of the
    run crossing the threshold `τ`. Splitting `C(τ) = #{pairs : t_prev < τ} + fin(τ)` into
    `#{pairs : t < τ} + X(τ)` is the step that needs `t_prev < t` of **every** pair in the run —
    a reverse-ordered pair contributes to a `Y(τ)` term instead, and `Y` has no bound.

    Without these clauses `Host.forcesAdmissible` is false, not merely unproven. Take
    `P.ptrReg = 5` and watch register `(1,5)`; the bridge chain makes the windows tile `[1,18)`:

    | instance | window | receives at `(1,5)` | sends at `(1,5)` |
    | --- | --- | --- | --- |
    | initial image | — | — | `t = 0` |
    | input `I₁`, `base = 1` | `[1, 4)` | `t = 0` | `t = 2` |
    | input `I₂`, `base = 4` | `[4, 7)` | **`t = 17`** | `t = 5` |
    | guest `G`, `base = 7`, `d = 10` | `[7, 17)` | `t = 2`, `t = 5` | `t = 8`, `t = 9` |
    | guest `H`, `base = 17`, `d = 1` | `[17, 18)` | `t = 9` | `t = 17` |
    | memory finalization | — | `t = 8` | — |

    Every record at `(1,5)` is sent once and received once, and `G` satisfies every clause of
    `Circuit.legalGuest`: its sends sit at offsets `1` and `2`, distinct and inside `[0, 10)`;
    its receives sit at offsets `-5` and `-2`, each before its own partner. Yet both of `G`'s
    receives reach back before its window, so `card (excessAt …) = 2`. The one illegal step in the
    whole run is `I₂` reading a record set at `t = 17` and writing at `t = 5` — `ptrOffset = 13`,
    which `ptrOffsetOk` now rejects. -/

namespace ApcOptimizer.OpenVM.InputTimeGap

/-- **The register peek reads a record strictly older than the write-back it performs.** The
    write-back lands at offset `1` (`InputRead.interactions`, `base + 1`), so this is §4.6.1's
    `t_prev < t` on the offset scale — the scale it can be *stated* on, since the timestamps
    themselves are field elements. -/
theorem inputRead_ptr_ordered (r : InputRead babyBear) : r.ptrOffset < (1 : ℤ) :=
  r.ptrOffsetOk.2

/-- …and the hinted word's overwrite, whose write lands at offset `2`. -/
theorem inputRead_word_ordered (r : InputRead babyBear) : r.wordOffset < (2 : ℤ) :=
  r.wordOffsetOk.2

/-- Neither reaches further back than `AssertLtSubAir` can range-check — the same lookback
    `StepLayout.tOffsetMatch` allows a guest chip. -/
theorem inputRead_lookback (r : InputRead babyBear) :
    -(openVmTimestampBound : ℤ) ≤ r.ptrOffset ∧ -(openVmTimestampBound : ℤ) ≤ r.wordOffset :=
  ⟨r.ptrOffsetOk.1, r.wordOffsetOk.1⟩

/-- **The offsets are offsets of the interactions actually emitted.** Read off
    `InputRead.interactions`: the register access is the pair `2 ↔ 3`, receiving at
    `base + ptrOffset` and sending at `base + 1`; the word access is `4 ↔ 5`, receiving at
    `base + wordOffset` and sending at `base + 2`. A clause about `ptrOffset` that did not pin the
    emitted timestamp would constrain nothing. -/
theorem inputRead_ptr_pair (r : InputRead babyBear) (ptrReg : Nat) :
    ((r.interactions ptrReg 0 1)[2]?.bind (fun bi => bi.payload[6]?))
        = some (r.base + ((r.ptrOffset : ℤ) : ZMod babyBear)) ∧
      ((r.interactions ptrReg 0 1)[3]?.bind (fun bi => bi.payload[6]?))
        = some (r.base + 1) := by
  have hlen : r.ptrLimbs.toList.length = 4 := by simp
  exact ⟨by simp [InputRead.interactions, hlen, r.ptrTimeMatch],
    by simp [InputRead.interactions, hlen]⟩

theorem inputRead_word_pair (r : InputRead babyBear) (ptrReg : Nat) :
    ((r.interactions ptrReg 0 1)[4]?.bind (fun bi => bi.payload[6]?))
        = some (r.base + ((r.wordOffset : ℤ) : ZMod babyBear)) ∧
      ((r.interactions ptrReg 0 1)[5]?.bind (fun bi => bi.payload[6]?))
        = some (r.base + 2) := by
  have hlen : r.oldWord.toList.length = 4 := by simp
  exact ⟨by simp [InputRead.interactions, hlen, r.wordTimeMatch],
    by simp [InputRead.interactions]⟩

/-- **`I₂` above is now unconstructible.** Its register peek would need `ptrOffset = 13`, reading
    a record set at `t = 17` while writing at `t = 5`. -/
theorem inputRead_no_reverse_pair (r : InputRead babyBear) : ¬ (1 ≤ r.ptrOffset) := by
  have := r.ptrOffsetOk.2
  omega

end ApcOptimizer.OpenVM.InputTimeGap
