import ApcOptimizer.VmSpec.Implementation.OpenVmChain

set_option autoImplicit false

/-! # OpenVM record and bridge shapes

    Two small shared pieces the audits build on: what `openVmPayloadOk` says about a record in a
    byte-checked address space, and the execution-bridge receive/send pair.

    `Audit/Legality/` is where a real APC is checked against `Circuit.legalGuest`; the gap files
    (`AdmissibleGap`, `BridgeOffsetGap`, `InputTimeGap`) use the bridge shapes below to build the
    runs they exclude. -/

namespace ApcOptimizer.OpenVM

variable {p : ℕ}

/-- `openVmPayloadOk` on a record in a byte-checked address space -- registers (`1`) or main
    memory (`2`), the two `MemoryPayload.isByteChecked` names -- is exactly "the data limbs are
    bytes". Both directions are used below: a receive hands one over, a send has to produce one. -/
theorem openVmPayloadOk_mem_iff_of_byteChecked {asp : ZMod p}
    (hasp : asp.val = 1 ∨ asp.val = 2) (ptr d0 d1 d2 d3 ts : ZMod p) :
    openVmPayloadOk (p := p) defaultBusMap (1, [asp, ptr, d0, d1, d2, d3, ts]) ↔
      (isByte d0 ∧ isByte d1 ∧ isByte d2 ∧ isByte d3) := by
  simp only [openVmPayloadOk, defaultBusMap, memoryPayload?]
  constructor
  · intro h
    have h' := h hasp
    exact ⟨h' _ (by simp), h' _ (by simp), h' _ (by simp), h' _ (by simp)⟩
  · rintro ⟨h0, h1, h2, h3⟩ - d hd
    simp at hd
    rcases hd with rfl | rfl | rfl | rfl <;> assumption

/-- The register (`1`) case, which most of this file's shapes are in. -/
theorem openVmPayloadOk_mem_iff [Fact (1 < p)] (ptr d0 d1 d2 d3 ts : ZMod p) :
    openVmPayloadOk (p := p) defaultBusMap (1, [1, ptr, d0, d1, d2, d3, ts]) ↔
      (isByte d0 ∧ isByte d1 ∧ isByte d2 ∧ isByte d3) :=
  openVmPayloadOk_mem_iff_of_byteChecked (Or.inl (ZMod.val_one p)) ptr d0 d1 d2 d3 ts

--------- The read-echo shape ---------

--------- The execution bridge ---------

/-- The execution-bridge receive: the instruction's incoming state `(pc, t)` (whitepaper §4.5,
    `ExecutionBus::execute` receives `prev_state`). -/
def bridgeRecv (pc t : ZMod p) : BusInteraction (Expression p) where
  busId := 0
  multiplicity := .const (-1)
  payload := [.const pc, .const t]

/-- The execution-bridge send: the outgoing state. -/
def bridgeSend (pc t : ZMod p) : BusInteraction (Expression p) where
  busId := 0
  multiplicity := .const 1
  payload := [.const pc, .const t]

end ApcOptimizer.OpenVM
