# VmSpec

`ApcOptimizer/Spec.lean` defines correctness for a single `Circuit`, with "the rest of the VM"
abstracted into `BusSemantics`'s per-message predicates. `ApcOptimizer/VmSpec/` makes the VM
explicit instead: named host chips, globally-balancing buses, and an observable input/output —
so that a whole VM's worth of guest chips, not just one circuit, can be optimized correctly.

It is a separate, still-WIP audit surface, excluded from the default `lake build` target and from
`ApcOptimizer.lean`'s import closure (see that file's comment); build it explicitly with
`lake build ApcOptimizer.VmSpec` (and `lake build ApcOptimizer.VmSpec.Audit.RealApcLegality` for
the slow real-circuit file). `ApcOptimizer/VmSpec.lean`'s own module docstring is the audit-tier
map — which files are audited (`Basic.lean`, `Legal.lean`, `OpenVm.lean`, `Theorems.lean`, and
`Audit/` as evidence for those), which are argument-only (`Implementation/`) and so need no audit.
This document is the rationale and the known gaps, not a restatement of that map.

## The VM-level statement (`Basic.lean`)

A `Host` names a fixed VM: its `chips : List (HostChip p)` (memory init/final, lookup tables, one
or more input chips, the output chip — each only an effect predicate `canProduce` plus an
`instanceBound`, no explicit circuit), the trace-budget and anti-wraparound fields
(`maxInstances`, `maxWindow`, `maxLookback`, `maxInteractions`, `noTimeOverflow`,
`noMultOverflow`), and what it requires of any guest chip it runs (`legalGuest`). A `Vm` pairs a
`Host` with a `Guest` (a `List Circuit`).

`VmSat` is the runtime-checkable half: every guest instance's algebraic constraints hold, every
host instance is producible and within its bound, every bus balances, and the guest instance count
fits the budget. Two things are deliberately *not* in `VmSat`: `Host.legalGuest` (quantifies over
every assignment, not just realized ones — the optimizer's problem, not the VM's) and anything
that is a consequence of several chips together (rank/byte invariants — proved in
`Implementation/`, not assumed).

`CanProduce vm e := ∃ a, VmSat vm a ∧ a.effects = e` is the whole correctness vocabulary:

- `VmSoundReplacement host G G'` — every effect `G'` can produce, `G` can too (nothing new).
- `VmCompleteReplacement host G G'` — every effect `G` can produce, `G'` can too (nothing lost);
  definitionally `VmSoundReplacement host G' G`.
- `VmEquivalent` — both directions.

`PreservesDegree` is the VM-level analogue of `Spec.lean`'s `optimizerRespectsDegreeBound`.

## Guest-chip legality (`Legal.lean`)

The VM has some shared resources: the bridge, memory, and tables. The resources are implemented
using balancing, but can be modeled more abstractly (as a program/time counter, a RAM, and ROMs) so
long as every chip "uses them correctly". Legality is that per-chip requirement, made explicit. It
needs to be guaranteed initially by OpenVM, and preserved by the optimizer.

`Host.legalGuest` is instantiated by `Circuit.legalGuest r maxWindow maxLookback maxInteractions`,
four clauses: `sendOnly` (`Circuit.statelessSendOnly`, `0`/`1` multiplicities on stateless buses),
`polarity` (`Circuit.statefulPolarity`, `0`/`±1` on stateful buses), `size` (bounded interaction
count), and `stepLayout` (`Circuit.hasStepLayout`) — every algebraically-satisfying,
stateless-accepting assignment admits a `StepLayout`.

A `StepLayout` is one instruction step: it receives `(pcFrom, tStart)` and sends
`(pcTo, tStart + tWindow)` on the execution bridge and nothing else there (`bridgeRecv`,
`bridgeSend`, `bridgeNoOther`), with `0 < tWindow < maxWindow`. Every stateful interaction sits at
an integer offset (`tOffset`) from `tStart`, in `[-maxLookback, tWindow]` — a receive may reach
back before the step (where the record it names was left), a send may not go past the step's own
end (`tOffsetMatch`). `memSendsOk` is the byte-invariant induction: a memory send's payload is Ok
given that every earlier-offset memory interaction's was.

Offsets, not timestamps, are what every clause is stated on, and that is what makes the clauses
checkable per-chip at all: a `ZMod p` timestamp's `.val` order is not what an AIR constrains, but
an integer offset comparison is wraparound-free by construction. Offsets are also what lets the
ordering leave the audited surface entirely — `Implementation/Rank.lean`'s `RankModel` turns
"offset order" into "rank order" globally (`Host.ordersRanks`, `VmAssignment.ordersRanks`), but no
field of `Host`, `VmSat`, `CanProduce`, `VmEquivalent`, or `Circuit.legalGuest` mentions a rank —
a reader checking what the theorem *says* never meets one.

## Connecting to a per-chip optimizer (`Implementation/Connection.lean`)

`vmSoundReplacement_of_forall₂` is the soundness half: given `host.realizes bs rm r0` (the fixed
facts about the concrete VM — `Realizes.lean`) and `host.legalGuests (G ++ G')`, a `List.Forall₂`
of per-chip `Circuit.isSoundReplacementOf` lifts to `VmSoundReplacement host G G'`. It is exactly
the shape a chip-level optimizer's own correctness proof produces (`Circuit.isSoundReplacementOf`
is one conjunct of `Optimizer.isCorrect`), so wiring `ApcOptimizer/Optimizer.lean`'s optimizer into
a whole-VM statement needs one more thing: legality of `G'`, the optimizer's *output*.

That is not free. `Circuit.legalGuest`'s clauses all have the shape "property `P` holds of *every*
algebraically-satisfying assignment" — no bus-acceptance required, because a real AIR cannot check
`legalGuest` at runtime. `Circuit.isSoundReplacementOf`, by contrast, only constrains assignments
that also satisfy bus acceptance (`Circuit.satisfies`), and only their *net* multiplicity per
stateful message — so a bus interaction's individual multiplicity is invisible to it, on any
stateless bus entirely and on any bus in isolation from the net. A sound replacement can therefore
introduce an assignment that is algebraically satisfying but not bus-accepting, with an
out-of-discipline multiplicity — legal chips do not admit such assignments, but nothing about
soundness rules the replacement out of admitting one — a chip sending a stateless message with a
wholly unconstrained multiplicity is a sound replacement of one sending the same message at a
legal, constant multiplicity, and violates `Circuit.statelessSendOnly` outright.
`Audit/SoundnessGivesLegality.lean` sharpens this against OpenVM's own bus semantics, measuring
how much of `legalGuest` a sound, satisfiable replacement still gives for free (all three
bus-shape clauses, but only on the assignments the semantics
*accepts* — `Circuit.legalOnAccepted`) and exhibiting a chip where the residual gap is real
(`openVm_sound_but_illegal`). So legality-preservation needs a **separate** argument per pass,
parallel to its soundness proof — for a pass that only ever rewrites a payload expression while
leaving multiplicity expressions untouched, that should be a short syntactic corollary;
`Audit/SendOnlyPolarity.lean`'s translation-validation checker is aimed at verifying exactly that
residual case on a pass's concrete output instead of proving it in general.

## Completeness

No theorem currently derives `VmCompleteReplacement` for a whole VM, and the obstacle is not proof
effort so much as a shape mismatch. `VmCompleteReplacement` is definitionally
`VmSoundReplacement host G' G` — the same existential shape as soundness, just the two lists
swapped — but that shape cannot be reached from `Circuit.isSoundReplacementOf` alone: soundness is
a one-directional containment, and an optimizer that replaced every chip with an unsatisfiable
circuit would be trivially sound and nowhere near complete. What is needed instead is the genuinely
different, per-chip `Circuit.isCompleteReplacementOf` — already proved per pass and composed to the
top of the audited, non-VM optimizer (`PassCorrect`'s fourth conjunct,
`OptimizerPasses/Basic.lean`) — threaded through a `Connection.lean`-shaped induction that has not
been written.

That induction would also need a VM-level notion of "real trace" that does not exist yet.
`Circuit.isCompleteReplacementOf`'s guarantee is gated on `Circuit.admissible`, which checks a
memory-ordering discipline (`admissibleMemoryBus`, `MemoryBus.lean`) over *one circuit's own local*
list of stateful bus interactions — the right scope when that circuit is a whole program, which is
what the non-VM optimizer assumes. A guest chip here is one instruction (or fused block) among
possibly thousands in a run, so the real "this is an honest execution" property spans every chip
instance stitched together by the host over real time — a fact no definition in `VmSpec/` states
today. Building it, and showing a genuine run's per-instance restriction satisfies each chip's own
local `admissible`, is new work; it will likely reuse the execution-bridge/offset machinery built
for soundness (`StepLayout`, `Implementation/Chain.lean`, `Implementation/OpenVmChain.lean`) but
pointed at a different conclusion.

## What is proven against a real APC (`Audit/RealApcLegality.lean`)

Measured against the keccak block at pc `2105000`, at three points of powdr's own optimizer
pipeline (`Audit/Apc2105000.lean`, emitted by `Scripts/emit-apc-lean.py`) — same block, same
semantics, three forms, so a difference between results is a statement about the optimizer, not
about the block:

| | unoptimized (`000`) | trivially-simplified (`039`) | final, gated (`040`) |
| --- | --- | --- | --- |
| `statelessSendOnly` / `statefulPolarity` | true | true | true, out of checker reach |
| `hasStepLayout` | **false** — four unchained steps | **true** — one step | **false** — padding row |

Both falsities are properties of the circuits, not the clause. The unoptimized stage is four
instruction steps whose bridge states do not cancel until powdr's substitution pass chains their
timestamps (`from_state__timestamp_{i+1} = from_state__timestamp_i + d_i`); adding those three
equations collapses it to the one step `039` already has
(`apc2105000UnoptChained_hasStepLayout`). The final stage's padding gate makes the all-zero
assignment algebraically satisfying with a bridge net of `0`, where a step's receive must net `-1`
(`apc2105000Gated_not_hasStepLayout`); pinning `is_valid` restores it
(`apc2105000GatedPinned_hasStepLayout`). Every "true" above is a decidable checker plus a
soundness theorem (`Audit/SendOnlyPolarity.lean`), not a hand proof over the circuit.

`Audit/LinForm.lean`, `BridgeCheck.lean`, `PlaceCheck.lean`, `ByteCheck.lean` are the checker
layers `apc2105000Opt_hasStepLayout`'s proof is built from — normalizing expressions to linear
form, then deciding the bridge shape, each interaction's offset (via a per-interaction `Recipe`),
and the byte invariant, respectively — each exposing a soundness theorem as its audit surface and
nothing about the search or arithmetic that produces its `Bool`.

## Known limitations

- **`inputChunkOf`/`outputArrayOf` recover *a* witness, not *the* one that actually produced the
  contribution.** `Host.getInputChunk`/`getOutput` need an ordered array off a bare `BusState`,
  which carries no enumeration of what touched it; `Classical.choose` picks some `InputRead`/
  `OutputRead` whose reconstructed messages match, which is all `canProduce` promises. Deliberate,
  not an oversight (see `OpenVm.lean`'s module docstring) — but it means two different input
  streams can, in principle, produce the identical `BusState` contribution.
- **The configuration conditions are asserted, not instantiated.** No `OpenVmParams` value exists
  in the repo satisfying `windowOk`/`budgetOk` at real segment sizes, so whether they are
  satisfiable at, say, `maxInstances = 2^22` guest instructions is still an open question rather
  than a checked fact.
- **Only `HINT_STOREW` is modelled** as an input chip; `Rv32HintStoreAir`'s other opcode,
  `HINT_BUFFER` (many words per instance off a count register), has none. `Host.inputChips` is a
  list, so adding it is a new entry, not a reshape.
- **`openVmHost` treats the write pointer register (`ptrReg`) as a VM-wide constant**, when real
  OpenVM chooses it per instruction (`extensions/rv32im/circuit/src/hintstore/execution.rs`, operand
  `b`). A faithful model puts it in the per-instance witness instead.
- **Initial memory in address spaces `1`/`2` is unconstrained**, with unbounded support —
  `memoryInitHostChip` allows it, so a segment's public inputs are an unobserved VM input. (Address
  space `3`, which the output chip reads, is pinned to all-zero.)
