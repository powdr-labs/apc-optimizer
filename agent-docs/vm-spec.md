# VmSpec

`ApcOptimizer/Spec.lean` defines correctness for a single `Circuit`, with "the rest of the VM"
abstracted into `BusSemantics`'s per-message predicates. `ApcOptimizer/VmSpec/` makes the VM
explicit instead: named host chips, globally-balancing buses, and an observable input/output —
so that a whole VM's worth of guest chips, not just one circuit, can be optimized correctly.

It is a separate, still-WIP audit surface, excluded from the default `lake build` target and from
`ApcOptimizer.lean`'s import closure (see that file's comment); build it explicitly with
`lake build ApcOptimizer.VmSpec` (and `lake build ApcOptimizer.VmSpec.Audit.Legality.All` for the
slow real-circuit corpus; the counterexample files are their own roots — `Audit.BridgeOffsetGap`,
which pulls in `AdmissibleGap`, and `Audit.InputTimeGap`). `ApcOptimizer/VmSpec.lean`'s own
module docstring is the audit-tier map — which files are audited (`Basic.lean`, `Legal.lean`,
`OpenVm.lean`, `Theorems.lean`, and `Audit/` as evidence for those), which are argument-only
(`Implementation/`) and so need no audit.
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

`vmCompleteReplacement_of_forall₂` (`Implementation/Connection.lean`) derives
`VmCompleteReplacement` for a whole VM, and `openVm_vmCompleteReplacement` /
`openVm_vmEquivalent` (`Theorems.lean`) are its OpenVM instances. They assume exactly what
soundness assumes — legality of the chips, plus the per-chip replacement facts — and nothing about
the machine.

There is no second induction. `VmCompleteReplacement host G G'` *is*
`VmSoundReplacement host G' G` — the same proposition with the lists swapped — so the existing
lifting runs unchanged, once two things are dealt with:

* **The `guaranteesInvariants` conjunct points the wrong way** under the swap. It turned out to be
  dead: no step of the lifting ever read it. `Circuit.replacesOn` is the half that *is* read, and
  the three lifting theorems are now stated on it, with the old `isSoundReplacementOf` versions
  kept as corollaries at the trivial filter.
* **Per-chip completeness is conditional.** `Circuit.isCompleteReplacementOf` guarantees nothing
  about an assignment that is not `Circuit.admissible`, so the lifting may only be applied to
  instances the VM realizes, and only if those are admissible. That is what `Circuit.replacesOn`'s
  filter `P` carries, and what `Host.forcesOn` supplies. Soundness instantiates the filter at
  `True` and pays nothing.

The existential the swapped lifting needs is supplied by witness generation itself
(`witgenTotal`, `replacesOn_of_isCompleteReplacementOf`).

### The obligation that used to be open

`Host.forcesAdmissible host bs` — the VM only realizes `Circuit.admissible` guest assignments.
It is stated in the shape of `Host.ordersRanks`: quantified over whatever legal chips the host runs
and over `VmSat` assignments, mentioning no particular circuit.

It cannot be weakened into a per-circuit legality clause, and that is not a matter of taste.
`Circuit.admissible` is a memory-discipline claim — a record read back carries what was written —
and a chip's own constraints do not force it: `Apcs/TwoLoads/` has satisfying, bus-accepting
assignments that violate it whenever its two computed pointers coincide. What makes it true of a
*run* is global.

`openVmHost_forcesAdmissible` (`Implementation/MemChain.lean`) now proves it for `openVmHost`
outright, so completeness carries no VM-level hypothesis. What it rests on:

* **bus balance** — already a conjunct of `VmSat` (`balances`);
* **window atomicity** — distinct bridge arcs own disjoint stretches of the clock
  (`bridge_windows_disjoint_arc`, `Implementation/ChainDisjoint.lean`), which bounds the records
  entering one instance's window from outside;
* **the guest's own access discipline** — `Circuit.legalGuestOF` (`VmSpec/LegalOF.lean`), audited
  per APC in `Audit/OF/`;
* **three facts about the host** — the initial image is a function of the address, an input-chip
  instance reads only records set before its own writes, and only a memory `getPrevious` may reach
  backwards. `Audit/AdmissibleGap.lean`, `Audit/InputTimeGap.lean` and `Audit/BridgeOffsetGap.lean`
  carry the run each of those excludes.

It is proved against the **order-free** `openVmBusSemanticsOF`, not the positional
`openVmBusSemantics`. Nothing in the completeness path looks inside `Circuit.admissible`, so that
change of memory discipline was a drop-in: it replaced what `forcesAdmissible` must prove without
touching a line of the lifting. It is also the only version that is true of a VM — the positional
discipline reads list order as time and demands a *pairing* between a specific send and a specific
receive, which `AdmissibleGap.lean`'s `badChip2` violates while doing nothing wrong.

## What is proven against real APCs (`Audit/Apcs/`)

One directory per APC, each in its own namespace with the same member names: `Stages.lean` is the
circuit at each point of powdr's pipeline (emitted by `Scripts/emit-apc-lean.py`) plus the
modifications a proof needs, `Layout.lean` is the placement data the optimized and gated stages
share, and one file per stage carries that stage's proofs — split because each stage's
`hasStepLayout` is a slow `decide`, so they compile in parallel. `Apcs/Common.lean` holds what no
APC owns; `Audit/Legality/All.lean` imports them all and is the index.

Five APCs are audited. Three of them at three points of powdr's own optimizer pipeline — same
block, same semantics, three forms, so a difference between results is a statement about the
optimizer, not about the block:

| | what it is |
| --- | --- |
| `Apcs/Keccak2105000/` | a keccak basic block at pc `2105000`, four fused instructions |
| `Apcs/SingleXor/` | one instruction, `[x8] = [x7] ^ [x5]` — a fresh write the bitwise table vouches for |
| `Apcs/SingleBeq/` | one instruction, `if [x8] == [x5] jump +2` — a *branching* step, no write |

| | unoptimized (`000`) | trivially-simplified | final, gated |
| --- | --- | --- | --- |
| `statelessSendOnly` / `statefulPolarity` | true | true | true, out of checker reach |
| `hasStepLayout` | fused: **false** — unchained steps; single: **true** | **true** — one step | **false** — padding row |

The other two come out of the shipped benchmark corpus, which carries only the pre-gate stage, so
they are audited at that one stage — the trivially-simplified column, where legality is actually
claimed. Each reaches `opt_legalGuest`, and each brings a shape the first three do not have:

| | what it is | what is new |
| --- | --- | --- |
| `Apcs/AndBranch/` | `apc_056_pc0x200bd4`: `andi` then branch-if-nonzero, two fused instructions | a masked write, byte-valued because a *lookup* says so (`isByte_of_andEq`), not because a constraint does |
| `Apcs/LoadBranch/` | `apc_072_pc0x391014`: `loadw` then `beq`, two fused instructions | main memory — address space `2`, at a pointer the circuit computes, echoed on into a register |
| `Apcs/TwoLoads/` | `apc_002_pc0x4ecc48`: two `loadb`s then a branch, three fused instructions | two main-memory accesses that *may alias*, and a quadratic memory address |

`TwoLoads` is what forced the checkers to stop over-approximating. A **byte** load's pointer is
quadratic in its own `flags__*` selector, and `placeCheckOne` and the `.echo`/`.limbs` witnesses
used to normalize a *whole* payload to a `LinForm` — so they rejected the APC at a field neither
clause reads. `placeCheckOne` reads only the timestamp; a byte witness reads only the address space
and the four data limbs. Both now normalize exactly those (`memShapeLin`), leaving the pointer a
raw evaluated field element. The change is strictly more permissive — every other APC's `decide`
still passes unchanged — and it shortened both soundness proofs, since neither ever used the rest
of the record.

The one thing genuinely not a shape is what the load *writes*: a flag-selected byte, not an echo.
`isByte_of_loadSelect` closes it — the four selector flags are trits, the block's own shape
constraint cuts `81` combinations to exactly `4`, and each makes the selection one-hot, so the
written limb is one of the four the load brought back and `sendsOk`'s own hypothesis vouches for
those.

`LoadBranch` is why `ByteCheck.lean`'s `memShape` admits both byte-checked address spaces rather
than registers alone: `MemoryPayload.isByteChecked` covers `1` and `2`, and a load's echo crosses
from one to the other.

Both falsities are properties of the circuits, not the clause, and they split cleanly. That the
gated stage's padding row reproduces on a single-instruction APC says that gap is powdr's gating
pass, not fusion. The unoptimized stage's failure is the opposite: it is entirely about fusion — a
single-instruction `unopt` is already one step, has nothing to chain, and reaches `legalGuest` as
it stands (`SingleXor.unopt_legalGuest`, `SingleBeq.unopt_legalGuest`), off the *raw* lt gadget
powdr has not yet substituted away. The keccak block's unoptimized stage is four
instruction steps whose bridge states do not cancel until powdr's substitution pass chains their
timestamps (`from_state__timestamp_{i+1} = from_state__timestamp_i + d_i`); adding those three
equations collapses it to the one step `039` already has (`unoptChained_hasStepLayout`). Every
final stage's padding gate makes the all-zero assignment algebraically satisfying with a bridge net
of `0`, where a step's receive must net `-1` (`gated_not_hasStepLayout`); pinning `is_valid`
restores it (`gatedPinned_hasStepLayout`). Every "true" above is a decidable checker plus a soundness
theorem (`Audit/SendOnlyPolarity.lean`), not a hand proof over the circuit.

`Audit/LinForm.lean`, `BridgeCheck.lean`, `PlaceCheck.lean`, `ByteCheck.lean` are the checker
layers `opt_hasStepLayout`'s proof is built from — normalizing expressions to linear
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
