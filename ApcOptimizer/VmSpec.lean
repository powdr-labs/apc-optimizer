import ApcOptimizer.VmSpec.Basic
import ApcOptimizer.VmSpec.Legal
import ApcOptimizer.VmSpec.OpenVm
import ApcOptimizer.VmSpec.Theorems
import ApcOptimizer.VmSpec.Implementation.Rank
import ApcOptimizer.VmSpec.Implementation.Counting
import ApcOptimizer.VmSpec.Implementation.Realizes
import ApcOptimizer.VmSpec.Implementation.Connection
import ApcOptimizer.VmSpec.Implementation.OpenVmConnection
import ApcOptimizer.VmSpec.Implementation.Chain
import ApcOptimizer.VmSpec.Implementation.OpenVmChain
import ApcOptimizer.VmSpec.Implementation.FuseLegal
import ApcOptimizer.VmSpec.Implementation.Validation

-- `VmSpec/Audit/` (see below) is deliberately not imported here: `Audit/Apcs/`
-- alone takes ~10 minutes to compile, and nothing in this file's own claims depends on it -- see
-- "files that audit the audit surface" below. Omitting the import keeps `lake build
-- ApcOptimizer.VmSpec` fast without disabling `Audit/`: build it explicitly, e.g. `lake build
-- ApcOptimizer.VmSpec.Audit.Legality.All`.

/-! # The VM-level correctness spec

    `Spec.lean` says what it means to replace *one* circuit correctly. This folder says what it
    means to replace the guest chips of a *whole VM* correctly, and connects the two.

    ## What has to be audited

    The split is by directory, matching the convention `AGENTS.md` sets for the repository as a
    whole: **everything directly under `VmSpec/` is audited; nothing under
    `VmSpec/Implementation/` is.**

    ### Audited — the theorems

    * `VmSpec/Theorems.lean` — the VM-level correctness theorems. Statements only: each proof is a
      one-line application of an `Implementation/` lemma, mirroring `ApcOptimizer/Optimizer.lean`.
      Read this to learn what has been established. Soundness needs only legality; completeness
      needs the rely to be forced as well, and that is a theorem
      (`openVmHost_forcesAdmissible`) rather than a hypothesis, so its statement assumes nothing
      about the machine either.

    ### Audited — the statement

    * `VmSpec/Basic.lean` — the spec proper. `Host`, `Vm`, `VmSat`, `VmAssignment.effects`,
      `CanProduce`, and the `VmSoundReplacement`/`VmCompleteReplacement`/`VmEquivalent` trio. Every
      field of `Host` here feeds `VmSat` or `effects`, so each one changes what the theorem *means*.
    * `VmSpec/Legal.lean` — `Circuit.legalGuest`, what a VM requires of a guest chip. This is a
      *hypothesis* of the theorems rather than part of the spec, so the risk it carries is the
      opposite one: too strong and the theorem is vacuous rather than wrong.
    * `VmSpec/OpenVm.lean` — the modelled OpenVM: its host chips, laid out to satisfy `StepLayout`
      (`Legal.lean`). The chips decide which real runs `CanProduce` can represent, so a chip that
      is too restrictive silently narrows the claim.

    ### Audited — files that audit the audit surface

    `VmSpec/Audit/`: nothing in `Basic.lean`/`Legal.lean`/`OpenVm.lean`/`Theorems.lean` depends on
    this folder, and nothing in it proves a new claim about a run — each file is either evidence
    that those files' hypotheses are checkable and non-vacuous, or a decidable checker that a
    candidate circuit satisfies them, not an ingredient of the soundness argument. It still lives
    directly under `VmSpec/`, so the directory rule still applies: a mistake here is a mistake in
    what gets audited, just not a mistake that can make a theorem *wrong*, only vacuous or (for a
    checker) unsound. This file does not import it (see the note above the imports) — that is a
    build-time exclusion, not a claim it needs no audit.

    For a checker file, that means only its *exposed soundness statement* needs auditing — that a
    `true` result from some `Bool`-valued function really does give the legality clause it claims
    to — never the function itself: a bug there can only make the checker fail to fire (return
    `false` where it could have returned `true`), never wrongly certify an illegal circuit, because
    `decide` has Lean's kernel re-derive the proof from the computation rather than trust it. This
    is `SendOnlyPolarity.lean`'s pattern, and every checker below follows it.

    * `Audit/OpenVmShapes.lean` — what `openVmPayloadOk` says about a record in a byte-checked
      address space, and the execution-bridge receive/send pair. Shared by the checkers and the gap
      files below.
    * `Audit/SendOnlyPolarity.lean` — a decidable, syntactic check that a candidate circuit's
      bus-interaction multiplicities satisfy `Circuit.statelessSendOnly`/`Circuit.statefulPolarity`.
      What needs auditing is the *statement* of `checkMultiplicities_sound`/
      `checkMultiplicitiesWith_sound` — that a `true` result really does give
      `statelessSendOnly`/`statefulPolarity` — exactly as a pass's correctness statement is audited
      in `ApcOptimizer/Implementation/OptimizerPasses/`; the checker itself (`Expression.foldConst`,
      `checkMultiplicities`, `pinRuleOf`, `checkMultiplicitiesWith`) needs no audit.
    * `Audit/LinForm.lean` — normalizes `Expression p` to a constant plus a coefficient vector over
      a fixed variable list, and re-reads a circuit's traffic on one bus as a sum over normalized
      entries. Every checker below builds on it without restating it, so what needs auditing is
      `Expression.toLin_eval` (the normal form denotes the expression, given the pin rules hold) and
      `allEffects_eq_entrySum` (the entry sum is the circuit's net); the normalizer itself
      (`Expression.toLin`, `busEntries`) does not.
    * `Audit/BridgeCheck.lean`, `Audit/PlaceCheck.lean`, `Audit/ByteCheck.lean` — decidable checks
      for `StepLayout`'s three remaining shapes: the execution-bridge receive/send/nothing-else
      triple, the placement and ordering of stateful interactions (via a per-interaction `Recipe`,
      since a memory receive's offset depends on the assignment — the gadget bound it reaches back
      by), and the byte invariant a memory send must satisfy. What needs auditing is each checker's
      exposed statement — `bridgeCheck_sound`; `recipe_placed`, `recipe_ordered` and
      `gadgetIdentity_sound` (the last is generic linear-identity checking, not OpenVM-specific —
      `Audit/Apcs/Common.lean`'s `lookback_of_gadget` is what ties it to `AssertLtSubAir`); and
      `byteCheck_sendsOk` — not the walk, matching, or arithmetic that produces the `Bool`.
    * `Audit/Apcs/` — the real APCs themselves, one directory per APC: `Stages.lean` (emitted
      from powdr's stage dumps by `Scripts/emit-apc-lean.py`) carries the circuits, `Layout.lean`
      the pin rules and byte witnesses, and `Opt.lean` the checker results for the stage powdr
      emits, over the shared `Apcs/Common.lean`.
    * `Audit/Legality/` — that corpus measured against `Circuit.legalGuest`. `Check.lean` is a
      decidable checker for the memory-access clauses, in the idiom of `Audit/PlaceCheck.lean`;
      `All.lean` is the index. Every APC passes, each by a single kernel `decide` over a pairing
      list, and three of the clauses were shaped by what the corpus refuted — see that file.
    * `Audit/AdmissibleGap.lean`, `Audit/BridgeOffsetGap.lean`, `Audit/InputTimeGap.lean` — the
      audit-surface gaps the VM-level completeness argument has turned up, each with the chip or
      witness that exhibits it and the clause that closes it. `AdmissibleGap`: an ordinary write
      listed send-first, and an initial image holding two records for one cell — closed by the
      order-free rely and `memoryInitHostChip`'s injectivity. `BridgeOffsetGap`: a cancelling
      pair of bridge messages at a wrapped timestamp, satisfying the original `StepLayout` in
      full — closed by `StepLayout.negOffsetOnlyMemRecv`. `InputTimeGap`: `InputRead` never
      stated §4.6.1's `t_prev < t` for its own two memory accesses, so a `HINT_STOREW` could read
      back a record set after its own write — closed by `InputRead.ptrOffsetOk`/`wordOffsetOk`,
      whose audit that file is. Each records the run or chip that would otherwise slip through.
    * `Implementation/Rank.lean` — `RankModel`, the ordering the balancing induction descends on.
      Deliberately *not* a field of `Host`: see that file for why a wrong choice cannot make the
      theorem unsound.
    * `Implementation/Counting.lean` — the anti-wraparound counting lemmas.
    * `Implementation/Realizes.lean` — `Host.realizes` and what it buys (`Host.forcesAccepts`).
    * `Implementation/Connection.lean` — per-chip `isSoundReplacementOf` to `VmSoundReplacement`.
    * `Implementation/OpenVmConnection.lean` — the same, discharged for `openVmHost`.
    * `Implementation/Chain.lean` — the balanced-arc combinatorics that turn a run's
      execution-bridge traffic into an ordering, with no mention of a circuit or a bus.
    * `Implementation/OpenVmChain.lean` — that argument applied to `openVmHost`, giving
      `Host.pinsRanks`: one range-checked boundary timestamp bounds every timestamp in the run.
    * `Implementation/ChainDisjoint.lean` — the same combinatorics strengthened to *disjointness*:
      distinct bridge arcs own disjoint stretches of the clock. `Chain.no_balanced_subset` is its
      core, and it needs no cycle argument — a balanced arc subset missing the connector telescopes
      its own time to zero while being an honest natural below `p`.
    * `Implementation/OrderFreeRealizes.lean` — `Host.realizes` transported to the order-free
      rely, which is free: `realizes` never reads `BusSemantics.admissible`, the only field that
      differs.
    * `Implementation/HostCounts.lean`, `Implementation/Excess.lean` — the host's exact signed
      contribution at a message, and `excessAt`'s cardinality bound reduced to a list count.
    * `Implementation/Forces.lean` — placement and record matching: every instance on the clock,
      every memory receive matched to a producer, and TS_BOUND, `x0ReturnsZero` and the execution
      bridge's own admissibility discharged.
    * `Implementation/MemChain.lean` — send- and receive-uniqueness for a whole run, the
      per-address counting that bounds the records entering one instance, and
      `openVmHost_forcesAdmissible`: the completeness theorem's last assumption, discharged.
    * `Implementation/Fusion.lean`, `Implementation/FuseLegal.lean` — fusing two instruction chips
      into one. `Fusion.lean` has the VM-level equivalence between the fused chip and its
      ingredients (`vmEquivalent_fuse_cons`, given budget to unfuse); `FuseLegal.lean` has
      `Circuit.legalGuest_fuse`, that legality survives fusion.
    * `Implementation/Validation.lean` — sanity lemmas about the spec (that the guest list behaves
      as a set, that `VmSoundReplacement` is a preorder). -/
