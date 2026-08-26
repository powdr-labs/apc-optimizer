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
import ApcOptimizer.VmSpec.Implementation.Validation

-- `VmSpec/Audit/` (see below) is deliberately not imported here: `Audit/RealApcLegality.lean`
-- alone takes ~5 minutes to compile, and nothing in this file's own claims depends on it -- see
-- "files that audit the audit surface" below. Omitting the import keeps `lake build
-- ApcOptimizer.VmSpec` fast without disabling `Audit/`: build it explicitly, e.g. `lake build
-- ApcOptimizer.VmSpec.Audit.RealApcLegality`.

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
      Read this to learn what has been established.

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

    * `Audit/OpenVmLegalAudit.lean` — real OpenVM circuit shapes shown to satisfy the audited
      hypotheses, so that "too strong and the theorem is vacuous" is a checkable worry rather than a
      standing one.
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
      `RealApcLegality.lean`'s `lookback_of_gadget` is what ties it to `AssertLtSubAir`); and
      `byteCheck_sendsOk` — not the walk, matching, or arithmetic that produces the `Bool`.
    * `Audit/RealApcLegality.lean` — the legality clauses measured against three *real* stages of
      one APC, the keccak block at pc `2105000` in powdr's optimizer pipeline
      (`Audit/Apc2105000.lean`, emitted from the stage dumps by `Scripts/emit-apc-lean.py`). Both
      multiplicity clauses hold at every stage. `hasStepLayout` holds only of the
      trivially-simplified stage, proved almost entirely through the checkers above
      (`apc2105000Opt_hasStepLayout`); it is false of the optimizer's final output, on the all-zero
      padding row its fresh `is_valid` column makes algebraically satisfying
      (`apc2105000Gated_not_hasStepLayout`), and false of the unoptimized stage, whose four fused
      instructions' bridge states do not cancel without powdr's substitution pass. Same block at
      every stage, so each falsity is a statement about the optimizer, not about the block.
    * `Audit/SoundnessGivesLegality.lean` — how much of `Circuit.legalGuest` a chip-level soundness
      proof already gives for free, and where the residue is real: legality of the optimizer's
      output cannot be derived from soundness alone (a per-chip `Circuit.isSoundReplacementOf`
      admits assignments violating `Circuit.statelessSendOnly` outright, so it has to be assumed
      or separately established, as `openVm_vmSoundReplacement` already does). OpenVM's own
      `maintainsInvariants` (`OpenVmSemantics.lean`) transports the three bus-shape clauses of
      `Circuit.legalGuest` on *accepted* assignments (`Circuit.legalOnAccepted`,
      `legalOnAccepted_of_isSoundReplacementOf`); `legalOnAccepted_not_statelessSendOnly` and
      `openVm_sound_but_illegal` show the gap between that and full legality is real under the
      *actual* semantics. `StepLayout` has no counterpart in `Spec.lean` at all, so none of it
      transports.

    ### Not audited — the argument

    Everything under `VmSpec/Implementation/`. These files are load-bearing for the *proof* and
    invisible in every statement, so a mistake in them cannot make a theorem mean the wrong thing —
    it can only make the build fail.

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
    * `Implementation/Validation.lean` — sanity lemmas about the spec (that the guest list behaves
      as a set, that `VmSoundReplacement` is a preorder). -/
