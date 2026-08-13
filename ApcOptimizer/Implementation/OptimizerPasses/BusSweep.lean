import ApcOptimizer.Implementation.MemoryBusOrdered
import ApcOptimizer.Implementation.OptimizerPasses.BusUnify

set_option autoImplicit false

/-! # Dense consecutive-match bus unification (runtime transform for `busSweep`)

Impl-only (no soundness lemma). `denseBusSweepF` matches the `denseF` shape `DenseVerifiedPassW.of`
(`Bridge.lean`) wraps directly.

Where the timestamp-group engine (`BusUnify.lean`) certifies one *address group* at a time — and so
needs every other interaction on the bus certified disjoint from it, which symbolic pointers deny —
this pass certifies the bus's list *as a whole*: it chunks into `(receive, send)` accesses and
checks that they are already in canonical access order (`denseBSOrder?`). The order-free rely then
yields the positional discipline for that list as a theorem
(`admissibleMemoryBus_of_pairUp`, `Implementation/MemoryBusOrdered.lean`), in which each
evaluated-address group is a *subsequence* — so no interaction is ever certified disjoint from
another and aliasing never enters.

On that list the pre-migration consecutive-match sweep runs unchanged: one left-to-right pass
maintaining open send windows (`constOpen`, keyed by canonical address; `symOpen`, tested against
every message), proposing `(sendPos, recvPos)` pairs. The sweep is untrusted — `denseBSCheckPair`
re-verifies every proposal — so it uses the fingerprint tests while the verifier uses the exact
ones. Proofs in `Proofs/BusSweep.lean`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## The canonical-order certificate

The pass *proposes* the bus's accesses as index pairs `(receivePos, sendPos)` — bucket by canonical
address key, pair the k-th receive with the k-th send of each bucket, order by send timestamp — and
`denseBSOrder?` verifies the proposal: the indices are a permutation of the bus's positions, each
pair shares an address and carries the solved LessThan gadget (`denseBUGadgetOk`), and the sends'
timestamps share one linear base whose constants step by `[1, B)` along the proposed order
(`denseBUSendTsOk`).

Pairing by *matching* rather than by list adjacency is what keeps the pass alive after
`busPairCancel` has removed matched pairs: a receive whose own send is gone is still certifiable
against a later same-address send, because its ts slot is still the lt-aux decomposition of the
shared base and `denseBUGadgetOk` recognizes the difference. -/

/-- One access of the pairing: its receive and send, each with its prepared record. -/
abbrev DenseBSPair (p : ℕ) :=
  (BusInteraction (DenseExpr p) × DenseBUPre p) × (BusInteraction (DenseExpr p) × DenseBUPre p)

/-- Placeholder for an out-of-range index. The permutation certificate excludes those, and keeping
    the record in `denseBUPrep` form makes the pairing's shape invariant unconditional. -/
def denseBSDefault (shape : MemoryBusShape) (T : DenseTwoRootMap p) :
    BusInteraction (DenseExpr p) × DenseBUPre p :=
  let bi : BusInteraction (DenseExpr p) :=
    { busId := 0, payload := [], multiplicity := .const 0 }
  (bi, denseBUPrep shape T bi)

/-- The proposed accesses, read off index pairs. -/
def denseBSAccessesOf (dflt : BusInteraction (DenseExpr p) × DenseBUPre p)
    (arr : Array (BusInteraction (DenseExpr p) × DenseBUPre p)) (ps : List (Nat × Nat)) :
    List (DenseBSPair p) :=
  ps.map (fun ij => ((arr[ij.1]?).getD dflt, (arr[ij.2]?).getD dflt))

/-- The bus's interactions rearranged into the certified canonical access order: each access's
    receive immediately before its own send, accesses ordered by send timestamp. -/
def denseBSCanon (shape : MemoryBusShape) (T : DenseTwoRootMap p)
    (bisL : List (BusInteraction (DenseExpr p))) (ps : List (Nat × Nat)) :
    List (BusInteraction (DenseExpr p)) :=
  ((denseBSAccessesOf (denseBSDefault shape T)
    (bisL.map (fun bi => (bi, denseBUPrep shape T bi))).toArray ps).flatMap
      (fun q => [q.1, q.2])).map (fun z => z.1)

/-- A monotone `Nat` key for the *signed* offset of `c` from `c0`, so ordering by it orders the
    timestamps whichever instruction's clock the shared base came from. -/
def denseBSTsKey (c0 c : ZMod p) : Nat := ((c - c0).val + p / 2) % p

/-- The proposal (untrusted): bucket the positions by canonical address key, pair the k-th receive
    with the k-th send of each bucket, then order the accesses by send timestamp. -/
def denseBSPropose (setMult prevMult : ZMod p) (tsField : Nat)
    (zipped : List (BusInteraction (DenseExpr p) × DenseBUPre p)) : List (Nat × Nat) :=
  let step := fun (acc : Nat × Std.HashMap (DenseAddrKey p) (List Nat × List Nat))
      (bp : BusInteraction (DenseExpr p) × DenseBUPre p) =>
    let (i, m) := acc
    (i + 1,
      match bp.2.key with
      | some k =>
        let rs := m.getD k ([], [])
        if bp.2.mult = some prevMult then m.insert k (i :: rs.1, rs.2)
        else if bp.2.mult = some setMult then m.insert k (rs.1, i :: rs.2)
        else m
      | none => m)
  let m := (zipped.foldl step (0, ∅)).2
  let pairs := m.toList.flatMap (fun kv => kv.2.1.reverse.zip kv.2.2.reverse)
  let arr := zipped.toArray
  let sendConst := fun (j : Nat) =>
    match arr[j]? with
    | some z => match denseBUTsLin tsField z.1 with | some L => some L.const | none => none
    | none => none
  match pairs.head? with
  | none => []
  | some ij0 =>
    match sendConst ij0.2 with
    | none => []
    | some c0 =>
      let keyed := pairs.map (fun ij =>
        match sendConst ij.2 with
        | some c => (denseBSTsKey c0 c, ij)
        | none => (0, ij))
      (keyed.mergeSort (fun a b => a.1 ≤ b.1)).map (fun x => x.2)

/-- The proposed indices are a permutation of the bus's positions — so the accesses cover every
    interaction exactly once, which is what makes the reordered list a permutation of the bus. -/
def denseBSCheckPerm (n : Nat) (ps : List (Nat × Nat)) : Bool :=
  decide ((ps.flatMap (fun ij => [ij.1, ij.2])).mergeSort (· ≤ ·) = List.range n)

/-- Every chunk is a `(receive, send)` pair at one address. -/
def denseBSPairsOk (setMult prevMult : ZMod p) (ps : List (DenseBSPair p)) : Bool :=
  ps.all (fun q =>
    decide (q.1.2.mult = some prevMult) && decide (q.2.2.mult = some setMult) &&
      denseBUConstsEq q.1.2 q.2.2)

/-- Every access's receive precedes its own send in time. -/
def denseBSGadgetsOk (bs : BusSemantics p) (facts : BusFacts p bs)
    (allBis : List (BusInteraction (DenseExpr p))) (idx : DenseBUIdx)
    (tsField B : Nat) (ps : List (DenseBSPair p)) : Bool :=
  ps.all (fun q => denseBUGadgetOk bs facts allBis idx tsField B q.2.1 q.1.1)

/-- Everything the pairing has to satisfy. -/
def denseBSChecksOk (bs : BusSemantics p) (facts : BusFacts p bs) (shape : MemoryBusShape)
    (T : DenseTwoRootMap p) (setMult prevMult : ZMod p)
    (tsField B : Nat) (allBis : List (BusInteraction (DenseExpr p)))
    (idx : DenseBUIdx)
    (zipped : List (BusInteraction (DenseExpr p) × DenseBUPre p)) (ps : List (Nat × Nat)) : Bool :=
  denseBSCheckPerm zipped.length ps
    && decide (2 ^ 30 < p) && decide (B ≤ 2 ^ 29)
    && denseBSPairsOk setMult prevMult (denseBSAccessesOf (denseBSDefault shape T) zipped.toArray ps)
    && denseBSGadgetsOk bs facts allBis idx tsField B
        (denseBSAccessesOf (denseBSDefault shape T) zipped.toArray ps)
    && denseBUSendTsOk tsField B
        ((denseBSAccessesOf (denseBSDefault shape T) zipped.toArray ps).map (fun q => q.2.1))

/-- The verified pairing: index pairs covering the bus exactly once, each a same-address
    `(receive, send)` with the gadget, ordered by send timestamp. -/
def denseBSOrder? (bs : BusSemantics p) (facts : BusFacts p bs) (shape : MemoryBusShape)
    (T : DenseTwoRootMap p) (setMult prevMult : ZMod p)
    (tsField B : Nat) (allBis : List (BusInteraction (DenseExpr p)))
    (idx : DenseBUIdx)
    (zipped : List (BusInteraction (DenseExpr p) × DenseBUPre p)) : Option (List (Nat × Nat)) :=
  let ps := denseBSPropose setMult prevMult tsField zipped
  if denseBSChecksOk bs facts shape T setMult prevMult tsField B allBis idx zipped ps
  then some ps else none

/-! ## The consumer sweep

One left-to-right pass over the bus's prepared array maintaining open send windows and closing,
excluding or dropping them as later messages consume, exclude or block them. -/

/-- One message tested against one open window (consumer / excluded / blocker). -/
inductive DenseBSStepRes
  | consumer
  | excluded
  | blocker

/-- The sweep's classification: exact on the consumer and constant arms, signature-gated on the
    affine and two-root arms. A signature collision can only turn a blocker into an exclusion, so
    the window lives longer and the extra proposal is rejected by `denseBSCheckPair`. -/
def denseBSStepSig (ops : DenseZModOps p) (nw : DenseNonzeroWits p) (prevMult : ZMod p)
    (a b : DenseBUPre p) : DenseBSStepRes :=
  if decide (b.mult = some prevMult) && denseBUConstsEq a b then .consumer
  else if denseBUConstsNeq a b || denseBUAffineNeq a b || denseBUTwoRootNeq a b
      || denseBUNonzeroNeq nw a b || decide (b.mult = some ops.zero) then .excluded
  else .blocker

/-- An open send window: its prepared record and its position. -/
structure DenseBSWin (p : ℕ) where
  pre : DenseBUPre p
  i : Nat

/-- The sweep. Returns the consumed windows as `(sendPos, recvPos)` pairs, in consume order. -/
def denseBSSweep (ops : DenseZModOps p) (nw : DenseNonzeroWits p) (setMult prevMult : ZMod p)
    (arr : Array (DenseBUPre p)) :
    (fuel : Nat) → (j : Nat) →
    (constOpen : Std.HashMap (DenseAddrKey p) (DenseBSWin p)) →
    (symOpen : List (DenseBSWin p)) →
    (out : List (Nat × Nat)) → List (Nat × Nat)
  | 0, _, _, _, out => out
  | fuel + 1, j, constOpen, symOpen, out =>
    match arr[j]? with
    | none => out
    | some mp =>
      -- (1) constant-keyed windows: an all-constant message meets only the window at its own key;
      --     a symbolic-address message is tested against every one.
      let (constOpen, out) :=
        if mp.allConst then
          match mp.key with
          | some k =>
            match constOpen[k]? with
            | some w =>
              match denseBSStepSig ops nw prevMult w.pre mp with
              | .consumer =>
                (constOpen.erase k, if w.i < j then (w.i, j) :: out else out)
              | .excluded => (constOpen, out)
              | .blocker => (constOpen.erase k, out)
            | none => (constOpen, out)
          | none => (constOpen, out)
        else
          let (drops, out) := constOpen.toList.foldl (init := (([] : List (DenseAddrKey p)), out))
            fun da kw =>
              match denseBSStepSig ops nw prevMult kw.2.pre mp with
              | .consumer =>
                (kw.1 :: da.1, if kw.2.i < j then (kw.2.i, j) :: da.2 else da.2)
              | .excluded => da
              | .blocker => (kw.1 :: da.1, da.2)
          (drops.foldl (·.erase ·) constOpen, out)
      -- (2) symbolic-keyed windows are tested literally against every message.
      let (symOpen, out) :=
        if symOpen.isEmpty then (symOpen, out) else
        symOpen.foldr (init := (([] : List (DenseBSWin p)), out)) fun w sa =>
          match denseBSStepSig ops nw prevMult w.pre mp with
          | .consumer => (sa.1, if w.i < j then (w.i, j) :: sa.2 else sa.2)
          | .excluded => (w :: sa.1, sa.2)
          | .blocker => (sa.1, sa.2)
      -- (3) a send opens its window; a same-key window that survived (1) moves to `symOpen`.
      let (constOpen, symOpen) :=
        if decide (mp.mult = some setMult) then
          match mp.key with
          | some k =>
            let w : DenseBSWin p := ⟨mp, j⟩
            if k.allConst then
              match constOpen[k]? with
              | some old => (constOpen.insert k w, old :: symOpen)
              | none => (constOpen.insert k w, symOpen)
            else (constOpen, w :: symOpen)
          | none => (constOpen, symOpen)
        else (constOpen, symOpen)
      denseBSSweep ops nw setMult prevMult arr fuel (j + 1) constOpen symOpen out

/-- Scatter the sweep's pairs by send position, then read them back ascending — the pairs come
    out in consume order, and the equalities have to follow send order. -/
def denseBSScatter (n : Nat) (pairs : List (Nat × Nat)) : Array (Option Nat) :=
  pairs.foldl (fun a ij => a.setIfInBounds ij.1 (some ij.2)) (Array.replicate n none)

def denseBSCands (out : Array (Option Nat)) : (i : Nat) → List (Nat × Nat) → List (Nat × Nat)
  | 0, acc => acc
  | i + 1, acc =>
    match out[i]? with
    | some (some j) => denseBSCands out i ((i, j) :: acc)
    | _ => denseBSCands out i acc

/-! ## The verifier

`denseBSCheckPair` on prepared records over an index range: no `mid` list is materialized, and
every arm is the exact certificate. -/

def denseBSMidOk (ops : DenseZModOps p) (nw : DenseNonzeroWits p) (a b : DenseBUPre p) : Bool :=
  denseBUConstsNeq a b || denseBUAffineNeq a b || denseBUTwoRootNeq a b
    || denseBUNonzeroNeq nw a b || decide (b.mult = some ops.zero)

def denseBSMidScan (ops : DenseZModOps p) (nw : DenseNonzeroWits p) (arr : Array (DenseBUPre p))
    (a : DenseBUPre p) (j : Nat) : (fuel : Nat) → (q : Nat) → Bool
  | 0, _ => true
  | fuel + 1, q =>
    if q ≥ j then true
    else
      match arr[q]? with
      | none => true
      | some b => if denseBSMidOk ops nw a b then denseBSMidScan ops nw arr a j fuel (q + 1)
                  else false

/-- The verifier checks the ordering itself, which is what lets the sweep stay entirely untrusted:
    nothing about the windows, the scatter or the candidate order carries a proof obligation. -/
def denseBSCheckPair (ops : DenseZModOps p) (nw : DenseNonzeroWits p) (setMult prevMult : ZMod p)
    (arr : Array (DenseBUPre p)) (i j : Nat) : Bool :=
  match arr[i]?, arr[j]? with
  | some a, some r =>
    decide (i < j) && decide (a.mult = some setMult) && decide (r.mult = some prevMult) &&
      denseBUConstsEq a r && denseBSMidScan ops nw arr a j (j - i) (i + 1)
  | _, _ => false

/-- For each verified candidate, the entailed slot equalities, in ascending send-position order. -/
def denseBSCollect (ops : DenseZModOps p) (nw : DenseNonzeroWits p) (setMult prevMult : ZMod p)
    (shape : MemoryBusShape) (bis : Array (BusInteraction (DenseExpr p)))
    (arr : Array (DenseBUPre p)) : List (Nat × Nat) → List (DenseExpr p)
  | [] => []
  | (i, j) :: rest =>
    let acc := denseBSCollect ops nw setMult prevMult shape bis arr rest
    if denseBSCheckPair ops nw setMult prevMult arr i j then
      match bis[i]?, bis[j]? with
      | some S, some R => denseMemEqConstraints shape S R ++ acc
      | _, _ => acc
    else acc

/-! ## Per-invocation scaffolding -/

/-- The entailed equalities of one bus with a declared ts slot: prepare, certify a pairing into
    canonical access order, sweep that order, verify. A bus whose interactions do not certify
    contributes nothing. -/
def denseBSForBus (bs : BusSemantics p) (facts : BusFacts p bs) (ops : DenseZModOps p)
    (T : DenseTwoRootMap p) (nw : DenseNonzeroWits p) (shape : MemoryBusShape) (tsField B : Nat)
    (allBis : List (BusInteraction (DenseExpr p))) (idx : DenseBUIdx)
    (bisL : List (BusInteraction (DenseExpr p))) : List (DenseExpr p) :=
  let setMult := denseSetNewMult ops shape
  let prevMult := denseGetPreviousMult ops shape
  let zipped := bisL.map (fun bi => (bi, denseBUPrep shape T bi))
  match denseBSOrder? bs facts shape T setMult prevMult tsField B allBis idx zipped with
  | none => []
  | some ps =>
    let canon := denseBSCanon shape T bisL ps
    let arr := (canon.map (denseBUPrep shape T)).toArray
    let pairs := denseBSSweep ops nw setMult prevMult arr arr.size 0 ∅ [] []
    let out := denseBSScatter arr.size pairs
    denseBSCollect ops nw setMult prevMult shape canon.toArray arr
      (denseBSCands out out.size [])

/-- The equalities every bus contributes, before the zero / already-present filter. A bus without
    a declared ts slot (`facts.memTsField`) contributes nothing. -/
def denseBSEqsOf (bs : BusSemantics p) (facts : BusFacts p bs)
    (busLists : List (Nat × MemoryBusShape × List (BusInteraction (DenseExpr p))))
    (d : DenseConstraintSystem p) : List (DenseExpr p) :=
  let T := denseBUTable busLists d
  let nw := denseBUWits d
  let idx := denseBUBuildIdx bs facts d.busInteractions
  (busLists.map (fun sl =>
    match facts.memTsField sl.1 with
    | some (tsField, B) =>
      denseBSForBus bs facts denseZModOps T nw sl.2.1 tsField B d.busInteractions idx sl.2.2
    | none => [])).flatten

def denseBSEqs (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    List (DenseExpr p) :=
  let busLists := denseBUBusLists facts.memShape d.busInteractions
  if busLists.isEmpty then [] else denseBSEqsOf bs facts busLists d

/-- The constraints `denseBusSweepF` appends: the entailed slot equalities of every verified
    consecutive send→receive pair, minus those that are identically zero or already present. -/
def denseBusSweepNewCs (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : List (DenseExpr p) :=
  let eqs := denseBSEqs bs facts d
  if eqs.isEmpty then [] else denseBUFilterNew d eqs

/-- For a memory bus, a `setNew` (send) at address `a` followed by a matching `getPrevious`
    (receive) at the same address with nothing at that address in between must carry the same
    payload, so this adds the entailed slot equalities `getᵢ = setᵢ` for every provably-matched
    such pair on each declared memory / execution-bridge bus whose interaction list is certified to
    be in canonical access order (skipping equations already present or zero).

    No-new-variable side condition holds by construction (`denseMemEqConstraints_vars`). -/
def denseBusSweepF (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    DenseConstraintSystem p :=
  if (1 : ZMod p) ≠ 0 then
    let new := denseBusSweepNewCs bs facts d
    if new.isEmpty then d
    else { d with algebraicConstraints := d.algebraicConstraints ++ new }
  else d

end ApcOptimizer.Dense
