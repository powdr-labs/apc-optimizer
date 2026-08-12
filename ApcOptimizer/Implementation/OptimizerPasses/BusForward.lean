import ApcOptimizer.Implementation.OptimizerPasses.BusUnify

set_option autoImplicit false

/-! # Dense value forwarding through value-preserving memory accesses (runtime for `busForward`)

Impl-only (no soundness lemma); the proof and wired pass live in `Proofs/BusForward.lean`.

`busUnify` drops a send→receive window whenever an intervening access sits at an address whose
aliasing with the window is undecidable. Per *slot*, more is entailed: if every undecided
intervening access is a complete same-address receive→send pair carrying the same expression in a
slot (a load's value slots), that slot survives the window whichever way the aliasing goes — a
non-aliasing pair is excluded like any different-address message, an aliasing one has the value
routed through it by the discipline, and preservation carries the slot across. The pass emits the
surviving slot equalities `R[t] = S[t]` only; the interactions all stay (only `gauss` benefits,
by merging the value variables).

Engine shape as in `BusUnify.lean`: prepared records (`denseBUPrep`), an untrusted windowed
sweep proposing `(sendPos, [(recvPos, sendPos), …], recvPos)` certificates, and a trusted
verifier (`denseBFCheckCert`) re-checking every proposal. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Preserved slots -/

/-- Slot `t` is preserved by the pair `(r, s)`: the two payload entries are syntactically equal
    expressions or equal constants (the slot test of `denseAddrConstsEq`). -/
def denseBFSlotEq (r s : BusInteraction (DenseExpr p)) (t : Nat) : Bool :=
  match r.payload[t]?, s.payload[t]? with
  | some e, some e' =>
    decide (e = e') ||
    (match e.constValue?, e'.constValue? with
     | some c, some c' => decide (c = c')
     | _, _ => false)
  | _, _ => false

/-- Slot `t` is preserved by every proposed pair. -/
def denseBFPairsPreserve (bis : Array (BusInteraction (DenseExpr p)))
    (pairs : List (Nat × Nat)) (t : Nat) : Bool :=
  pairs.all (fun kl =>
    match bis[kl.1]?, bis[kl.2]? with
    | some r, some s => denseBFSlotEq r s t
    | _, _ => false)

/-- The entailed conclusions of a verified proposal: the slot equalities `R[t] = S[t]` for the
    non-address slots preserved by every forwarding pair (timestamp slots drop out on their own —
    a real access never carries syntactically equal timestamps on its receive and send). -/
def denseBFEmit (shape : MemoryBusShape) (bis : Array (BusInteraction (DenseExpr p)))
    (pairs : List (Nat × Nat)) (S Rt : BusInteraction (DenseExpr p)) : List (DenseExpr p) :=
  ((List.range S.payload.length).filter (fun t =>
      decide (t ∉ shape.addressFields) && denseBFPairsPreserve bis pairs t)).map
    (fun t => denseEqExpr ((Rt.payload[t]?).getD (.const 0)) ((S.payload[t]?).getD (.const 0)))

/-- Boxed twin of `denseBFEmit` (see `denseMemEqConstraintsW`). -/
def denseBFEmitW (negOne pad : DenseExpr p) (shape : MemoryBusShape)
    (bis : Array (BusInteraction (DenseExpr p))) (pairs : List (Nat × Nat))
    (S Rt : BusInteraction (DenseExpr p)) : List (DenseExpr p) :=
  ((List.range S.payload.length).filter (fun t =>
      decide (t ∉ shape.addressFields) && denseBFPairsPreserve bis pairs t)).map
    (fun t => .add ((Rt.payload[t]?).getD pad) (.mul negOne ((S.payload[t]?).getD pad)))

def denseBFEmitFast (shape : MemoryBusShape) (bis : Array (BusInteraction (DenseExpr p)))
    (pairs : List (Nat × Nat)) (S Rt : BusInteraction (DenseExpr p)) : List (DenseExpr p) :=
  denseBFEmitW (.const (-1)) (.const 0) shape bis pairs S Rt

@[csimp] theorem denseBFEmit_eq_fast : @denseBFEmit = @denseBFEmitFast := by
  funext p shape bis pairs S Rt; rfl

/-! ## The verifier -/

/-- Verify a proposal's pair list over `[q, j)`: each listed pair `(k, l)` in order — receive at
    `k`, send at `l`, internally same-(syntactic/constant-)address — with every position outside
    the pairs passing `denseBUMidOk` against the outer send `aS`. The strict ordering
    `q ≤ k < l < j` is load-bearing: interleaved pairs would break the entailment (countermodel in
    `Proofs/BusForward.lean`). -/
def denseBFCheckPairs (ops : DenseZModOps p) (nw : DenseNonzeroWits p)
    (setMult prevMult : ZMod p) (arr : Array (DenseBUPre p)) (aS : DenseBUPre p) (j : Nat) :
    (pairs : List (Nat × Nat)) → (q : Nat) → Bool
  | [], q => denseBUMidScan ops nw arr aS j (j - q) q
  | (k, l) :: rest, q =>
    decide (q ≤ k) && decide (k < l) && decide (l < j) &&
    (match arr[k]?, arr[l]? with
     | some ak, some al =>
       decide (ak.mult = some prevMult) && decide (al.mult = some setMult) &&
       denseBUConstsEq ak al &&
       denseBUMidScan ops nw arr aS k (k - q) q &&
       denseBUMidScan ops nw arr aS l (l - (k + 1)) (k + 1) &&
       denseBFCheckPairs ops nw setMult prevMult arr aS j rest (l + 1)
     | _, _ => false)

/-- The verified certificate of one proposal `(i, pairs, j)`: send at `i`, receive at `j`, equal
    addresses, and `denseBFCheckPairs` on the strictly-ordered forwarding pairs between them.
    `pairs = []` is `busUnify`'s case and is not accepted here. -/
def denseBFCheckCert (ops : DenseZModOps p) (nw : DenseNonzeroWits p)
    (setMult prevMult : ZMod p) (arr : Array (DenseBUPre p)) (i : Nat)
    (pairs : List (Nat × Nat)) (j : Nat) : Bool :=
  match arr[i]?, arr[j]? with
  | some aS, some aR =>
    decide (i < j) && decide (aS.mult = some setMult) && decide (aR.mult = some prevMult) &&
    denseBUConstsEq aS aR && !pairs.isEmpty &&
    denseBFCheckPairs ops nw setMult prevMult arr aS j pairs (i + 1)
  | _, _ => false

/-! ## The proposer sweep (untrusted) -/

/-- An open forwarding window: the send's prepared record and position, the pending unmatched
    receive of a forwarding pair (if any), the closed pairs (in reverse), and the slots every
    closed pair has preserved so far. -/
structure DenseBFWin (p : ℕ) where
  pre : DenseBUPre p
  i : Nat
  pending : Option (DenseBUPre p × Nat)
  pairs : List (Nat × Nat)
  mask : List Nat

/-- One message against one window: keep (possibly updated), drop, or emit a proposal. -/
inductive DenseBFStep (p : ℕ) where
  | keep (w : DenseBFWin p)
  | drop
  | propose (prop : Nat × List (Nat × Nat) × Nat)

def denseBFStep (ops : DenseZModOps p) (nw : DenseNonzeroWits p) (setMult prevMult : ZMod p)
    (bis : Array (BusInteraction (DenseExpr p))) (mb : BusInteraction (DenseExpr p))
    (mp : DenseBUPre p) (j : Nat) (w : DenseBFWin p) : DenseBFStep p :=
  match w.pending with
  | none =>
    if decide (mp.mult = some prevMult) && denseBUConstsEq w.pre mp then
      -- a receive back at the window's own address: `pairs = []` is `busUnify`'s case.
      if w.pairs.isEmpty then .drop else .propose (w.i, w.pairs.reverse, j)
    else if denseBUMidOk ops nw w.pre mp then .keep w
    else if decide (mp.mult = some prevMult) then
      .keep { w with pending := some (mp, j) }
    else .drop
  | some (ak, k) =>
    if decide (mp.mult = some setMult) && denseBUConstsEq ak mp then
      let mask := match bis[k]? with
        | some rb => w.mask.filter (fun t => denseBFSlotEq rb mb t)
        | none => []
      if mask.isEmpty then .drop
      else .keep { w with pending := none, pairs := (k, j) :: w.pairs, mask := mask }
    else if denseBUMidOk ops nw w.pre mp then .keep w
    else .drop

/-- The sweep: a send opens a window; each later message updates or drops every open window per
    `denseBFStep`; a receive back at the window's own address with at least one closed pair yields
    a proposal. One window per send, first-match. -/
def denseBFSweep (ops : DenseZModOps p) (nw : DenseNonzeroWits p) (setMult prevMult : ZMod p)
    (shape : MemoryBusShape) (bis : Array (BusInteraction (DenseExpr p)))
    (arr : Array (DenseBUPre p)) :
    (fuel j : Nat) → (wins : List (DenseBFWin p)) →
    (out : List (Nat × List (Nat × Nat) × Nat)) → List (Nat × List (Nat × Nat) × Nat)
  | 0, _, _, out => out
  | fuel + 1, j, wins, out =>
    match arr[j]?, bis[j]? with
    | some mp, some mb =>
      let (wins, out) := wins.foldr (init := (([] : List (DenseBFWin p)), out)) fun w acc =>
        match denseBFStep ops nw setMult prevMult bis mb mp j w with
        | .keep w' => (w' :: acc.1, acc.2)
        | .drop => acc
        | .propose pr => (acc.1, pr :: acc.2)
      let wins :=
        if decide (mp.mult = some setMult) then
          { pre := mp, i := j, pending := none, pairs := [],
            mask := (List.range mb.payload.length).filter
              (fun t => decide (t ∉ shape.addressFields)) } :: wins
        else wins
      denseBFSweep ops nw setMult prevMult shape bis arr fuel (j + 1) wins out
    | _, _ => out

/-! ## Verify and emit -/

def denseBFCollect (ops : DenseZModOps p) (nw : DenseNonzeroWits p) (setMult prevMult : ZMod p)
    (shape : MemoryBusShape) (bis : Array (BusInteraction (DenseExpr p)))
    (arr : Array (DenseBUPre p)) : List (Nat × List (Nat × Nat) × Nat) → List (DenseExpr p)
  | [] => []
  | (i, pairs, j) :: rest =>
    let acc := denseBFCollect ops nw setMult prevMult shape bis arr rest
    if denseBFCheckCert ops nw setMult prevMult arr i pairs j then
      match bis[i]?, bis[j]? with
      | some S, some R => denseBFEmit shape bis pairs S R ++ acc
      | _, _ => acc
    else acc

/-- The entailed value-forwarding equalities of one bus: prepare, sweep, verify. -/
def denseBFForBus (ops : DenseZModOps p) (T : DenseTwoRootMap p) (nw : DenseNonzeroWits p)
    (shape : MemoryBusShape) (bisL : List (BusInteraction (DenseExpr p))) : List (DenseExpr p) :=
  let setMult := denseSetNewMult ops shape
  let prevMult := denseGetPreviousMult ops shape
  let bis := bisL.toArray
  let arr := bis.map (denseBUPrep shape T)
  let props := denseBFSweep ops nw setMult prevMult shape bis arr arr.size 0 [] []
  denseBFCollect ops nw setMult prevMult shape bis arr props

def denseBFEqsOf (busLists : List (Nat × MemoryBusShape × List (BusInteraction (DenseExpr p))))
    (d : DenseConstraintSystem p) : List (DenseExpr p) :=
  let T := denseBUTable busLists d
  let nw := denseBUWits d
  (busLists.map (fun sl => denseBFForBus denseZModOps T nw sl.2.1 sl.2.2)).flatten

def denseBFEqs (memShape : Nat → Option MemoryBusShape) (d : DenseConstraintSystem p) :
    List (DenseExpr p) :=
  let busLists := denseBUBusLists memShape d.busInteractions
  if busLists.isEmpty then [] else denseBFEqsOf busLists d

/-- The constraints `denseBusForwardF` appends, minus those identically zero or already present. -/
def denseBusForwardNewCs (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : List (DenseExpr p) :=
  let _ := bs
  let eqs := denseBFEqs facts.memShape d
  if eqs.isEmpty then [] else denseBUFilterNew d eqs

/-- For a memory-bus send `S` and a later receive `R` at the same address, with every message
    between them either provably different-address/inactive or part of a strictly-ordered
    same-address receive→send pair, every payload slot carried unchanged through all such pairs is
    equal on `R` and `S` — e.g. `mload a; mstore a, v; mload b (aliasing unknown); mload a -> u`
    entails `u = v`, the stored value forwarded to the second load through the value-preserving
    `mload b` pair. Emits those value-slot equalities only; no interaction is touched. -/
def denseBusForwardF (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    DenseConstraintSystem p :=
  if (1 : ZMod p) ≠ 0 then
    let new := denseBusForwardNewCs bs facts d
    if new.isEmpty then d
    else { d with algebraicConstraints := d.algebraicConstraints ++ new }
  else d

end ApcOptimizer.Dense
