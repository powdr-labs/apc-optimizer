import ApcOptimizer.Implementation.OptimizerPasses.BusSweep

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
verifier (`denseBFCheckCert`) re-checking every proposal.

The positions are read off the bus's interactions *rearranged into canonical access order*
(`denseBSCanon`, `BusSweep.lean`), which the order-free rely certifies via `denseBSOrder?` — the
window's "nothing at this address in between" test is positional, so the list it runs on has to be
the certified time order rather than the export's order (`Proofs/BusSweep.lean`,
`denseBSOrder?_admissibleMemoryBus`). A bus whose interactions do not certify contributes
nothing. -/

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
    the pairs passing `denseBSMidOk` against the outer send `aS`. The strict ordering
    `q ≤ k < l < j` is load-bearing: interleaved pairs would break the entailment (countermodel in
    `Proofs/BusForward.lean`). -/
def denseBFCheckPairs (ops : DenseZModOps p) (nw : DenseNonzeroWits p)
    (setMult prevMult : ZMod p) (arr : Array (DenseBUPre p)) (aS : DenseBUPre p) (j : Nat) :
    (pairs : List (Nat × Nat)) → (q : Nat) → Bool
  | [], q => denseBSMidScan ops nw arr aS j (j - q) q
  | (k, l) :: rest, q =>
    decide (q ≤ k) && decide (k < l) && decide (l < j) &&
    (match arr[k]?, arr[l]? with
     | some ak, some al =>
       decide (ak.mult = some prevMult) && decide (al.mult = some setMult) &&
       denseBUConstsEq ak al &&
       denseBSMidScan ops nw arr aS k (k - q) q &&
       denseBSMidScan ops nw arr aS l (l - (k + 1)) (k + 1) &&
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

/-- The slot-only arms of `denseBSMidOk` (the zero-multiplicity arm is tested at the call site).
    Depends only on the two address-slot lists, so the sweep memoizes it per class pair. -/
def denseBFAddrExcl (nw : DenseNonzeroWits p) (a b : DenseBUPre p) : Bool :=
  denseBUConstsNeq a b || denseBUAffineNeq a b || denseBUTwoRootNeq a b || denseBUNonzeroNeq nw a b

/-- Positions whose address slots are syntactically identical (hash-gated). -/
def denseBFSlotsIdent : List (Option (DenseBUSlot p)) → List (Option (DenseBUSlot p)) → Bool
  | [], [] => true
  | some a :: as, some b :: bs =>
    a.eHash == b.eHash && decide (a.expr = b.expr) && denseBFSlotsIdent as bs
  | none :: as, none :: bs => denseBFSlotsIdent as bs
  | _, _ => false

/-- Intern each position's address-slot list into a class id: syntactically identical slot lists
    share a class, so their prepared records — and every `denseBFAddrExcl` verdict — coincide. -/
def denseBFClasses (arr : Array (DenseBUPre p)) : Array Nat × Nat :=
  let step := fun (acc : Array Nat × Std.HashMap UInt64 (List (Nat × List (Option (DenseBUSlot p)))) × Nat)
      (a : DenseBUPre p) =>
    let (ids, tbl, n) := acc
    let h := a.slots.foldl (fun acc so =>
      mixHash acc (match so with | some s => s.eHash | none => 13)) 7
    let bucket := tbl.getD h []
    match bucket.find? (fun e => denseBFSlotsIdent e.2 a.slots) with
    | some e => (ids.push e.1, tbl, n)
    | none => (ids.push n, tbl.insert h ((n, a.slots) :: bucket), n + 1)
  let (ids, _, n) := arr.foldl step (#[], ∅, 0)
  (ids, n)

/-- An open forwarding window: the send's prepared record, position and address class, the pending
    unmatched receive of a forwarding pair (if any), the closed pairs (in reverse), and the slots
    every closed pair has preserved so far. -/
structure DenseBFWin (p : ℕ) where
  pre : DenseBUPre p
  i : Nat
  cls : Nat
  pending : Option (DenseBUPre p × Nat)
  pairs : List (Nat × Nat)
  mask : List Nat

/-- One message against one window: keep unchanged (excluded), keep updated (pending formed or
    pair closed), drop, or emit a proposal. `keepSame` lets the sweep skip the map re-insert. -/
inductive DenseBFStep (p : ℕ) where
  | keepSame
  | keep (w : DenseBFWin p)
  | drop
  | propose (prop : Nat × List (Nat × Nat) × Nat)

/-- `nCls`/`mcls` and `memo` memoize the `denseBSMidOk` slot arms per (window, message) class
    pair; the verdict equals the unmemoized test, so the proposals are unchanged. -/
def denseBFStep (ops : DenseZModOps p) (nw : DenseNonzeroWits p) (setMult prevMult : ZMod p)
    (bis : Array (BusInteraction (DenseExpr p))) (mb : BusInteraction (DenseExpr p))
    (mp : DenseBUPre p) (j nCls mcls : Nat) (w : DenseBFWin p)
    (memo : Std.HashMap Nat Bool) : DenseBFStep p × Std.HashMap Nat Bool :=
  let excl : Unit → Bool × Std.HashMap Nat Bool := fun _ =>
    if decide (mp.mult = some ops.zero) then (true, memo)
    else
      let key := w.cls * nCls + mcls
      match memo[key]? with
      | some v => (v, memo)
      | none => let v := denseBFAddrExcl nw w.pre mp; (v, memo.insert key v)
  match w.pending with
  | none =>
    if decide (mp.mult = some prevMult) && denseBUConstsEq w.pre mp then
      -- a receive back at the window's own address: `pairs = []` is `busUnify`'s case.
      (if w.pairs.isEmpty then .drop else .propose (w.i, w.pairs.reverse, j), memo)
    else
      let (e, memo) := excl ()
      if e then (.keepSame, memo)
      else if decide (mp.mult = some prevMult) then
        (.keep { w with pending := some (mp, j) }, memo)
      else (.drop, memo)
  | some (ak, k) =>
    if decide (mp.mult = some setMult) && denseBUConstsEq ak mp then
      let mask := match bis[k]? with
        | some rb => w.mask.filter (fun t => denseBFSlotEq rb mb t)
        | none => []
      (if mask.isEmpty then .drop
       else .keep { w with pending := none, pairs := (k, j) :: w.pairs, mask := mask }, memo)
    else
      let (e, memo) := excl ()
      if e then (.keepSame, memo) else (.drop, memo)

/-- The sweep: a send opens a window; each later message updates or drops open windows per
    `denseBFStep`; a receive back at the window's own address with at least one closed pair yields
    a proposal. Windows split as in `denseBUSweep`: constant-address windows live in a map and an
    all-constant message steps only the window at its own key — against any other constant window
    it is excluded by `denseBUConstsNeq`, and it can never close a symbolic pending (syntactic
    equality would const-fold both sides), so those windows step to `.keep` unchanged. Symbolic
    windows, and every window on a symbolic message, are stepped one by one. -/
def denseBFSweep (ops : DenseZModOps p) (nw : DenseNonzeroWits p) (setMult prevMult : ZMod p)
    (shape : MemoryBusShape) (bis : Array (BusInteraction (DenseExpr p)))
    (arr : Array (DenseBUPre p)) (cls : Array Nat) (nCls : Nat) :
    (fuel j : Nat) →
    (constOpen : Std.HashMap (DenseAddrKey p) (DenseBFWin p)) →
    (symOpen : List (DenseBFWin p)) →
    (memo : Std.HashMap Nat Bool) →
    (out : List (Nat × List (Nat × Nat) × Nat)) → List (Nat × List (Nat × Nat) × Nat)
  | 0, _, _, _, _, out => out
  | fuel + 1, j, constOpen, symOpen, memo, out =>
    match arr[j]?, bis[j]? with
    | some mp, some mb =>
      let mcls := cls[j]?.getD 0
      let step := denseBFStep ops nw setMult prevMult bis mb mp j nCls mcls
      let (constOpen, memo, out) :=
        if mp.allConst then
          match mp.key with
          | some k =>
            match constOpen[k]? with
            | some w =>
              match step w memo with
              | (.keepSame, memo) => (constOpen, memo, out)
              | (.keep w', memo) => (constOpen.insert k w', memo, out)
              | (.drop, memo) => (constOpen.erase k, memo, out)
              | (.propose pr, memo) => (constOpen.erase k, memo, pr :: out)
            | none => (constOpen, memo, out)
          | none => (constOpen, memo, out)
        else
          -- updates and drops are applied after the fold, once `toList`'s borrow is released,
          -- so the map is mutated in place rather than copied per touched window.
          let (upds, drops, memo, out) :=
            constOpen.toList.foldl (init := (([] : List (DenseAddrKey p × DenseBFWin p)),
                ([] : List (DenseAddrKey p)), memo, out)) fun acc kw =>
              match step kw.2 acc.2.2.1 with
              | (.keepSame, memo) => (acc.1, acc.2.1, memo, acc.2.2.2)
              | (.keep w', memo) => ((kw.1, w') :: acc.1, acc.2.1, memo, acc.2.2.2)
              | (.drop, memo) => (acc.1, kw.1 :: acc.2.1, memo, acc.2.2.2)
              | (.propose pr, memo) => (acc.1, kw.1 :: acc.2.1, memo, pr :: acc.2.2.2)
          let constOpen := drops.foldl (·.erase ·) constOpen
          (upds.foldl (fun m kw => m.insert kw.1 kw.2) constOpen, memo, out)
      let (symOpen, memo, out) :=
        if symOpen.isEmpty then (symOpen, memo, out) else
        symOpen.foldr (init := (([] : List (DenseBFWin p)), memo, out)) fun w acc =>
          match step w acc.2.1 with
          | (.keepSame, memo) => (w :: acc.1, memo, acc.2.2)
          | (.keep w', memo) => (w' :: acc.1, memo, acc.2.2)
          | (.drop, memo) => (acc.1, memo, acc.2.2)
          | (.propose pr, memo) => (acc.1, memo, pr :: acc.2.2)
      -- a same-key send steps the old window to `.drop` above, so the slot is already free.
      let (constOpen, symOpen) :=
        if decide (mp.mult = some setMult) then
          match mp.key with
          | some k =>
            let w : DenseBFWin p :=
              { pre := mp, i := j, cls := mcls, pending := none, pairs := [],
                mask := (List.range mb.payload.length).filter
                  (fun t => decide (t ∉ shape.addressFields)) }
            if k.allConst then (constOpen.insert k w, symOpen)
            else (constOpen, w :: symOpen)
          | none => (constOpen, symOpen)
        else (constOpen, symOpen)
      denseBFSweep ops nw setMult prevMult shape bis arr cls nCls fuel (j + 1) constOpen symOpen
        memo out
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

/-- The entailed value-forwarding equalities of one bus with a declared ts slot: prepare, certify a
    pairing into canonical access order, sweep that order, verify. -/
def denseBFForBus (bs : BusSemantics p) (facts : BusFacts p bs) (ops : DenseZModOps p)
    (T : DenseTwoRootMap p) (nw : DenseNonzeroWits p) (shape : MemoryBusShape) (tsField B : Nat)
    (allBis : List (BusInteraction (DenseExpr p))) (idx : DenseBUIdx)
    (bisL : List (BusInteraction (DenseExpr p))) : List (DenseExpr p) :=
  let setMult := denseSetNewMult ops shape
  let prevMult := denseGetPreviousMult ops shape
  let zipped := bisL.map (fun bi => (bi, denseBUPrep shape T bi))
  match denseBSOrder? bs facts shape T setMult prevMult tsField B allBis idx zipped with
  | none => []
  | some ps =>
    let bis := (denseBSCanon shape T bisL ps).toArray
    let arr := bis.map (denseBUPrep shape T)
    let (cls, nCls) := denseBFClasses arr
    let props := denseBFSweep ops nw setMult prevMult shape bis arr cls nCls arr.size 0 ∅ [] ∅ []
    denseBFCollect ops nw setMult prevMult shape bis arr props

/-- A bus without a declared ts slot (`facts.memTsField`) contributes nothing: the canonical-order
    certificate the positional window test rests on needs one. -/
def denseBFEqsOf (bs : BusSemantics p) (facts : BusFacts p bs)
    (busLists : List (Nat × MemoryBusShape × List (BusInteraction (DenseExpr p))))
    (d : DenseConstraintSystem p) : List (DenseExpr p) :=
  let T := denseBUTable busLists d
  let nw := denseBUWits d
  let idx := denseBUBuildIdx bs facts d.busInteractions
  (busLists.map (fun sl =>
    match facts.memTsField sl.1 with
    | some (tsField, B) =>
      denseBFForBus bs facts denseZModOps T nw sl.2.1 tsField B d.busInteractions idx sl.2.2
    | none => [])).flatten

def denseBFEqs (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    List (DenseExpr p) :=
  let busLists := denseBUBusLists facts.memShape d.busInteractions
  if busLists.isEmpty then [] else denseBFEqsOf bs facts busLists d

/-- The constraints `denseBusForwardF` appends, minus those identically zero or already present. -/
def denseBusForwardNewCs (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : List (DenseExpr p) :=
  let eqs := denseBFEqs bs facts d
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
