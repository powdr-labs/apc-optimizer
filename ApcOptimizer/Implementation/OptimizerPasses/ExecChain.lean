import ApcOptimizer.Implementation.OptimizerPasses.BusUnify

set_option autoImplicit false

/-! # Chain unification on a designated-entry bus (runtime transform for `execChain`)

Adds the payload-copy equalities a *chain* bus entails: an execution bridge, where access `i`
receives `(pc i, ts i)` and sends `(pc (i+1), ts i + δ)`. The rely is `entryKeyed` (ENTRY_KEY —
`facts.memEntryKey`, the record entering the block carries the block's entry pc) plus TS_BOUND
(`facts.memTsField`), consumed through `entryKeyed_chain_copies`
(`Implementation/MemoryBusChain.lean`). Nothing about the interaction list's order is trusted; the
list order only *proposes* the chain, which the certificate re-checks on the key slot.

For a block `pc₀, pc₀+4, …`, unifying the interior pairs yields `ts_{i+1} = ts_i + δ_i`; `gauss`
then substitutes the chain, which is what brings every instruction's memory timestamps onto one base
and lets `busUnify` forward memory across instructions.

The certificate per bus (`denseECGroup?`): every interaction classifies against the group leader
(reusing `denseBUSplit`), the fibers pair up, each access's send ts slot exceeds its own receive's by
a positive constant `< B` (`denseECStepOk`), and the receives' key slots are constants that strictly
increase, start at the declared entry key, and are carried by the previous send
(`denseECKeysOk`). -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- The constant value of an interaction's key slot, if it has one. -/
def denseECKey (slot : Nat) (bi : BusInteraction (DenseExpr p)) : Option (ZMod p) :=
  (bi.payload[slot]?).bind DenseExpr.constValue?

/-- The receives' key-slot constants, in order; `none` if any is not a constant. -/
def denseECKeys (slot : Nat) :
    List (BusInteraction (DenseExpr p)) → Option (List (ZMod p))
  | [] => some []
  | R :: rest =>
    match denseECKey slot R, denseECKeys slot rest with
    | some k, some ks => some (k :: ks)
    | _, _ => none

/-- One access: the send's ts slot is the receive's plus a positive constant `< B`, so under
    TS_BOUND the receive's ts *value* is below its own send's (`denseECStepOk_sound`). -/
def denseECStepOk (tsField B : Nat) (S R : BusInteraction (DenseExpr p)) : Bool :=
  match denseBUTsLin tsField S, denseBUTsLin tsField R with
  | some LS, some LR =>
    let N := (LS.add (LR.scale (-1))).norm
    N.terms.isEmpty && decide (1 ≤ N.const.val) && decide (N.const.val < B)
  | _, _ => false

/-- The chain certificate on the key slot: the receives carry constant keys that strictly increase
    (hence are pairwise distinct — only the *first* can be the entry key), the first is the declared
    entry key, and send `i` carries receive `i + 1`'s key. The last send is unconstrained: its key
    is the block's exit target, which need not be a constant. -/
def denseECKeysOk (slot : Nat) (key : ZMod p)
    (sends recvs : List (BusInteraction (DenseExpr p))) : Bool :=
  match denseECKeys slot recvs with
  | none => false
  | some ks =>
    match ks.head? with
    | none => false
    | some k0 =>
      decide (k0 = key)
      && decide (List.IsChain (· < ·) (ks.map (fun k => k.val)))
      && (sends.zip ks.tail).all (fun sk => decide (denseECKey slot sk.1 = some sk.2))

/-- Verify the chain on one bus: everything on it classifies against the leader (source-order
    head), the fibers pair up (`#sends = #recvs ≥ 2`), each access steps its timestamp, and the key
    slots chain. Returns the member sends and receives in source order. -/
def denseECGroup? (nw : DenseNonzeroWits p) (setMult prevMult : ZMod p) (tsField B slot : Nat)
    (key : ZMod p) (zipped : List (BusInteraction (DenseExpr p) × DenseBUPre p)) :
    Option (List (BusInteraction (DenseExpr p)) × List (BusInteraction (DenseExpr p))) :=
  match zipped[0]? with
  | none => none
  | some lp =>
    if decide (2 ^ 30 < p) && decide (B ≤ 2 ^ 29) then
      match denseBUSplit nw setMult prevMult lp.2 zipped with
      | some (sends, recvs) =>
        if decide (2 ≤ sends.length) && decide (sends.length = recvs.length)
            && denseECKeysOk slot key sends recvs
            && (sends.zip recvs).all (fun sr => denseECStepOk tsField B sr.1 sr.2)
        then some (sends, recvs)
        else none
      | none => none
    else none

/-- The entailed equalities of one chain bus: interior receive `i` copies send `i − 1`, exactly the
    pairing `denseBUGroupEqs` builds. -/
def denseECForBus (ops : DenseZModOps p) (T : DenseTwoRootMap p) (nw : DenseNonzeroWits p)
    (shape : MemoryBusShape) (tsField B slot : Nat) (key : ZMod p)
    (bisL : List (BusInteraction (DenseExpr p))) : List (DenseExpr p) :=
  match denseECGroup? nw (denseSetNewMult ops shape) (denseGetPreviousMult ops shape)
      tsField B slot key (bisL.map (fun bi => (bi, denseBUPrep shape T bi))) with
  | some (sends, recvs) => denseBUGroupEqs shape sends recvs
  | none => []

/-- The equalities every declared chain bus contributes. A bus without both a declared entry key
    (`facts.memEntryKey`) and a declared ts slot (`facts.memTsField`) contributes nothing. -/
def denseECEqsOf (bs : BusSemantics p) (facts : BusFacts p bs)
    (busLists : List (Nat × MemoryBusShape × List (BusInteraction (DenseExpr p))))
    (d : DenseConstraintSystem p) : List (DenseExpr p) :=
  let T := denseBUTable busLists d
  let nw := denseBUWits d
  (busLists.map (fun sl =>
    match facts.memEntryKey sl.1, facts.memTsField sl.1 with
    | some (slot, key), some (tsField, B) =>
      denseECForBus denseZModOps T nw sl.2.1 tsField B slot key sl.2.2
    | _, _ => [])).flatten

def denseECEqs (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    List (DenseExpr p) :=
  let busLists := denseBUBusLists facts.memShape d.busInteractions
  if busLists.isEmpty then [] else denseECEqsOf bs facts busLists d

/-- The constraints `denseExecChainF` appends: the chain's copy equalities, minus those that are
    identically zero or already present. -/
def denseExecChainNewCs (bs : BusSemantics p) (facts : BusFacts p bs)
    (d : DenseConstraintSystem p) : List (DenseExpr p) :=
  let eqs := denseECEqs bs facts d
  if eqs.isEmpty then [] else denseBUFilterNew d eqs

/-- On a chain bus (a VM's execution bridge), each instruction's received CPU state is the previous
    instruction's sent state, so this adds the entailed slot equalities — for OpenVM,
    `pc_{i+1} = pc_i + 4` and `ts_{i+1} = ts_i + δ_i`, the timestamp chain the rest of the pipeline
    needs to forward memory across instructions. Justified order-free via
    `entryKeyed_chain_copies`. -/
def denseExecChainF (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    DenseConstraintSystem p :=
  if (1 : ZMod p) ≠ 0 then
    let new := denseExecChainNewCs bs facts d
    if new.isEmpty then d
    else { d with algebraicConstraints := d.algebraicConstraints ++ new }
  else d

end ApcOptimizer.Dense
