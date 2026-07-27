import ApcOptimizer.Implementation.OptimizerPasses.BusPairCancelIndex
import ApcOptimizer.Implementation.OptimizerPasses.BusPairCancelLive
import ApcOptimizer.Implementation.OptimizerPasses.AddrDiseqPre

set_option autoImplicit false

/-! # Dense region tests + emitted-check acceptance for `busPairCancel`

The receive scan (`denseFirstMatchAt`), address-disequality refutation
(`denseMidRefuted`/`densePreRefuted`/`denseProvRecv`), the shield scan (`denseShieldOk`), emitted
byte checks (`denseMkByteCheck`/`denseMkBytePair`), and the per-candidate acceptance test
(`denseCheckCancel`). Impl-only; soundness in `Proofs/BusPairCancelCheck.lean`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- The first indexed position after `i` on `busId` whose payload matches `S.payload` among still
    **live** positions (ascending); tombstoned positions are skipped, so it is the first live match. -/
def denseFirstMatchAt (M : Thunk (DenseEqConstraintMap p)) (arr : Array (BusInteraction (DenseExpr p)))
    (alive : Array Bool)
    (busId : Nat) (S : BusInteraction (DenseExpr p)) (i : Nat) : List Nat → Option Nat
  | [] => none
  | j :: rest =>
    if decide (i < j) && alive[j]?.getD false then
      match arr[j]? with
      | some R =>
        if decide (R.busId = busId) && densePayloadEntailedEq M S.payload R.payload then some j
        else denseFirstMatchAt M arr alive busId S i rest
      | none => denseFirstMatchAt M arr alive busId S i rest
    else denseFirstMatchAt M arr alive busId S i rest

/-- Refute `m` as an active same-address message on `busId` (the "between" region test). The two-root
    disequality (`denseAddrTwoRootNeq`) lets it step over interleaved accesses whose addresses are
    pointer expressions rather than constants. -/
def denseMidRefuted (ops : DenseZModOps p) (shape : MemoryBusShape)
    (T : Thunk (DenseAddrCerts p)) (busId : Nat)
    (S m : BusInteraction (DenseExpr p)) : Bool :=
  decide (m.busId ≠ busId) || decide (denseMultConst m = some ops.zero) || denseAddrConstsNeq shape S m
    || denseAddrAffineNeq shape S m || denseAddrTwoRootNeq shape T.get.tworoot S m
    || denseAddrNonzeroNeq shape T.get.nonzero S m

/-- Refute `m` as an active same-address *send* on `busId` (the "before" region test:
    earliest-send). -/
def densePreRefuted (ops : DenseZModOps p) (shape : MemoryBusShape)
    (T : Thunk (DenseAddrCerts p)) (busId : Nat)
    (S m : BusInteraction (DenseExpr p)) : Bool :=
  denseMidRefuted ops shape T busId S m ||
    (match denseMultConst m with
     | some c => decide (c ≠ denseSetNewMult ops shape)
     | none => false)

/-- `m` is a *provable* active same-address receive on `busId`: on-bus, constant `-1`
    multiplicity, and a constant address equal to `S`'s. -/
def denseProvRecv (ops : DenseZModOps p) (shape : MemoryBusShape) (busId : Nat)
    (S m : BusInteraction (DenseExpr p)) : Bool :=
  decide (m.busId = busId) && denseAddrConstsEq shape S m &&
    decide (denseMultConst m = some (denseGetPreviousMult ops shape))

/-- Single right-to-left pass returning `(hasRecvSoFar, ok)`: `hasRecvSoFar` is whether the tail
    processed so far (everything to the right) contains a provable active same-address receive; `ok`
    is whether every not-`densePreRefuted` message so far is followed by such a receive. O(n). -/
def denseShieldScan (ops : DenseZModOps p) (shape : MemoryBusShape)
    (T : Thunk (DenseAddrCerts p)) (busId : Nat)
    (S : BusInteraction (DenseExpr p)) :
    List (BusInteraction (DenseExpr p)) → Bool × Bool
  | [] => (false, true)
  | m0 :: rest =>
    let r := denseShieldScan ops shape T busId S rest
    (r.1 || denseProvRecv ops shape busId S m0,
      r.2 && (densePreRefuted ops shape T busId S m0 || r.1))

/-- The *shield* check on the before-region: every message that is **not** provably a
    non-(active-same-address-send) (`¬densePreRefuted`) is followed by a provable active
    same-address receive (`denseProvRecv`). Computed in one O(n) pass (`denseShieldScan`). -/
def denseShieldOk (ops : DenseZModOps p) (shape : MemoryBusShape)
    (T : Thunk (DenseAddrCerts p)) (busId : Nat)
    (S : BusInteraction (DenseExpr p)) (l : List (BusInteraction (DenseExpr p))) : Bool :=
  (denseShieldScan ops shape T busId S l).2

/-- `denseShieldScan` with the two per-message tests abstracted. -/
def denseShieldScanW {α : Type} (P Q : α → Bool) : List α → Bool × Bool
  | [] => (false, true)
  | m0 :: rest =>
    let r := denseShieldScanW P Q rest
    (r.1 || Q m0, r.2 && (P m0 || r.1))

theorem denseShieldScanW_eq (ops : DenseZModOps p) (shape : MemoryBusShape)
    (T : Thunk (DenseAddrCerts p)) (busId : Nat) (S : BusInteraction (DenseExpr p)) :
    ∀ l, denseShieldScanW (densePreRefuted ops shape T busId S)
        (denseProvRecv ops shape busId S) l = denseShieldScan ops shape T busId S l := by
  intro l
  induction l with
  | nil => rfl
  | cons m0 rest ih => rw [denseShieldScanW, denseShieldScan, ih]

/-- `denseShieldScanW` over a derived per-position array (prepared certificate records), reading
    the prepared record at each live position. -/
def denseShieldScanSegP {α : Type} (P Q : α → Bool) (preArr : Array α) (alive : Array Bool) :
    (lo n : Nat) → Bool × Bool
  | _, 0 => (false, true)
  | lo, n + 1 =>
    let r := denseShieldScanSegP P Q preArr alive (lo + 1) n
    if alive[lo]?.getD false then
      match preArr[lo]? with
      | some m0 => (r.1 || Q m0, r.2 && (P m0 || r.1))
      | none => r
    else r

theorem denseShieldScanSegP_eq {α : Type} (f : BusInteraction (DenseExpr p) → α)
    (P Q : α → Bool) (arr : Array (BusInteraction (DenseExpr p))) (alive : Array Bool) :
    ∀ (lo n : Nat),
      denseShieldScanSegP P Q (arr.map f) alive lo n
        = denseShieldScanW (fun m => P (f m)) (fun m => Q (f m))
            (denseLiveSeg arr alive lo n) := by
  intro lo n
  induction n generalizing lo with
  | zero => rfl
  | succ n ih =>
      rw [denseShieldScanSegP, ih (lo + 1), Array.getElem?_map]
      cases halive : alive[lo]?.getD false with
      | false => rw [denseLiveSeg_skip arr alive lo n halive, if_neg (by simp)]
      | true =>
          rw [if_pos rfl]
          cases harr : arr[lo]? with
          | some m0 =>
              rw [denseLiveSeg_peel arr alive lo n m0 halive harr]
              rfl
          | none =>
              rw [denseLiveSeg, halive, harr, if_pos rfl]
              simp

/-! ## The region tests on prepared records (`AddrDiseqPre.lean`) -/

def denseMidRefutedP (ops : DenseZModOps p) (nw : DenseNonzeroWits p) (busId : Nat)
    (a b : DenseAddrPre p) : Bool :=
  decide (b.busId ≠ busId) || decide (b.mult.get = some ops.zero) || denseAddrConstsNeqP a b
    || denseAddrAffineNeqP a b || denseAddrTwoRootNeqP a b || denseAddrNonzeroNeqP nw a b

theorem denseMidRefutedP_eq (ops : DenseZModOps p) (shape : MemoryBusShape)
    (T : Thunk (DenseAddrCerts p)) (busId : Nat) (S m : BusInteraction (DenseExpr p)) :
    denseMidRefutedP ops T.get.nonzero busId (denseAddrPrep shape T.get.tworoot S)
        (denseAddrPrep shape T.get.tworoot m)
      = denseMidRefuted ops shape T busId S m := by
  unfold denseMidRefutedP denseMidRefuted
  rw [denseAddrConstsNeqP_eq, denseAddrAffineNeqP_eq, denseAddrTwoRootNeqP_eq,
    denseAddrNonzeroNeqP_eq]
  rfl

def densePreRefutedP (ops : DenseZModOps p) (nw : DenseNonzeroWits p) (busId : Nat)
    (setMult : ZMod p) (a b : DenseAddrPre p) : Bool :=
  denseMidRefutedP ops nw busId a b ||
    (match b.mult.get with
     | some c => decide (c ≠ setMult)
     | none => false)

theorem densePreRefutedP_eq (ops : DenseZModOps p) (shape : MemoryBusShape)
    (T : Thunk (DenseAddrCerts p)) (busId : Nat) (S m : BusInteraction (DenseExpr p)) :
    densePreRefutedP ops T.get.nonzero busId (denseSetNewMult ops shape)
        (denseAddrPrep shape T.get.tworoot S) (denseAddrPrep shape T.get.tworoot m)
      = densePreRefuted ops shape T busId S m := by
  unfold densePreRefutedP densePreRefuted
  rw [denseMidRefutedP_eq]
  rfl

def denseProvRecvP (busId : Nat) (getPrevMult : ZMod p) (a b : DenseAddrPre p) : Bool :=
  decide (b.busId = busId) && denseAddrConstsEqP a b && decide (b.mult.get = some getPrevMult)

theorem denseProvRecvP_eq (ops : DenseZModOps p) (shape : MemoryBusShape)
    (T : DenseTwoRootMap p) (busId : Nat) (S m : BusInteraction (DenseExpr p)) :
    denseProvRecvP busId (denseGetPreviousMult ops shape) (denseAddrPrep shape T S)
        (denseAddrPrep shape T m)
      = denseProvRecv ops shape busId S m := by
  unfold denseProvRecvP denseProvRecv
  rw [denseAddrConstsEqP_eq]
  rfl

/-- Single-value byte check on `e`, emitted through `spec` (multiplicity `1`). -/
def denseMkByteCheck (spec : ByteXorSpec p) (busId : Nat) (e : DenseExpr p) :
    BusInteraction (DenseExpr p) :=
  { busId := busId, multiplicity := .const 1,
    payload := spec.encode (.const spec.xorOp) e e (.const 0) }

/-- Packed pair byte check on `(e₁, e₂)`, emitted through `spec` (multiplicity `1`). -/
def denseMkBytePair (spec : ByteXorSpec p) (busId : Nat) (e₁ e₂ : DenseExpr p) :
    BusInteraction (DenseExpr p) :=
  { busId := busId, multiplicity := .const 1,
    payload := spec.encode (.const spec.pairOp) e₁ e₂ (.const 0) }

/-- Certificate that an emitted check faithfully carries `R`'s byte obligation: on a `byteXorSpec`
    bus (bound `256`), multiplicity 1, self-check payload `(xorOp, e, e, 0)` for an `e` that is a
    declared byte slot of `R`. -/
def denseEmitOk (ops : DenseZModOps p) (bs : BusSemantics p) (facts : BusFacts p bs)
    (busId : Nat) (shape : MemoryBusShape) (slots : List Nat)
    (R ck : BusInteraction (DenseExpr p)) : Bool :=
  match facts.byteXorSpec ck.busId with
  | none => false
  | some spec =>
    decide (spec.bound = 256) &&
    decide (ck.multiplicity = (.const ops.one : DenseExpr p)) &&
    (match spec.decode ck.payload with
     | some (op, o1, o2, r) =>
       decide (op = (.const spec.xorOp : DenseExpr p)) && decide (o1 = o2) &&
       decide (r = (.const ops.zero : DenseExpr p)) &&
       slots.any (fun slot =>
         decide (R.payload[slot]? = some o1) &&
         (match facts.slotBound busId (denseGetPreviousMult ops shape)
              (R.payload.map DenseExpr.constValue?) slot with
          | some b => decide (b ≤ 256)
          | none => false))
     | none => false)

/-- The declared byte slots of `R` whose payload entries the witnesses do not justify. -/
def denseUnjustifiedSlots (bound : Nat) (deep : Bool)
    (domIdx : Std.HashMap VarId (List (DenseExpr p)))
    (candsOf : VarId → List (DenseExpr p)) (bs : BusSemantics p)
    (facts : BusFacts p bs) (wits fwits : VarId → List (BusInteraction (DenseExpr p)))
    (slots : List Nat) (R : BusInteraction (DenseExpr p)) : List Nat :=
  slots.filter (fun slot =>
    match R.payload[slot]? with
    | some e => !denseByteJustifiedW bound deep domIdx candsOf bs facts wits fwits e
    | none => false)

/-- The per-candidate certificate: bus/multiplicity/payload of the pair, the emitted checks'
    certificates, and byte justification of `R`'s declared slots. The split equation and region
    tests are not re-checked here (the scan established them); the justification scan is last, so it
    only runs for already-matching candidates. -/
def denseCheckCancel (ops : DenseZModOps p) (deep : Bool) (bs : BusSemantics p)
    (facts : BusFacts p bs)
    (M : Thunk (DenseEqConstraintMap p))
    (domIdx : Std.HashMap VarId (List (DenseExpr p))) (candsOf : VarId → List (DenseExpr p))
    (wits fwits : VarId → List (BusInteraction (DenseExpr p)))
    (busId : Nat) (shape : MemoryBusShape) (slots : List Nat) (bound : Nat)
    (S R : BusInteraction (DenseExpr p))
    (checks : List (BusInteraction (DenseExpr p))) : Bool :=
  decide (S.busId = busId) && decide (R.busId = busId) &&
  decide (denseMultConst S = some (denseSetNewMult ops shape)) &&
    decide (denseMultConst R = some (denseGetPreviousMult ops shape)) &&
  densePayloadEntailedEq M S.payload R.payload &&
  checks.all (denseEmitOk ops bs facts busId shape slots R) &&
  denseRecvSlotsJustified bound deep domIdx candsOf bs facts wits fwits slots R

end ApcOptimizer.Dense
