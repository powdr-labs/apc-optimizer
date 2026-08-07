import ApcOptimizer.Implementation.OptimizerPasses.DomainTable

set_option autoImplicit false

/-! # The `domainBatch` pass

Finite domains per variable — the affine roots of a constraint, a bus `slotBound` fact, a byte
operand's coset — then a box enumeration per candidate variable set, keeping every variable that
takes the same value in every surviving point as a forced constant. Soundness is
`dbDomainBatchσ_entailed` in `Proofs/DomainBatch.lean`.

The representation is built for the scan:

* every per-variable structure is an `Array` keyed by `VarId.index` (domain table, anchor buckets),
  and every fact that depends on the bus alone is resolved once per `busId` (`DbBusCache`);
* each item's distinct variable list is computed **once** and reused by the table build, the target
  list, the buckets, the dedup key and the gathers;
* the affine roots of a constraint come from a six-slot accumulator, not a `DenseLinExpr`;
* a scan reads the system's own expressions against a `VarId.index`-keyed register file of
  `ZMod.val`s, so it neither compiles nor allocates a point: the box loop writes one register per
  step and the candidate mask is a value array plus an alive flag array with a live count, so the
  abort test is O(1);
* the box is enumerated largest-domain-outermost and each item is tested at the depth of its
  innermost key, so a failure prunes a whole subtree;
* a `.coset` domain arm streams a byte operand's coset in the field with one hoisted inverse. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-! ## Domains

The scan works on `ZMod p` values in their `ZMod.val` representation — a plain `Nat` below `p` —
so a point costs machine arithmetic instead of a `p`-match plus a `Fin` reconstruction per
operation. `DbDom` therefore stores `Nat`s; `zmodOfNatP` maps back at the boundary. -/

/-- A finite domain: explicit values, `[0, bound)`, or the `bound`-element coset
    `{(v + negB) * aInv : v < bound}` (a byte operand's entailed domain, never materialized).
    Every value is a `ZMod.val`. -/
inductive DbDom where
  | explicit (vals : Array Nat)
  | range (bound : Nat)
  | coset (bound : Nat) (negB aInv : Nat)
deriving Inhabited

@[inline] def DbDom.size : DbDom → Nat
  | .explicit vs => vs.size
  | .range b => b
  | .coset b _ _ => b

/-- `(n : ZMod p)`, dictionary-free (mirrors `zmodOneP`). -/
def zmodOfNatP : ∀ (p : ℕ), Nat → ZMod p
  | 0, n => ((n : ℤ) : ZMod 0)
  | m + 1, n => (⟨n % (m + 1), Nat.mod_lt _ (Nat.succ_pos m)⟩ : Fin (m + 1))

/-- `a + b` on `val`s: both are below `p`, so the sum needs a conditional subtraction rather than
    the division `Fin.add` performs. -/
@[inline] def dbAddN (p a b : Nat) : Nat := let s := a + b; if s < p then s else s - p

@[inline] def dbMulN (p a b : Nat) : Nat := a * b % p

/-- The `i`-th element of a domain, in `toList` order. The index is a position in a domain of at
    most `maxEnumSize` elements, so the reduction is a comparison rather than a division. -/
@[inline] def DbDom.at (p : ℕ) (d : DbDom) (i : Nat) : Nat :=
  match d with
  | .explicit vs => vs.getD i 0
  | .range _ => if i < p then i else i % p
  | .coset _ negB aInv =>
    dbMulN p (dbAddN p (if i < p then i else i % p) negB) aInv

/-- Elements of a coset domain, with early exit; the other two arms need no iteration. -/
def dbCosetIterN {β : Type} (p : ℕ) (f : β → Nat → β) (stop : β → Bool) (negB aInv cur : Nat) :
    Nat → β → β
  | 0, acc => acc
  | n + 1, acc =>
    if stop acc then acc
    else dbCosetIterN p f stop negB aInv ((cur + 1 % p) % p) n (f acc (dbMulN p ((cur + negB) % p) aInv))

/-- The single value the domain admits, or `none` (`denseDomainConstantValueV?`). -/
def DbDom.const? (p : ℕ) (d : DbDom) : Option Nat :=
  match d with
  | .explicit vs =>
    match vs[0]? with
    | none => none
    | some v => if vs.all (fun w => w == v) then some v else none
  | .range b => if b == 1 then some 0 else none
  | .coset b negB aInv => if b == 1 then some (dbMulN p negB aInv) else none

/-- Every element is `< bound` as a `Nat` (`denseDomainBelowV`). -/
def DbDom.below (p : ℕ) (d : DbDom) (bound : Nat) : Bool :=
  match d with
  | .explicit vs => vs.all (fun v => decide (v < bound))
  | .range b => decide (b ≤ bound)
  | .coset b negB aInv =>
    dbCosetIterN p (fun acc v => acc && decide (v < bound)) (fun acc => !acc) negB aInv 0 b true

/-! ## Items

An item is a system expression read against a `VarId.index`-keyed register file of `ZMod.val`s: the
scan evaluates `DenseExpr` directly, so selecting an item allocates nothing (a compiled tree would
copy every node of every constraint, once per invocation). `ZMod.val` at a `const` leaf is a match
on `p` and a projection. -/

def dbEval (p : ℕ) (regs : Array Nat) : DenseExpr p → Nat
  | .const c => c.val
  | .var i => regs.getD i.index 0
  | .add a b => dbAddN p (dbEval p regs a) (dbEval p regs b)
  | .mul a b => dbMulN p (dbEval p regs a) (dbEval p regs b)

/-- One gathered item's per-point obligation; the bus arms mirror `DenseCBiPred`. -/
inductive DbItem (p : ℕ) where
  | zero (e : DenseExpr p)
  | always
  | varRange (mult x width : DenseExpr p)
  | varRangeConst (mult x : DenseExpr p) (bound : Nat)
  | tupleRange (mult x y : DenseExpr p) (boundX boundY : Nat)
  | fixedRange (mult value : DenseExpr p) (bound : Nat)
  | byte (mult o1 o2 result : DenseExpr p) (bound : Nat) (kind : DenseBytePredKind)
  | fallback (busId : Nat) (mult : DenseExpr p) (payload : List (DenseExpr p))

def dbByteRel (kind : DenseBytePredKind) (a b r : Nat) : Bool :=
  match kind with
  | .xor => decide (r = Nat.xor a b)
  | .pair => r == 0
  | .or => decide (r = Nat.lor a b)
  | .and => decide (r = Nat.land a b)

def dbItemOk {bs : BusSemantics p} (facts : BusFacts p bs) (regs : Array Nat) :
    DbItem p → Bool
  | .zero e => dbEval p regs e == 0
  | .always => true
  | .varRange mult x width =>
    if dbEval p regs mult == 0 then true
    else
      let w := dbEval p regs width
      decide (w ≤ 17) && decide (dbEval p regs x < 2 ^ w)
  | .varRangeConst mult x bound =>
    if dbEval p regs mult == 0 then true
    else decide (dbEval p regs x < bound)
  | .tupleRange mult x y boundX boundY =>
    if dbEval p regs mult == 0 then true
    else decide (dbEval p regs x < boundX) && decide (dbEval p regs y < boundY)
  | .fixedRange mult value bound =>
    if dbEval p regs mult == 0 then true
    else decide (dbEval p regs value < bound)
  | .byte mult o1 o2 result bound kind =>
    if dbEval p regs mult == 0 then true
    else
      let a := dbEval p regs o1
      let b := dbEval p regs o2
      decide (a < bound) && decide (b < bound) && dbByteRel kind a b (dbEval p regs result)
  | .fallback busId mult payload =>
    let m := dbEval p regs mult
    if m == 0 then true
    else
      facts.acceptsDec
        { busId := busId, multiplicity := zmodOfNatP p m,
          payload := payload.map (fun t => zmodOfNatP p (dbEval p regs t)) }

/-- Every gathered item whose level is `d` — the depth of the innermost key it mentions, so its
    registers are already bound when the box loop reaches that depth. -/
def dbAllOkLev {bs : BusSemantics p} (facts : BusFacts p bs) (items : Array (DbItem p))
    (ilev : Array Nat) (d : Nat) (regs : Array Nat) (i : Nat) : Bool :=
  if h : i < items.size then
    if ilev.getD i 0 == d then
      (if dbItemOk facts regs items[i] then dbAllOkLev facts items ilev d regs (i + 1) else false)
    else dbAllOkLev facts items ilev d regs (i + 1)
  else true
  termination_by items.size - i
  decreasing_by all_goals omega

/-! ### Per-interaction data, computed once

Every `BusFacts` query about an interaction is resolved here, once, and read by the three consumers
that used to each ask again: the byte-domain phase, the item compiler and the domain-redundancy
test. `spec.decode` in particular allocates and was run three times per interaction. -/

/-- An interaction's byte-bus view: the spec, the op selector's constant value, and the decoded
    logical operands. -/
structure DbBytePre (p : ℕ) where
  spec : ByteXorSpec p
  op? : Option (ZMod p)
  o1 : DenseExpr p
  o2 : DenseExpr p
  result : DenseExpr p

/-- The constant multiplicity, the constant-slot pattern, the distinct variables, the stateless
    flag and the resolved bus facts of one interaction. Built once and never rewritten:
    `denseBiInformative`'s verdict rides alongside in its own array, so the slot-bound phase
    does not rebuild this record per interaction. -/
structure DbBiPre (p : ℕ) where
  mult? : Option (ZMod p)
  pat : List (Option (ZMod p))
  vars : Array VarId
  usable : Bool
  byte? : Option (DbBytePre p)
  varRange : Bool
  tuple? : Option (Nat × Nat)
  rangeAt? : Option (Nat × Nat)

def dbBiPreEmpty : DbBiPre p := ⟨none, [], #[], false, none, false, none, none⟩

/-- Every fact that depends on the bus alone, keyed by `busId`. A `BusFacts` query resolves the
    bus type through the VM's `busMap`, which is a list lookup; a system has a handful of distinct
    bus ids against hundreds of thousands of interactions. -/
structure DbBusCache (p : ℕ) where
  usable : Array Bool
  varRange : Array Bool
  tuple : Array (Option (Nat × Nat))
  byteSpec : Array (Option (ByteXorSpec p))
  alwaysOk0 : Array Bool
  neverViol : Array Bool

def dbBusCacheOf {bs : BusSemantics p} (facts : BusFacts p bs) (nb : Nat) : DbBusCache p :=
  let ids := Array.range nb
  { usable := ids.map (fun b => !bs.isStateful b)
    varRange := ids.map facts.varRangeBus
    tuple := ids.map facts.tupleRangeBus
    byteSpec := ids.map facts.byteXorSpec
    alwaysOk0 := ids.map facts.neverViolates
    neverViol := ids.map facts.neverViolates }

/-- `denseBiAlwaysOk` with the busId-only disjunct cached. -/
@[inline] def dbBiAlwaysOk {bs : BusSemantics p} (facts : BusFacts p bs) (bc : DbBusCache p)
    (bi : BusInteraction (DenseExpr p)) : Bool :=
  bc.alwaysOk0.getD bi.busId false || facts.neverViolatesArity bi.busId bi.payload.length

/-- Resolve every `BusFacts` query about one interaction. Faithfulness of the cache is
    `DbBiPreOf` (`Proofs/DomainBatch.lean`). -/
def dbPreOne {bs : BusSemantics p} (facts : BusFacts p bs) (bc : DbBusCache p)
    (bi : BusInteraction (DenseExpr p)) (vars : Array VarId) : DbBiPre p :=
  let pat := bi.payload.map DenseExpr.constValue?
  let usable := bc.usable.getD bi.busId false
  -- the width/tuple facts are consulted only on a two-slot payload, and the range fact only when
  -- neither of them answered: each is resolved exactly where its consumers can reach it
  let twoSlot := match bi.payload with | [_, _] => true | _ => false
  let varRange := usable && twoSlot && bc.varRange.getD bi.busId false
  let tuple? := if usable && twoSlot && !varRange then bc.tuple.getD bi.busId none else none
  { mult? := bi.multiplicity.constValue?
    pat
    vars
    usable
    -- read by the compiler and the pair-redundancy test (both `usable`-only) and by the
    -- byte-domain phase (nonzero constant multiplicity only)
    byte? :=
      if usable || (bi.multiplicity.constValue?).any (fun m => !zmodIsZero m) then
        (bc.byteSpec.getD bi.busId none).bind fun spec =>
          (spec.decode bi.payload).map fun t => ⟨spec, t.1.constValue?, t.2.1, t.2.2.1, t.2.2.2⟩
      else none
    varRange
    tuple?
    rangeAt? :=
      if usable && !varRange && tuple?.isNone then facts.rangeCheckAt bi.busId pat else none }

/-! ### Compiling a bus interaction (mirrors `denseCompileCBiPredV`) -/

def dbCompileRange (bi : BusInteraction (DenseExpr p)) (e : DbBiPre p) (mult : DenseExpr p) :
    Option (DbItem p) :=
  match e.mult? with
  | some m =>
    if zmodIsOne m then
      match e.rangeAt? with
      | some (slot, bound) =>
        match bi.payload[slot]? with
        | some value => some (.fixedRange mult value bound)
        | none => none
      | none => none
    else none
  | none => none

def dbCompileByte (e : DbBiPre p) (mult : DenseExpr p) : Option (DbItem p) :=
  match e.byte? with
  | none => none
  | some b =>
    match b.op? with
    | none => none
    | some opValue =>
      let spec := b.spec
      let mk : DenseBytePredKind → Option (DbItem p) := fun kind =>
        some (.byte mult b.o1 b.o2 b.result spec.bound kind)
      if opValue = spec.xorOp then mk .xor
      else if opValue = spec.pairOp then mk .pair
      else
        match spec.orOp with
        | some orOp =>
          if opValue = orOp then mk .or
          else
            match spec.andOp with
            | some andOp => if opValue = andOp then mk .and else none
            | none => none
        | none =>
          match spec.andOp with
          | some andOp => if opValue = andOp then mk .and else none
          | none => none

def dbCompileOther (bi : BusInteraction (DenseExpr p)) (e : DbBiPre p)
    (mult : DenseExpr p) : DbItem p :=
  match dbCompileRange bi e mult with
  | some item => item
  | none =>
    match dbCompileByte e mult with
    | some item => item
    | none => .fallback bi.busId mult bi.payload

def dbCompileBi {bs : BusSemantics p} (facts : BusFacts p bs) (bc : DbBusCache p)
    (bi : BusInteraction (DenseExpr p)) (e : DbBiPre p) : DbItem p :=
  if dbBiAlwaysOk facts bc bi then .always
  else
    let mult := bi.multiplicity
    match bi.payload with
    | [x, width] =>
      if e.varRange then
        match width.constValue? with
        | some widthValue =>
          if widthValue.val ≤ 17 then .varRangeConst mult x (2 ^ widthValue.val)
          else .varRange mult x width
        | none => .varRange mult x width
      else
        match e.tuple? with
        | some (boundX, boundY) =>
          .tupleRange mult x width boundX boundY
        | none => dbCompileOther bi e mult
    | _ => dbCompileOther bi e mult

/-! ## Distinct variables per item, computed once -/

def dbPushVar (acc : Array VarId) (i : VarId) : Array VarId :=
  if acc.contains i then acc else acc.push i

def dbVarsOf : DenseExpr p → Array VarId → Array VarId
  | .const _, acc => acc
  | .var i, acc => dbPushVar acc i
  | .add a b, acc => dbVarsOf b (dbVarsOf a acc)
  | .mul a b, acc => dbVarsOf b (dbVarsOf a acc)

def dbVarsOfList : List (DenseExpr p) → Array VarId → Array VarId
  | [], acc => acc
  | e :: rest, acc => dbVarsOfList rest (dbVarsOf e acc)

def dbBiVars (bi : BusInteraction (DenseExpr p)) : Array VarId :=
  dbVarsOfList bi.payload (dbVarsOf bi.multiplicity (Array.emptyWithCapacity 4))

/-! ### Membership over small variable arrays -/

def dbMemVar (b : Array VarId) (v : VarId) (k : Nat) : Bool :=
  if h : k < b.size then (b[k] == v || dbMemVar b v (k + 1)) else false
  termination_by b.size - k
  decreasing_by all_goals omega

def dbSubsetVars (a b : Array VarId) (k : Nat) : Bool :=
  if h : k < a.size then (dbMemVar b a[k] 0 && dbSubsetVars a b (k + 1)) else true
  termination_by a.size - k
  decreasing_by all_goals omega

/-- Both arrays hold distinct variables, so equal sizes plus one inclusion is set equality. -/
@[inline] def dbSameSet (a b : Array VarId) : Bool := a.size == b.size && dbSubsetVars a b 0

/-! ## Affine roots without a linear form

`dbRootsOfLin` only ever asks whether the normalized linear form of a factor is a constant or
`a·x + b` for one queried variable, and the mining runs only on constraints with at most three
distinct variables. So the form is accumulated into six `ZMod.val` slots of a uniquely-owned array
— `[ok, const, c₀, c₁, c₂, spill]`, `cⱼ` the coefficient of `vs[j]` — instead of a
`DenseLinExpr`'s term list plus a merge and a sort. `k` is the enclosing product's scale factor,
and `constValue?` decides the product arm exactly as `terms.isEmpty` does in `denseLinearize`. -/

def dbSlotOf (vs : Array VarId) (i : VarId) (k : Nat) : Nat :=
  if h : k < vs.size then (if vs[k] == i then k else dbSlotOf vs i (k + 1)) else 3
  termination_by vs.size - k
  decreasing_by all_goals omega

def dbAffAcc (vs : Array VarId) : DenseExpr p → Nat → Array Nat → Array Nat
  | .const c, k, st => st.modify 1 (fun v => dbAddN p v (dbMulN p k c.val))
  | .var i, k, st => st.modify (2 + dbSlotOf vs i 0) (fun v => dbAddN p v k)
  | .add a b, k, st => dbAffAcc vs b k (dbAffAcc vs a k st)
  | .mul a b, k, st =>
    match a.constValue? with
    | some ca => dbAffAcc vs b (dbMulN p k ca.val) st
    | none =>
      match b.constValue? with
      | some cb => dbAffAcc vs a (dbMulN p k cb.val) st
      | none => st.set! 0 0

/-- Does any coefficient other than slot `j`'s survive the merge? Slot 5 collects variables outside
    `vs`, which the caller rules out; checking all three coefficient slots keeps the reading of the
    form independent of `vs.size`. -/
@[inline] def dbOtherLive (st : Array Nat) (j : Nat) : Bool :=
  (j != 0 && st.getD 2 0 != 0) || (j != 1 && st.getD 3 0 != 0) ||
    (j != 2 && st.getD 4 0 != 0) || st.getD 5 0 != 0

/-- The roots of `c + a·x = 0`, read off the accumulated coefficients. `a = 0` with `c ≠ 0` is an
    unsatisfiable equation, whose (empty) root list is vacuously sound. -/
def dbAffRootsOf (p : ℕ) (an cn : Nat) : Option (List (ZMod p)) :=
  if an == 0 then (if cn == 0 then none else some [])
  else
    let a := zmodOfNatP p an
    let c := zmodOfNatP p cn
    -- a normalized `x - c`: the root is `c`, with no modular inverse to compute
    if zmodIsOne a then some [zmodNegP c]
    else
      let r := zmodNegP (zmodMulP a⁻¹ c)
      if zmodIsZero (zmodAddP (zmodMulP a r) c) then some [r] else none

/-- `dbRootsOfLin` on the accumulated form: the roots of `e` in `vs[j]`, seen as an affine equation
    in that variable alone. -/
def dbAffRoots (vs : Array VarId) (j : Nat) (e : DenseExpr p) : Option (List (ZMod p)) :=
  let st := dbAffAcc vs e 1 #[1, 0, 0, 0, 0, 0]
  if st.getD 0 0 == 0 || dbOtherLive st j then none
  else dbAffRootsOf p (st.getD (2 + j) 0) (st.getD 1 0)

/-- `denseRootsIn` over the product spine: the whole node first, then the union of the factors'. -/
def dbRootsAt (vs : Array VarId) (j : Nat) : DenseExpr p → Option (List (ZMod p))
  | .mul a b =>
    match dbAffRoots vs j (.mul a b) with
    | some r => some r
    | none =>
      match dbRootsAt vs j a, dbRootsAt vs j b with
      | some ra, some rb => some (ra ++ rb)
      | _, _ => none
  | e => dbAffRoots vs j e

/-! ## The domain table -/

structure DbTab (p : ℕ) where
  dom : Array (Option (DbDom))

/-- Keep the strictly smaller domain, as `DenseDomainTable.insertEntry`. -/
def DbTab.insert (T : DbTab p) (i : Nat) (d : DbDom) : DbTab p :=
  let ⟨dom⟩ := T
  match dom.getD i none with
  | some d0 => if d.size < d0.size then ⟨dom.set! i (some d)⟩ else ⟨dom⟩
  | none => ⟨dom.set! i (some d)⟩

@[inline] def DbTab.get (T : DbTab p) (i : Nat) : Option (DbDom) := T.dom.getD i none

def dbAddConstraintVars (e : DenseExpr p) (vs : Array VarId) (k : Nat) (T : DbTab p) :
    DbTab p :=
  if h : k < vs.size then
    match dbRootsAt vs k e with
    | some rs =>
      dbAddConstraintVars e vs (k + 1) (T.insert vs[k].index (.explicit (rs.map ZMod.val).toArray))
    | none => dbAddConstraintVars e vs (k + 1) T
  else T
  termination_by vs.size - k
  decreasing_by all_goals omega

def dbSlotBound {bs : BusSemantics p} (facts : BusFacts p bs) (bi : BusInteraction (DenseExpr p))
    (mult? : Option (ZMod p)) (pat : List (Option (ZMod p))) (slot : Nat) : Option Nat :=
  match mult? with
  | none => none
  | some m => if zmodIsZero m then none else facts.slotBound bi.busId m pat slot

/-- Walk the payload once: the raw-variable slots' bounds (first slot per variable, as
    `denseVarSlot`) feed both the table and `denseBiInformative`'s second disjunct. -/
def dbBusSlots {bs : BusSemantics p} (facts : BusFacts p bs) (bi : BusInteraction (DenseExpr p))
    (mult? : Option (ZMod p)) (pat : List (Option (ZMod p))) :
    List (DenseExpr p) → List (Option (ZMod p)) → Nat → Array VarId → Bool → DbTab p →
      Bool × DbTab p
  | [], _, _, _, inf, T => (inf, T)
  | e :: rest, ps, slot, seen, inf, T =>
    let pRest := ps.tail
    match e with
    | .var i =>
      if seen.contains i then dbBusSlots facts bi mult? pat rest pRest (slot + 1) seen inf T
      else
        match dbSlotBound facts bi mult? pat slot with
        | none => dbBusSlots facts bi mult? pat rest pRest (slot + 1) (seen.push i) true T
        | some bound =>
          let T := if bound ≤ maxDomainBound then T.insert i.index (.range bound) else T
          dbBusSlots facts bi mult? pat rest pRest (slot + 1) (seen.push i) inf T
    | _ =>
      -- `pat` already holds this slot's `constValue?`
      dbBusSlots facts bi mult? pat rest pRest (slot + 1) seen
        (inf || !(ps.head?.getD none).isSome) T

/-! ### Byte-operand domains (`denseAddByteVarDoms`), coset streamed -/

def dbByteOperand (e : DenseExpr p) (bound : Nat) : Option (Nat × DbDom) :=
  match e with
  | .var i => some (i.index, .range bound)
  | _ => (denseAffineOfExpr e).map (fun t => (t.1.index, .coset bound (zmodNegP t.2.2).val (t.2.1⁻¹).val))

def dbByteOperandVar (e : DenseExpr p) : Option Nat :=
  match e with
  | .var i => some i.index
  | _ => (denseAffineOfExpr e).map (fun t => t.1.index)

def dbAddByteOperand (e : DenseExpr p) (bound : Nat) (T : DbTab p) : DbTab p :=
  match dbByteOperandVar e with
  | none => T
  | some i =>
    match T.get i with
    | none => T
    | some d0 =>
      if bound < d0.size then
        match dbByteOperand e bound with
        | some (i', d) => T.insert i' d
        | none => T
      else T

def dbAddByteBi (e : DbBiPre p) (T : DbTab p) : DbTab p :=
  match e.mult? with
  | none => T
  | some m =>
    if zmodIsZero m then T
    else
      match e.byte? with
      | none => T
      | some b =>
        match b.op? with
        | none => T
        | some opv =>
          if denseByteOpBounds b.spec opv then
            dbAddByteOperand b.o2 b.spec.bound (dbAddByteOperand b.o1 b.spec.bound T)
          else T

/-! ## Box helpers -/

def dbBoxOf (T : DbTab p) (vs : Array VarId) (k : Nat) (acc : Nat) : Option Nat :=
  if h : k < vs.size then
    match T.get vs[k].index with
    | none => none
    | some d => dbBoxOf T vs (k + 1) (acc * d.size)
  else some acc
  termination_by vs.size - k
  decreasing_by all_goals omega

def dbDomsOf (T : DbTab p) (vs : Array VarId) : Option (Array (DbDom)) :=
  vs.foldl (init := some #[]) fun acc v =>
    match acc with
    | none => none
    | some ds =>
      match T.get v.index with
      | none => none
      | some d => some (ds.push d)

/-- Enumerate a box, testing one item at every point; `false` at the first failure. Explicit-arg
    loops: no per-point allocation. -/
def dbBoxAllOne {bs : BusSemantics p} (facts : BusFacts p bs) (item : DbItem p)
    (keys : Array Nat) (doms : Array (DbDom)) (d i n : Nat) (regs : Array Nat)
    (ok : Bool) : Array Nat × Bool :=
  if i ≥ n then ⟨regs, ok⟩
  else if !ok then ⟨regs, ok⟩
  else
    let regs := regs.set! (keys.getD d 0) (DbDom.at p (doms.getD d (.range 0)) i)
    if d + 1 ≥ keys.size then
      if dbItemOk facts regs item then dbBoxAllOne facts item keys doms d (i + 1) n regs true
      else ⟨regs, false⟩
    else
      let ⟨regs, ok⟩ := dbBoxAllOne facts item keys doms (d + 1) 0
        (doms.getD (d + 1) (.range 0)).size regs true
      if ok then dbBoxAllOne facts item keys doms d (i + 1) n regs true else ⟨regs, false⟩
  termination_by (keys.size - d, n - i)
  decreasing_by
    all_goals first
      | (apply Prod.Lex.right; omega)
      | (apply Prod.Lex.left; omega)

/-- The box point where key `d` takes element `min i (size_d - 1)`. -/
def dbDiagPoint (p : ℕ) (keys : Array Nat) (doms : Array (DbDom)) (i : Nat) (regs : Array Nat) :
    Array Nat :=
  (Array.range keys.size).foldl (init := regs) fun regs d =>
    let dom := doms.getD d (.range 0)
    regs.set! (keys.getD d 0) (DbDom.at p dom (min i (dom.size - 1)))

/-- Refute redundancy on the box diagonal before sweeping it. The sweep varies the last key fastest,
    so a constraint that only fails once an *outer* key moves costs a whole inner domain to refute;
    97 % of the non-redundant checks on sha256/keccak fail within the first eight diagonal points
    (measured). Verdict-identical: these are box points, so a failure here is a failure there. -/
def dbDiagRefute {bs : BusSemantics p} (facts : BusFacts p bs) (item : DbItem p)
    (keys : Array Nat) (doms : Array (DbDom)) (i imax : Nat) (regs : Array Nat) :
    Array Nat × Bool :=
  if i ≥ imax then ⟨regs, false⟩
  else
    let regs := dbDiagPoint p keys doms i regs
    if dbItemOk facts regs item then dbDiagRefute facts item keys doms (i + 1) imax regs
    else ⟨regs, true⟩
  termination_by imax - i
  decreasing_by omega

/-- Boxes at most this size are swept directly; the diagonal pre-test would cost more than it
    saves. -/
def dbDiagGate : Nat := 16

/-- `denseConstraintRedundantV`: identically zero on the box of its own variables' domains. -/
def dbConstraintRedundant {bs : BusSemantics p} (facts : BusFacts p bs) (T : DbTab p)
    (item : DbItem p) (vs : Array VarId) (regs : Array Nat) : Array Nat × Bool :=
  match dbBoxOf T vs 0 1 with
  | none => ⟨regs, false⟩
  | some box =>
    if box ≤ maxEnumSize then
      match dbDomsOf T vs with
      | none => ⟨regs, false⟩
      | some doms =>
        if vs.isEmpty then ⟨regs, dbItemOk facts regs item⟩
        else
          let keys := vs.map (fun v => v.index)
          let ⟨regs, refuted⟩ :=
            if dbDiagGate < box then dbDiagRefute facts item keys doms 0 8 regs
            else ⟨regs, false⟩
          if refuted then ⟨regs, false⟩
          else
            dbBoxAllOne facts item keys doms 0 0 (doms.getD 0 (.range 0)).size regs true
    else ⟨regs, false⟩

/-! ## Domain-redundancy of an interaction -/

def dbExprBelow (T : DbTab p) (e : DenseExpr p) (bound : Nat) : Bool :=
  match e.constValue? with
  | some c => decide (c.val < bound)
  | none =>
    match e with
    | .var i => match T.get i.index with | some d => DbDom.below p d bound | none => false
    | _ => false

def dbRangeCheckRedundant (T : DbTab p) (bi : BusInteraction (DenseExpr p)) (e : DbBiPre p) :
    Bool :=
  match e.mult? with
  | some mult =>
    if zmodIsZero mult then true
    else if zmodIsOne mult then
      match e.rangeAt? with
      | some (slot, bound) =>
        match bi.payload[slot]? with
        | some x => dbExprBelow T x bound
        | none => false
      | none => false
    else false
  | none => false

def dbBytePairRedundant (T : DbTab p) (e : DbBiPre p) : Bool :=
  match e.byte? with
  | none => false
  | some b =>
    match b.op?, b.result.constValue? with
    | some opValue, some resultValue =>
      opValue = b.spec.pairOp && zmodIsZero resultValue &&
        dbExprBelow T b.o1 b.spec.bound && dbExprBelow T b.o2 b.spec.bound
    | _, _ => false

/-- `denseConstBiV?` from the pattern computed once. -/
def dbConstBi? (bi : BusInteraction (DenseExpr p)) (mult? : Option (ZMod p))
    (pat : List (Option (ZMod p))) : Option (BusInteraction (ZMod p)) :=
  match mult? with
  | none => none
  | some m =>
    match pat.foldr (fun s acc => match s, acc with
      | some v, some vs => some (v :: vs)
      | _, _ => none) (some []) with
    | none => none
    | some payload => some { busId := bi.busId, multiplicity := m, payload }

/-- `denseBiDomainRedundantV`. -/
def dbBiDomainRedundant {bs : BusSemantics p} (facts : BusFacts p bs) (bc : DbBusCache p)
    (T : DbTab p) (bi : BusInteraction (DenseExpr p)) (e : DbBiPre p) : Bool :=
  match dbConstBi? bi e.mult? e.pat with
  | some value => zmodIsZero value.multiplicity || facts.acceptsDec value
  | none =>
    if bc.neverViol.getD bi.busId false then true
    else
      match bi.payload with
      | [x, b] =>
        if e.varRange then
          match b.constValue? with
          | some width => if width.val ≤ 17 then dbExprBelow T x (2 ^ width.val) else false
          | none => false
        else
          match e.tuple? with
          | some (boundX, boundB) => dbExprBelow T x boundX && dbExprBelow T b boundB
          | none => dbRangeCheckRedundant T bi e || dbBytePairRedundant T e
      | _ => dbRangeCheckRedundant T bi e || dbBytePairRedundant T e

/-! ## The box scan

The register file is `VarId.index`-keyed and owned by the scan; the candidate mask is a value array
plus an alive flag array with a live count, so the abort test is O(1) per point. -/

structure DbScanSt where
  regs : Array Nat
  vals : Array Nat
  alive : Array Bool
  live : Nat
  started : Bool
deriving Inhabited

def dbAbsorbGo (regs : Array Nat) (keys : Array Nat) (i : Nat)
    (vals : Array Nat) (alive : Array Bool) (live : Nat) :
    Array Nat × Array Bool × Nat :=
  if h : i < keys.size then
    if alive.getD i false then
      if regs.getD (keys[i]) 0 == vals.getD i 0 then dbAbsorbGo regs keys (i + 1) vals alive live
      else dbAbsorbGo regs keys (i + 1) vals (alive.set! i false) (live - 1)
    else dbAbsorbGo regs keys (i + 1) vals alive live
  else (vals, alive, live)
  termination_by keys.size - i
  decreasing_by all_goals omega

/-- Intersect the mask with a surviving point; called only for survivors. -/
def dbAbsorbArgs (keys : Array Nat) (regs : Array Nat) (vals : Array Nat)
    (alive : Array Bool) (live : Nat) (started : Bool) :
    Array Nat × Array Bool × Nat × Bool :=
  if !started then
    ⟨keys.map (fun k => regs.getD k 0), Array.replicate keys.size true, keys.size, true⟩
  else
    let (vals, alive, live) := dbAbsorbGo regs keys 0 vals alive live
    ⟨vals, alive, live, started⟩

/-- The box loop. State is passed as explicit arguments, so nothing is allocated per point: the
    innermost dimension is walked in place (`regs.set!` on a uniquely-owned register file) and only a
    surviving point touches the mask.

    Items are grouped by *level* — the depth of the innermost key they mention (`itemAt` slices the
    array, `itemAt.getD d 0 .. itemAt.getD (d+1) 0`) — and tested as soon as that key is bound. An
    item that fails at depth `d` prunes the whole subtree below it, and one that mentions no inner
    key is not re-tested per point. Dropping a filter can only add survivors, so the grouping is
    verdict-identical however the levels are assigned. -/
def dbScanLoop {bs : BusSemantics p} (facts : BusFacts p bs) (items : Array (DbItem p))
    (ilev : Array Nat) (keys : Array Nat) (doms : Array (DbDom)) (d : Nat)
    (key : Nat) (dom : DbDom) (i n : Nat)
    (regs : Array Nat) (vals : Array Nat) (alive : Array Bool) (live : Nat)
    (started : Bool) : DbScanSt :=
  if i ≥ n then ⟨regs, vals, alive, live, started⟩
  else if started && live == 0 then ⟨regs, vals, alive, live, started⟩
  else
    let regs := regs.set! key (DbDom.at p dom i)
    if dbAllOkLev facts items ilev d regs 0 then
      if d + 1 ≥ keys.size then
        let ⟨vals, alive, live, started⟩ := dbAbsorbArgs keys regs vals alive live started
        dbScanLoop facts items ilev keys doms d key dom (i + 1) n regs vals alive live started
      else
        let dom' := doms.getD (d + 1) (.range 0)
        let ⟨regs, vals, alive, live, started⟩ :=
          dbScanLoop facts items ilev keys doms (d + 1) (keys.getD (d + 1) 0) dom' 0 dom'.size
            regs vals alive live started
        dbScanLoop facts items ilev keys doms d key dom (i + 1) n regs vals alive live started
    else
      dbScanLoop facts items ilev keys doms d key dom (i + 1) n regs vals alive live started
  termination_by (keys.size - d, n - i)
  decreasing_by
    all_goals first
      | (apply Prod.Lex.right; omega)
      | (apply Prod.Lex.left; omega)

/-- Scan a job's box, starting from an empty mask. -/
def dbScanBox {bs : BusSemantics p} (facts : BusFacts p bs) (items : Array (DbItem p))
    (ilev : Array Nat) (keys : Array Nat) (doms : Array (DbDom)) (regs : Array Nat) :
    DbScanSt :=
  if keys.isEmpty then
    -- the variable-free box has exactly one (empty) point
    if dbAllOkLev facts items ilev 0 regs 0 then ⟨regs, #[], #[], 0, true⟩
    else ⟨regs, #[], #[], 0, false⟩
  else
    let dom := doms.getD 0 (.range 0)
    dbScanLoop facts items ilev keys doms 0 (keys.getD 0 0) dom 0 dom.size regs #[] #[] 0 false

/-! ## Key order

The mask is an intersection over the box's survivors, so the forced set does not depend on the
order the box is enumerated in, and `live == 0` aborts soundly in any order. In lex order the last
key to die is the outermost one, and killing it costs one sweep of `box / size(key 0)` points — so
the largest domain goes outermost. The sort is **stable**: breaking equal sizes the other way is
measurably worse (keccak 2.7×).

The sort itself is untrusted. Its output is accepted only if it is still a distinct rearrangement of
the target's keys, and the domains are re-read from the table so the key/domain pairing holds by
construction (`dbDomsOf_get`); otherwise the original order is kept. -/

def dbSiftKey (a : Array (VarId × DbDom)) : Nat → Array (VarId × DbDom)
  | 0 => a
  | j + 1 =>
    if (a.getD (j + 1) default).2.size > (a.getD j default).2.size then
      dbSiftKey (a.swapIfInBounds j (j + 1)) j
    else a

def dbSortKeys (n : Nat) (a : Array (VarId × DbDom)) (i : Nat) : Array (VarId × DbDom) :=
  if i < n then dbSortKeys n (dbSiftKey a i) (i + 1) else a
  termination_by n - i

def dbNodupVars (a : Array VarId) (k : Nat) : Bool :=
  if h : k < a.size then (!dbMemVar a a[k] (k + 1) && dbNodupVars a (k + 1)) else true
  termination_by a.size - k
  decreasing_by all_goals omega

def dbOrderKeys (T : DbTab p) (xs : Array VarId) (doms : Array (DbDom)) :
    Array VarId × Array (DbDom) :=
  if xs.size ≤ 1 then (xs, doms)
  else
    let ks := (dbSortKeys xs.size (xs.zip doms) 1).map (·.1)
    if ks.size == xs.size && dbSubsetVars ks xs 0 && dbSubsetVars xs ks 0 && dbNodupVars ks 0 then
      match dbDomsOf T ks with
      | some ds => (ks, ds)
      | none => (xs, doms)
    else (xs, doms)

/-! ## Item levels

An item is tested at the depth of the innermost key it mentions, so a failure there prunes the whole
subtree and an item that mentions no inner key is not retested per point. `ilev` runs parallel to the
items the scan carries. An item mentioning a non-key is *dropped* (compiled to `.always`): the
gather rules that out, and dropping a filter can only add survivors. -/

def dbKeyPos? (keys : Array VarId) (v : VarId) (k : Nat) : Option Nat :=
  if h : k < keys.size then (if keys[k] == v then some k else dbKeyPos? keys v (k + 1))
  else none
  termination_by keys.size - k
  decreasing_by all_goals omega

/-- The depth of the innermost key the item mentions, or `none` when it mentions a non-key. -/
def dbItemLevel? (keys : Array VarId) (vs : Array VarId) : Option Nat :=
  vs.foldl (init := some 0) fun m v =>
    match m, dbKeyPos? keys v 0 with
    | some a, some b => some (max a b)
    | _, _ => none

/-- Pair the gathered items with their levels, dropping any whose variables are not all keys. -/
def dbLevelItems (keys : Array VarId) (items : Array (DbItem p)) (ivars : Array (Array VarId))
    (k : Nat) (out : Array (DbItem p)) (lev : Array Nat) : Array (DbItem p) × Array Nat :=
  if h : k < items.size then
    match dbItemLevel? keys (ivars.getD k #[]) with
    | some l => dbLevelItems keys items ivars (k + 1) (out.push items[k]) (lev.push l)
    | none => dbLevelItems keys items ivars (k + 1) (out.push DbItem.always) (lev.push 0)
  else (out, lev)
  termination_by items.size - k
  decreasing_by all_goals omega

/-! ## Plans -/

/-- A preflighted target: an immediate answer, or a scan job carrying its compiled items. -/
inductive DbPlan (p : ℕ) where
  | done (forced : List (VarId × ZMod p))
  | scan (keys : Array VarId) (doms : Array (DbDom)) (items : Array (DbItem p))
      (ilev : Array Nat) (constOk : Bool)

def dbForcedOfMask (p : ℕ) (keys : Array VarId) (vals : Array Nat) (alive : Array Bool) (i : Nat) :
    List (VarId × ZMod p) :=
  if h : i < keys.size then
    let rest := dbForcedOfMask p keys vals alive (i + 1)
    if alive.getD i false then (keys[i], zmodOfNatP p (vals.getD i 0)) :: rest else rest
  else []
  termination_by keys.size - i
  decreasing_by all_goals omega

def dbZeroAll (keys : Array VarId) : List (VarId × ZMod p) :=
  keys.toList.map (fun x => (x, zmodZeroP p))

/-! ## The slot-compiled unboxed box scan

`dbEval` walks a boxed `DenseExpr` at every point of every box. This engine compiles a plan once
and makes the point loop branch-light machine arithmetic:

* a plan's keys become **slots `0..k-1`** (`box ≤ maxEnumSize` with every domain ≥ 2 keeps
  `k ≤ 16`), so the register file is a k-element `UInt32` array;
* operands become sums of monomials `Σ cᵢ·∏ s` over slots where possible within `dbTermCap`
  (slot-indexed tree otherwise), each **split at the item's level `d`**: terms without slot `d`
  (`outer`), terms linear in slot `d` (`linCo`, the coefficient monomial with the slot removed —
  coefficients are constants, so a degree-1 occurrence always splits this way), and the rare
  `slot_d^{≥2}` terms (`high`);
* on each descent into depth `d` the loop evaluates `outer`/`linCo` once per operand into flat
  scratch arrays (`pb`/`pl`, preallocated, mutated in place), so **a box point costs one multiply
  and one add per operand** (`pb[o] + pl[o]·x`), plus `high`/tree work only where present;
* items are counting-sorted by level (`lstart` offsets), so the per-point test iterates exactly
  the current depth's items instead of filtering the whole array, and `.always` items are dropped
  at compile time.

Values are `ZMod.val`s: on a field with `65536 < p < 2^31` they fit `UInt32` and products fit
`UInt64`; `dbRunPlansFast` falls back to the boxed engine on any other field. Reassociating the
modular sums is the only arithmetic change, so the engine is verdict-identical. -/

/-- `a + b` on values below `p ≤ 2^31`: the sum cannot wrap a `UInt32`. -/
@[inline] def dbAddU (pm a b : UInt32) : UInt32 := let s := a + b; if s < pm then s else s - pm

/-- `a * b` on values below `p ≤ 2^31`: the product cannot wrap a `UInt64`. -/
@[inline] def dbMulU (pm64 : UInt64) (a b : UInt32) : UInt32 :=
  ((a.toUInt64 * b.toUInt64) % pm64).toUInt32

/-- The `i`-th element of a domain (`DbDom.at` under the field guard: every domain element and
    every `.range` index is below `maxDomainBound ≤ p`). -/
@[inline] def DbDom.atU (pm : UInt32) (pm64 : UInt64) (d : DbDom) (i : Nat) : UInt32 :=
  match d with
  | .explicit vs => (vs.getD i 0).toUInt32
  | .range _ => i.toUInt32
  | .coset _ negB aInv => dbMulU pm64 (dbAddU pm i.toUInt32 negB.toUInt32) aInv.toUInt32

/-- A bound compared against a register value. Values are below `2^31`, so a bound at or above
    `2^32` is equivalent to `2^32` and the comparison stays exact in `UInt64`. -/
@[inline] def dbBoundU (b : Nat) : UInt64 := if 4294967296 ≤ b then 4294967296 else b.toUInt64

@[inline] def dbLtU (x : UInt32) (b : UInt64) : Bool := x.toUInt64 < b

@[inline] def dbByteRelU (kind : DenseBytePredKind) (a b r : UInt32) : Bool :=
  match kind with
  | .xor => r == a ^^^ b
  | .pair => r == 0
  | .or => r == a ||| b
  | .and => r == a &&& b

/-- One monomial over slots. -/
inductive DbTerm where
  | cst (c : UInt32)
  | lin (c : UInt32) (s : Nat)
  | mono (c : UInt32) (ss : Array Nat)
deriving Inhabited

def DbTerm.coef : DbTerm → UInt32
  | .cst c => c | .lin c _ => c | .mono c _ => c

def DbTerm.slotsArr : DbTerm → Array Nat
  | .cst _ => #[] | .lin _ s => #[s] | .mono _ ss => ss

@[inline] def DbTerm.of (c : UInt32) (ss : Array Nat) : DbTerm :=
  if ss.size == 0 then .cst c else if ss.size == 1 then .lin c (ss.getD 0 0) else .mono c ss

/-- Slot-indexed operand tree, for operands the monomial expansion does not cover. -/
inductive DbSTr where
  | cst (c : UInt32)
  | slot (s : Nat)
  | add (a b : DbSTr)
  | mul (a b : DbSTr)
deriving Inhabited

def dbEvalTr (pm : UInt32) (pm64 : UInt64) (regs : Array UInt32) : DbSTr → UInt32
  | .cst c => c
  | .slot s => regs.getD s 0
  | .add a b => dbAddU pm (dbEvalTr pm pm64 regs a) (dbEvalTr pm pm64 regs b)
  | .mul a b => dbMulU pm64 (dbEvalTr pm pm64 regs a) (dbEvalTr pm pm64 regs b)

def dbEvalTerms (pm : UInt32) (pm64 : UInt64) (regs : Array UInt32) (ts : Array DbTerm) :
    UInt32 :=
  ts.foldl (init := 0) fun acc t =>
    match t with
    | .cst c => dbAddU pm acc c
    | .lin c s => dbAddU pm acc (dbMulU pm64 c (regs.getD s 0))
    | .mono c ss =>
      dbAddU pm acc (ss.foldl (init := c) fun m s => dbMulU pm64 m (regs.getD s 0))

/-! ### Compilation -/

/-- The slot of variable index `v`, or `keys.size` (an unbound register reading 0 — unreachable:
    the gather only admits items whose variables are all keys). -/
def dbSlotIdx (keys : Array Nat) (v : Nat) (k : Nat) : Nat :=
  if h : k < keys.size then (if keys[k] == v then k else dbSlotIdx keys v (k + 1)) else keys.size
  termination_by keys.size - k
  decreasing_by all_goals omega

def dbTrOf (keys : Array Nat) : DenseExpr p → DbSTr
  | .const c => .cst c.val.toUInt32
  | .var i => .slot (dbSlotIdx keys i.index 0)
  | .add a b => .add (dbTrOf keys a) (dbTrOf keys b)
  | .mul a b => .mul (dbTrOf keys a) (dbTrOf keys b)

def dbMulTerm (pm64 : UInt64) (s t : DbTerm) : DbTerm :=
  DbTerm.of (dbMulU pm64 s.coef t.coef) (s.slotsArr ++ t.slotsArr)

def dbCrossTerms (pm64 : UInt64) (x y : Array DbTerm) : Array DbTerm :=
  x.foldl (init := Array.emptyWithCapacity (x.size * y.size)) fun acc s =>
    y.foldl (init := acc) fun acc t => acc.push (dbMulTerm pm64 s t)

/-- Terms beyond this many abandon the expansion for the tree walk. -/
def dbTermCap : Nat := 64

def dbTermsOf (pm64 : UInt64) (keys : Array Nat) : DenseExpr p → Option (Array DbTerm)
  | .const c => some #[.cst c.val.toUInt32]
  | .var i => some #[.lin 1 (dbSlotIdx keys i.index 0)]
  | .add a b =>
    match dbTermsOf pm64 keys a, dbTermsOf pm64 keys b with
    | some x, some y => if x.size + y.size ≤ dbTermCap then some (x ++ y) else none
    | _, _ => none
  | .mul a b =>
    match dbTermsOf pm64 keys a, dbTermsOf pm64 keys b with
    | some x, some y =>
      if x.size * y.size ≤ dbTermCap then some (dbCrossTerms pm64 x y) else none
    | _, _ => none

def dbCountEq (ss : Array Nat) (d : Nat) : Nat :=
  ss.foldl (init := 0) fun n s => if s == d then n + 1 else n

def dbEraseOne (ss : Array Nat) (d : Nat) : Array Nat :=
  (ss.foldl (init := (Array.emptyWithCapacity ss.size, false)) fun st s =>
    if !st.2 && s == d then (st.1, true) else (st.1.push s, st.2)).1

/-- Split terms at level `d`: terms without slot `d`, coefficient monomials of the terms linear in
    slot `d`, and the `slot_d^{≥2}` terms. -/
def dbSplitTerms (d : Nat) (ts : Array DbTerm) :
    Array DbTerm × Array DbTerm × Array DbTerm :=
  ts.foldl (init := (#[], #[], #[])) fun st t =>
    let (o, l, h) := st
    match t with
    | .cst _ => (o.push t, l, h)
    | .lin c s => if s == d then (o, l.push (.cst c), h) else (o.push t, l, h)
    | .mono c ss =>
      match dbCountEq ss d with
      | 0 => (o.push t, l, h)
      | 1 => (o, l.push (DbTerm.of c (dbEraseOne ss d)), h)
      | _ => (o, l, h.push t)

/-- One compiled operand: split terms (evaluated as `pb[o] + pl[o]·x` per point), or a tree. -/
inductive DbCOp where
  | split (outer linCo high : Array DbTerm)
  | tree (t : DbSTr)
deriving Inhabited

def dbExprSize : DenseExpr p → Nat
  | .const _ => 1 | .var _ => 1
  | .add a b => 1 + dbExprSize a + dbExprSize b
  | .mul a b => 1 + dbExprSize a + dbExprSize b

def dbCOpOf (pm64 : UInt64) (keys : Array Nat) (d : Nat) (e : DenseExpr p) : DbCOp :=
  if dbExprSize e ≤ 1 then .tree (dbTrOf keys e)
  else
    match dbTermsOf pm64 keys e with
    | some ts =>
      let (o, l, h) := dbSplitTerms d ts
      .split o l h
    | none => .tree (dbTrOf keys e)

/-- A compiled item: operand indices into the plan's `ops` array. -/
inductive DbXIt where
  | zero (o : Nat)
  | varRange (m x w : Nat)
  | varRangeConst (m x : Nat) (bound : UInt64)
  | tupleRange (m x y : Nat) (bx bY : UInt64)
  | fixedRange (m v : Nat) (bound : UInt64)
  | byte (m o1 o2 r : Nat) (bound : UInt64) (kind : DenseBytePredKind)
  | fallback (busId : Nat) (m : Nat) (payload : List Nat)
deriving Inhabited

def dbCompileOps (pm64 : UInt64) (keys : Array Nat) (d : Nat) (ops : Array DbCOp) :
    List (DenseExpr p) → Array DbCOp × List Nat
  | [] => (ops, [])
  | e :: rest =>
    let o := ops.size
    let (ops, os) := dbCompileOps pm64 keys d (ops.push (dbCOpOf pm64 keys d e)) rest
    (ops, o :: os)

def dbCompileItem (pm64 : UInt64) (keys : Array Nat) (d : Nat) (ops : Array DbCOp) :
    DbItem p → Array DbCOp × Option DbXIt
  | .always => (ops, none)
  | .zero e => (ops.push (dbCOpOf pm64 keys d e), some (.zero ops.size))
  | .varRange m x w =>
    let o := ops.size
    let ops := ((ops.push (dbCOpOf pm64 keys d m)).push (dbCOpOf pm64 keys d x)).push
      (dbCOpOf pm64 keys d w)
    (ops, some (.varRange o (o + 1) (o + 2)))
  | .varRangeConst m x b =>
    let o := ops.size
    let ops := (ops.push (dbCOpOf pm64 keys d m)).push (dbCOpOf pm64 keys d x)
    (ops, some (.varRangeConst o (o + 1) (dbBoundU b)))
  | .tupleRange m x y bx bY =>
    let o := ops.size
    let ops := ((ops.push (dbCOpOf pm64 keys d m)).push (dbCOpOf pm64 keys d x)).push
      (dbCOpOf pm64 keys d y)
    (ops, some (.tupleRange o (o + 1) (o + 2) (dbBoundU bx) (dbBoundU bY)))
  | .fixedRange m v b =>
    let o := ops.size
    let ops := (ops.push (dbCOpOf pm64 keys d m)).push (dbCOpOf pm64 keys d v)
    (ops, some (.fixedRange o (o + 1) (dbBoundU b)))
  | .byte m o1 o2 r b kind =>
    let o := ops.size
    let ops := (((ops.push (dbCOpOf pm64 keys d m)).push (dbCOpOf pm64 keys d o1)).push
      (dbCOpOf pm64 keys d o2)).push (dbCOpOf pm64 keys d r)
    (ops, some (.byte o (o + 1) (o + 2) (o + 3) (dbBoundU b) kind))
  | .fallback busId m payload =>
    let o := ops.size
    let (ops, os) := dbCompileOps pm64 keys d (ops.push (dbCOpOf pm64 keys d m)) payload
    (ops, some (.fallback busId o os))

def dbLevCount (items : Array (DbItem p)) (ilev : Array Nat) (k : Nat) (counts : Array Nat) :
    Array Nat :=
  if h : k < items.size then
    let counts := match items[k] with
      | .always => counts
      | _ => counts.modify (ilev.getD k 0) (· + 1)
    dbLevCount items ilev (k + 1) counts
  else counts
  termination_by items.size - k
  decreasing_by all_goals omega

def dbLstartOf (counts : Array Nat) : Array Nat :=
  counts.foldl (init := #[0]) fun ls c => ls.push (ls.getD (ls.size - 1) 0 + c)

/-- A compiled plan: items counting-sorted by level (`lstart` offsets), operands flattened. -/
structure DbCompiled where
  items : Array DbXIt
  ops : Array DbCOp
  lstart : Array Nat
deriving Inhabited

def dbCompileGo (pm64 : UInt64) (keys : Array Nat) (items : Array (DbItem p))
    (ilev : Array Nat) (k : Nat) (cur : Array Nat) (out : Array DbXIt) (ops : Array DbCOp) :
    Array DbXIt × Array DbCOp :=
  if h : k < items.size then
    let d := ilev.getD k 0
    let (ops, xit?) := dbCompileItem pm64 keys d ops items[k]
    match xit? with
    | none => dbCompileGo pm64 keys items ilev (k + 1) cur out ops
    | some xit =>
      let pos := cur.getD d 0
      dbCompileGo pm64 keys items ilev (k + 1) (cur.modify d (· + 1)) (out.set! pos xit) ops
  else (out, ops)
  termination_by items.size - k
  decreasing_by all_goals omega

def dbCompilePlan (pm64 : UInt64) (keys : Array Nat) (kks : Nat) (items : Array (DbItem p))
    (ilev : Array Nat) : DbCompiled :=
  let counts := dbLevCount items ilev 0 (Array.replicate kks 0)
  let lstart := dbLstartOf counts
  let total := lstart.getD kks 0
  let cur := lstart.extract 0 kks
  let (out, ops) := dbCompileGo pm64 keys items ilev 0 cur
    (Array.replicate total default) (Array.emptyWithCapacity (2 * items.size))
  { items := out, ops, lstart }

/-! ### Descent preparation and point evaluation -/

def dbPrepOp (pm : UInt32) (pm64 : UInt64) (ops : Array DbCOp) (regs : Array UInt32) (o : Nat)
    (st : Array UInt32 × Array UInt32) : Array UInt32 × Array UInt32 :=
  match ops.getD o default with
  | .split outer linCo _ =>
    (st.1.set! o (dbEvalTerms pm pm64 regs outer), st.2.set! o (dbEvalTerms pm pm64 regs linCo))
  | .tree _ => st

/-- A level's pivot: the slot value `x0` solving `operand o = target` is the only one any point
    can survive (`.val`), or no point at this depth can survive at all (`.dead`). -/
inductive DbPivot where
  | val (o : Nat) (target : UInt32)
  | dead

/-- The operand viewed as `base + lin·x` at depth `d` (`x` the slot-`d` register), `none` when it
    is not affine in `x`. Slots below `d` are bound, so a foreign-slot tree leaf is a constant. -/
def dbOpAffine? (ops : Array DbCOp) (pb pl regs : Array UInt32) (d o : Nat) :
    Option (UInt32 × UInt32) :=
  match ops.getD o default with
  | .split _ _ high => if high.isEmpty then some (pb.getD o 0, pl.getD o 0) else none
  | .tree (.cst c) => some (c, 0)
  | .tree (.slot s) => if s == d then some (0, 1) else some (regs.getD s 0, 0)
  | .tree _ => none

@[inline] def dbOpConstU? (ops : Array DbCOp) (pb pl regs : Array UInt32) (d o : Nat) :
    Option UInt32 :=
  match dbOpAffine? ops pb pl regs d o with
  | some (b, l) => if l == 0 then some b else none
  | none => none

/-- A byte item's pivot at depth `d`: with a nonzero constant multiplicity, a slot-affine operand
    among `o1`/`o2`/`result` while the other two are constants pins the slot to one value (xor is
    solvable from either side; or/and/pair only through the result). -/
def dbBytePivot (ops : Array DbCOp) (pb pl regs : Array UInt32) (d : Nat)
    (m o1 o2 r : Nat) (bound : UInt64) (kind : DenseBytePredKind) : Option DbPivot :=
  match dbOpConstU? ops pb pl regs d m with
  | none => none
  | some mv =>
    if mv == 0 then none
    else
      match dbOpAffine? ops pb pl regs d o1, dbOpAffine? ops pb pl regs d o2,
          dbOpAffine? ops pb pl regs d r with
      | some (b1, l1), some (b2, l2), some (br, lr) =>
        if l1 != 0 && l2 == 0 && lr == 0 then
          match kind with
          | .xor =>
            if !dbLtU b2 bound then some .dead
            else
              let a := br ^^^ b2
              if dbLtU a bound then some (.val o1 a) else some .dead
          | _ => none
        else if l1 == 0 && l2 != 0 && lr == 0 then
          match kind with
          | .xor =>
            if !dbLtU b1 bound then some .dead
            else
              let b := br ^^^ b1
              if dbLtU b bound then some (.val o2 b) else some .dead
          | _ => none
        else if l1 == 0 && l2 == 0 && lr != 0 then
          if !dbLtU b1 bound || !dbLtU b2 bound then some .dead
          else
            match kind with
            | .xor => some (.val r (b1 ^^^ b2))
            | .or => some (.val r (b1 ||| b2))
            | .and => some (.val r (b1 &&& b2))
            | .pair => some (.val r 0)
        else none
      | _, _, _ => none

/-- Evaluate the level's `outer`/`linCo` sums into the scratch arrays, one item range per
    descent — and report a pivot where an item pins the slot to at most one value. -/
def dbPrepRange (pm : UInt32) (pm64 : UInt64) (items : Array DbXIt) (ops : Array DbCOp)
    (regs : Array UInt32) (d : Nat) (i hi : Nat) (st : Array UInt32 × Array UInt32)
    (piv : Option DbPivot) : (Array UInt32 × Array UInt32) × Option DbPivot :=
  if i < hi then
    if h : i < items.size then
      let (st, piv) := match items[i] with
        | .zero o =>
          let st := dbPrepOp pm pm64 ops regs o st
          let piv := if piv.isSome then piv
            else
              match dbOpAffine? ops st.1 st.2 regs d o with
              | some (_, l) => if l != 0 then some (.val o 0) else none
              | none => none
          (st, piv)
        | .varRange m x w =>
          (dbPrepOp pm pm64 ops regs w (dbPrepOp pm pm64 ops regs x
            (dbPrepOp pm pm64 ops regs m st)), piv)
        | .varRangeConst m x _ =>
          (dbPrepOp pm pm64 ops regs x (dbPrepOp pm pm64 ops regs m st), piv)
        | .tupleRange m x y _ _ =>
          (dbPrepOp pm pm64 ops regs y (dbPrepOp pm pm64 ops regs x
            (dbPrepOp pm pm64 ops regs m st)), piv)
        | .fixedRange m v _ =>
          (dbPrepOp pm pm64 ops regs v (dbPrepOp pm pm64 ops regs m st), piv)
        | .byte m o1 o2 r bound kind =>
          let st := dbPrepOp pm pm64 ops regs r (dbPrepOp pm pm64 ops regs o2
            (dbPrepOp pm pm64 ops regs o1 (dbPrepOp pm pm64 ops regs m st)))
          let piv := if piv.isSome then piv
            else dbBytePivot ops st.1 st.2 regs d m o1 o2 r bound kind
          (st, piv)
        | .fallback _ m payload =>
          (payload.foldl (init := dbPrepOp pm pm64 ops regs m st) fun st o =>
            dbPrepOp pm pm64 ops regs o st, piv)
      dbPrepRange pm pm64 items ops regs d (i + 1) hi st piv
    else (st, piv)
  else (st, piv)
  termination_by hi - i
  decreasing_by all_goals omega

/-- `b^e mod p` by binary exponentiation (32 rounds cover any `UInt32` exponent). -/
def dbPowU (pm64 : UInt64) : Nat → UInt32 → UInt32 → UInt32 → UInt32
  | 0, _, acc, _ => acc
  | fuel + 1, b, acc, e =>
    if e == 0 then acc
    else
      let acc := if e &&& 1 == 1 then dbMulU pm64 acc b else acc
      dbPowU pm64 fuel (dbMulU pm64 b b) acc (e >>> 1)

/-- `a⁻¹ mod p` for prime `p` and `a ≠ 0`: `a^(p−2)`. -/
@[inline] def dbInvU (pm : UInt32) (pm64 : UInt64) (a : UInt32) : UInt32 :=
  dbPowU pm64 32 a 1 (pm - 2)

@[inline] def dbNegU (pm a : UInt32) : UInt32 := if a == 0 then 0 else pm - a

/-- The index of value `x` in a domain, `none` when absent (`.coset` callers keep the sweep). -/
def dbDomFind (d : DbDom) (x : UInt32) : Option Nat :=
  match d with
  | .range b => if x.toNat < b then some x.toNat else none
  | .explicit vs => vs.findIdx? (fun v => v.toUInt32 == x)
  | .coset _ _ _ => none

/-- One operand at the current point: `pb[o] + pl[o]·x`, plus `high`/tree work where present.
    `imm` (levels whose domain is too small to repay a prepared descent) evaluates the sums in
    place instead of reading the scratch arrays. -/
@[inline] def dbOpVal (imm : Bool) (pm : UInt32) (pm64 : UInt64) (ops : Array DbCOp)
    (pb pl regs : Array UInt32) (x : UInt32) (o : Nat) : UInt32 :=
  match ops.getD o default with
  | .split outer linCo high =>
    let b := if imm then dbEvalTerms pm pm64 regs outer else pb.getD o 0
    let l := if imm then dbEvalTerms pm pm64 regs linCo else pl.getD o 0
    let v := dbAddU pm b (dbMulU pm64 l x)
    if high.isEmpty then v else dbAddU pm v (dbEvalTerms pm pm64 regs high)
  | .tree t => dbEvalTr pm pm64 regs t

def dbXItOk {bs : BusSemantics p} (facts : BusFacts p bs) (imm : Bool) (pm : UInt32)
    (pm64 : UInt64) (ops : Array DbCOp) (pb pl regs : Array UInt32) (x : UInt32) : DbXIt → Bool
  | .zero o => dbOpVal imm pm pm64 ops pb pl regs x o == 0
  | .varRange m xo w =>
    if dbOpVal imm pm pm64 ops pb pl regs x m == 0 then true
    else
      let wv := dbOpVal imm pm pm64 ops pb pl regs x w
      if wv ≤ 17 then dbLtU (dbOpVal imm pm pm64 ops pb pl regs x xo) (1 <<< wv.toUInt64)
      else false
  | .varRangeConst m xo bound =>
    if dbOpVal imm pm pm64 ops pb pl regs x m == 0 then true
    else dbLtU (dbOpVal imm pm pm64 ops pb pl regs x xo) bound
  | .tupleRange m xo yo bx bY =>
    if dbOpVal imm pm pm64 ops pb pl regs x m == 0 then true
    else
      dbLtU (dbOpVal imm pm pm64 ops pb pl regs x xo) bx &&
        dbLtU (dbOpVal imm pm pm64 ops pb pl regs x yo) bY
  | .fixedRange m v bound =>
    if dbOpVal imm pm pm64 ops pb pl regs x m == 0 then true
    else dbLtU (dbOpVal imm pm pm64 ops pb pl regs x v) bound
  | .byte m o1 o2 r bound kind =>
    if dbOpVal imm pm pm64 ops pb pl regs x m == 0 then true
    else
      let a := dbOpVal imm pm pm64 ops pb pl regs x o1
      let b := dbOpVal imm pm pm64 ops pb pl regs x o2
      dbLtU a bound && dbLtU b bound &&
        dbByteRelU kind a b (dbOpVal imm pm pm64 ops pb pl regs x r)
  | .fallback busId m payload =>
    let mv := dbOpVal imm pm pm64 ops pb pl regs x m
    if mv == 0 then true
    else
      facts.acceptsDec
        { busId := busId, multiplicity := zmodOfNatP p mv.toNat,
          payload := payload.map
            (fun o => zmodOfNatP p (dbOpVal imm pm pm64 ops pb pl regs x o).toNat) }

def dbLevOkY {bs : BusSemantics p} (facts : BusFacts p bs) (imm : Bool) (pm : UInt32)
    (pm64 : UInt64) (items : Array DbXIt) (ops : Array DbCOp) (pb pl regs : Array UInt32)
    (x : UInt32) (i hi : Nat) : Bool :=
  if i < hi then
    if h : i < items.size then
      if dbXItOk facts imm pm pm64 ops pb pl regs x items[i] then
        dbLevOkY facts imm pm pm64 items ops pb pl regs x (i + 1) hi
      else false
    else true
  else true
  termination_by hi - i
  decreasing_by all_goals omega

/-! ### The box loop -/

structure DbScanY where
  regs : Array UInt32
  pb : Array UInt32
  pl : Array UInt32
  vals : Array UInt32
  alive : Array Bool
  live : Nat
  started : Bool
deriving Inhabited

def dbAbsorbY (regs : Array UInt32) (i : Nat) (vals : Array UInt32) (alive : Array Bool)
    (live : Nat) : Array UInt32 × Array Bool × Nat :=
  if h : i < vals.size then
    if alive.getD i false then
      if regs.getD i 0 == vals.getD i 0 then dbAbsorbY regs (i + 1) vals alive live
      else dbAbsorbY regs (i + 1) vals (alive.set! i false) (live - 1)
    else dbAbsorbY regs (i + 1) vals alive live
  else (vals, alive, live)
  termination_by vals.size - i
  decreasing_by all_goals omega

@[inline] def dbAbsorbYArgs (kks : Nat) (regs vals : Array UInt32) (alive : Array Bool)
    (live : Nat) (started : Bool) : Array UInt32 × Array Bool × Nat × Bool :=
  if !started then (regs.extract 0 kks, Array.replicate kks true, kks, true)
  else
    let (vals, alive, live) := dbAbsorbY regs 0 vals alive live
    (vals, alive, live, started)

mutual

/-- Enter depth `d` with slots `0..d-1` bound: prepare the level's operands and, when a pivot
    exists on a directly-indexable domain, test only the pivot's root — the level's sweep
    collapses from `n` points to one lookup. `dbDomFind` misses ⟹ no point at this depth
    survives the pivot item ⟹ no survivors at all. -/
def dbScanDepth {bs : BusSemantics p} (facts : BusFacts p bs) (pm : UInt32) (pm64 : UInt64)
    (items : Array DbXIt) (ops : Array DbCOp) (lstart : Array Nat) (doms : Array DbDom)
    (kks d : Nat) (regs pb pl vals : Array UInt32) (alive : Array Bool) (live : Nat)
    (started : Bool) : DbScanY :=
  let dom := doms.getD d (.range 0)
  let n := dom.size
  -- a small domain does not repay the prepared descent: sweep in immediate mode, no scratch
  if n < 12 then
    dbScanLoopY facts true pm pm64 items ops lstart doms kks d 0 n regs pb pl vals alive live
      started
  else
  let (st, piv) := dbPrepRange pm pm64 items ops regs d (lstart.getD d 0)
    (lstart.getD (d + 1) 0) (pb, pl) none
  let pb := st.1
  let pl := st.2
  match piv with
  | some .dead => ⟨regs, pb, pl, vals, alive, live, started⟩
  | some (.val o target) =>
    let direct := match dom with | .coset _ _ _ => false | _ => true
    if direct && 8 < n then
      -- solve `base + lin·x = target` (the affine view is re-derived; `lin ≠ 0` by construction)
      let x0 :=
        match dbOpAffine? ops pb pl regs d o with
        | some (b, l) =>
          let diff := dbAddU pm target (dbNegU pm b)
          if l == 1 then diff else dbMulU pm64 diff (dbInvU pm pm64 l)
        | none => 0
      match dbDomFind dom x0 with
      | some i0 =>
        dbScanLoopY facts false pm pm64 items ops lstart doms kks d i0 (i0 + 1) regs pb pl
          vals alive live started
      | none => ⟨regs, pb, pl, vals, alive, live, started⟩
    else
      dbScanLoopY facts false pm pm64 items ops lstart doms kks d 0 n regs pb pl vals alive
        live started
  | none =>
    dbScanLoopY facts false pm pm64 items ops lstart doms kks d 0 n regs pb pl vals alive live
      started
  termination_by (kks - d, (doms.getD d (.range 0)).size + 2)
  decreasing_by
    all_goals (apply Prod.Lex.right; omega)

def dbScanLoopY {bs : BusSemantics p} (facts : BusFacts p bs) (imm : Bool) (pm : UInt32)
    (pm64 : UInt64) (items : Array DbXIt) (ops : Array DbCOp) (lstart : Array Nat)
    (doms : Array DbDom) (kks d i n : Nat) (regs pb pl vals : Array UInt32)
    (alive : Array Bool) (live : Nat) (started : Bool) : DbScanY :=
  if i ≥ n then ⟨regs, pb, pl, vals, alive, live, started⟩
  else if started && live == 0 then ⟨regs, pb, pl, vals, alive, live, started⟩
  else
    let x := DbDom.atU pm pm64 (doms.getD d (.range 0)) i
    let regs := regs.set! d x
    if dbLevOkY facts imm pm pm64 items ops pb pl regs x (lstart.getD d 0)
      (lstart.getD (d + 1) 0)
    then
      if d + 1 ≥ kks then
        let (vals, alive, live, started) := dbAbsorbYArgs kks regs vals alive live started
        dbScanLoopY facts imm pm pm64 items ops lstart doms kks d (i + 1) n regs pb pl vals alive
          live started
      else
        let r := dbScanDepth facts pm pm64 items ops lstart doms kks (d + 1) regs pb pl vals
          alive live started
        dbScanLoopY facts imm pm pm64 items ops lstart doms kks d (i + 1) n r.regs r.pb r.pl r.vals
          r.alive r.live r.started
    else
      dbScanLoopY facts imm pm pm64 items ops lstart doms kks d (i + 1) n regs pb pl vals alive live
        started
  termination_by (kks - d, n - i)
  decreasing_by
    all_goals first
      | (apply Prod.Lex.right; omega)
      | (apply Prod.Lex.left; omega)

end

def dbForcedOfMaskU (p : ℕ) (keys : Array VarId) (vals : Array UInt32) (alive : Array Bool)
    (i : Nat) : List (VarId × ZMod p) :=
  if h : i < keys.size then
    let rest := dbForcedOfMaskU p keys vals alive (i + 1)
    if alive.getD i false then (keys[i], zmodOfNatP p (vals.getD i 0).toNat) :: rest else rest
  else []
  termination_by keys.size - i
  decreasing_by all_goals omega

def dbRunPlanY {bs : BusSemantics p} (facts : BusFacts p bs) (pm : UInt32) (pm64 : UInt64)
    (out : List (List (VarId × ZMod p))) (plan : DbPlan p) : List (List (VarId × ZMod p)) :=
  match plan with
  | .done forced => forced :: out
  | .scan keys doms items ilev constOk =>
    if !constOk then dbZeroAll keys :: out
    else if keys.isEmpty then [] :: out
    else
      let kks := keys.size
      let kidx := keys.map (fun v => v.index)
      let C := dbCompilePlan pm64 kidx kks items ilev
      let regs := Array.replicate kks (0 : UInt32)
      let r := dbScanDepth facts pm pm64 C.items C.ops C.lstart doms kks 0 regs
        (Array.replicate C.ops.size 0) (Array.replicate C.ops.size 0) #[] #[] 0 false
      if !r.started then dbZeroAll keys :: out
      else if r.live == 0 then [] :: out
      else dbForcedOfMaskU p keys r.vals r.alive 0 :: out

/-- Run one plan, threading the register file so it is allocated once for the whole run. -/
def dbRunPlan {bs : BusSemantics p} (facts : BusFacts p bs) (nv : Nat)
    (st : Array Nat × List (List (VarId × ZMod p))) (plan : DbPlan p) :
    Array Nat × List (List (VarId × ZMod p)) :=
  match plan with
  | .done forced => ⟨st.1, forced :: st.2⟩
  | .scan keys doms items ilev constOk =>
    let ⟨regs0, out⟩ := st
    let regs0 := if regs0.size == nv then regs0 else Array.replicate nv 0
    if !constOk then ⟨regs0, dbZeroAll keys :: out⟩
    else
      let res := dbScanBox facts items ilev (keys.map (fun v => v.index)) doms regs0
      let ⟨regs, vals, alive, live, started⟩ := res
      if !started then ⟨regs, dbZeroAll keys :: out⟩
      else if live == 0 then ⟨regs, [] :: out⟩
      else ⟨regs, dbForcedOfMask p keys vals alive 0 :: out⟩

/-- Boxes below this many points do not repay the per-plan compilation; they run on the boxed
    engine. -/
def dbCompileGate : Nat := 256

/-- One plan on the hybrid engine: the compiled scan for large boxes, the boxed scan (with its
    threaded register file) below the gate. -/
def dbRunPlanH {bs : BusSemantics p} (facts : BusFacts p bs) (pm : UInt32) (pm64 : UInt64)
    (nv : Nat) (st : Array Nat × List (List (VarId × ZMod p))) (plan : DbPlan p) :
    Array Nat × List (List (VarId × ZMod p)) :=
  match plan with
  | .done forced => (st.1, forced :: st.2)
  | .scan _ doms _ _ _ =>
    if doms.foldl (init := 1) (fun a d => a * d.size) < dbCompileGate then
      dbRunPlan facts nv st plan
    else (st.1, dbRunPlanY facts pm pm64 st.2 plan)

/-- The compiled engine, standing in for `dbRunPlans` on any field whose values fit the `UInt32`
    register file (`65536 < p < 2^31`, which both supported fields satisfy). -/
def dbRunPlansFast {bs : BusSemantics p} (facts : BusFacts p bs) (nv : Nat)
    (plans : List (DbPlan p)) : List (List (VarId × ZMod p)) :=
  if 65536 < p && p < 2147483648 then
    (plans.foldl (dbRunPlanH facts p.toUInt32 p.toUInt64 nv)
      (⟨#[], []⟩ : Array Nat × List (List (VarId × ZMod p)))).2.reverse
  else
    (plans.foldl (dbRunPlan facts nv)
      (⟨#[], []⟩ : Array Nat × List (List (VarId × ZMod p)))).2.reverse

@[implemented_by dbRunPlansFast]
def dbRunPlans {bs : BusSemantics p} (facts : BusFacts p bs) (nv : Nat) (plans : List (DbPlan p)) :
    List (List (VarId × ZMod p)) :=
  (plans.foldl (dbRunPlan facts nv)
    (⟨#[], []⟩ : Array Nat × List (List (VarId × ZMod p)))).2.reverse

/-! ## Target dedup

The key is the target's own distinct-variable array — no copy, no sort — under an
order-independent content hash, with an exact set compare in the bucket (a false hit would lose a
forced constant, so the compare is not optional). -/

@[inline] def dbMixIdx (i : Nat) : UInt64 :=
  let x := (UInt64.ofNat i) * 0x9e3779b97f4a7c15
  (x ^^^ (x >>> 29)) * 0xbf58476d1ce4e5b9

/-- Summed, so two orderings of the same variable set collide by construction. -/
def dbKeyHash (vs : Array VarId) : UInt64 :=
  vs.foldl (init := 0x27d4eb2f165667c5) fun h v => h + dbMixIdx v.index

/-- Seen target keys, bucketed by content hash. -/
structure DbSeen where
  buckets : Std.HashMap UInt64 (List (Array VarId))

def dbAnySame (l : List (Array VarId)) (k : Array VarId) : Bool :=
  match l with
  | [] => false
  | a :: rest => dbSameSet a k || dbAnySame rest k

/-- Destructure before reading the bucket: leaving `s.buckets` referenced by the record while
    inserting copies the whole table per insert. -/
def DbSeen.insertNew (s : DbSeen) (h : UInt64) (k : Array VarId) : Bool × DbSeen :=
  let ⟨buckets⟩ := s
  let cur := buckets.getD h []
  if dbAnySame cur k then (false, ⟨buckets⟩)
  else (true, ⟨buckets.insert h (k :: cur)⟩)

/-! ## The per-invocation context

Everything the target loop reads, built by four passes over the system: variable lists, the domain
table (constraint roots, then bus slot bounds, then byte operands), the per-item flags, and the
anchor buckets. -/

structure DbCtx (p : ℕ) where
  nv : Nat
  T : DbTab p
  csVars : Array (Array VarId)
  csItems : Array (DbItem p)
  csActive : Array Bool
  csBucket : Array (Array Nat)
  /-- Variable-free constraints' target-independent contribution: their count (active or not) and
      the active ones' items (`denseConstraintCovIndexV`). -/
  csVarlessCount : Nat
  csVarlessItems : Array (DbItem p)
  /-- `csVarlessItems`'s (empty) variable lists, so the gather's seed needs no allocation. -/
  csVarlessVars : Array (Array VarId)
  biVars : Array (Array VarId)
  biItems : Array (DbItem p)
  biUsable : Array Bool
  biInformative : Array Bool
  biDomRed : Array Bool
  biBucket : Array (Array Nat)
  /-- The variable-free usable interactions' summary (`DenseBusVarlessSummary`). -/
  biVarlessCount : Nat
  biVarlessInformative : Bool
  biVarlessDomRed : Bool
  constOk : Bool

def dbNvOf (vs : Array (Array VarId)) (m : Nat) : Nat :=
  vs.foldl (init := m) fun acc a => a.foldl (fun b v => max b (v.index + 1)) acc

/-- Phase 1: constraint-sourced domains, one root plan per constraint (≤ 3 distinct variables). -/
def dbConstraintPhase (cs : Array (DenseExpr p)) (csVars : Array (Array VarId)) (k : Nat)
    (T : DbTab p) : DbTab p :=
  if h : k < cs.size then
    let vs := csVars.getD k #[]
    let T := if vs.size ≤ 3 then dbAddConstraintVars cs[k] vs 0 T else T
    dbConstraintPhase cs csVars (k + 1) T
  else T
  termination_by cs.size - k
  decreasing_by all_goals omega

/-- Phase 2a: resolve every `BusFacts` query about each interaction. -/
def dbPrePhase {bs : BusSemantics p} (facts : BusFacts p bs) (bc : DbBusCache p)
    (bis : Array (BusInteraction (DenseExpr p))) (biVars : Array (Array VarId)) (k : Nat)
    (out : Array (DbBiPre p)) : Array (DbBiPre p) :=
  if h : k < bis.size then
    dbPrePhase facts bc bis biVars (k + 1) (out.push (dbPreOne facts bc bis[k] (biVars.getD k #[])))
  else out
  termination_by bis.size - k
  decreasing_by all_goals omega

/-- Phase 2: bus slot bounds and `informative`, one payload walk per interaction. -/
def dbBusPhase {bs : BusSemantics p} (facts : BusFacts p bs)
    (bis : Array (BusInteraction (DenseExpr p))) (pre : Array (DbBiPre p)) (k : Nat)
    (st : DbTab p × Array Bool) : DbTab p × Array Bool :=
  if h : k < bis.size then
    let ⟨T, inf⟩ := st
    let e := pre.getD k dbBiPreEmpty
    let (i, T) := dbBusSlots facts bis[k] e.mult? e.pat bis[k].payload e.pat 0
      (Array.emptyWithCapacity 4) false T
    dbBusPhase facts bis pre (k + 1) ⟨T, inf.push i⟩
  else st
  termination_by bis.size - k
  decreasing_by all_goals omega

/-- Phase 3: byte-operand domains (reads the table phase 2 produced). -/
def dbBytePhase (pre : Array (DbBiPre p)) (k : Nat) (T : DbTab p) : DbTab p :=
  if h : k < pre.size then
    dbBytePhase pre (k + 1) (dbAddByteBi pre[k] T)
  else T
  termination_by pre.size - k
  decreasing_by all_goals omega

/-- Phase 4: the per-constraint scan program and its `active` (`¬ redundant`) verdict, in one
    traversal. An item with a variable outside the table can never be gathered (a target's keys are
    all domained), so it needs neither a program nor a verdict. -/
def dbCsPhase {bs : BusSemantics p} (facts : BusFacts p bs) (T : DbTab p)
    (cs : Array (DenseExpr p)) (csVars : Array (Array VarId)) (k : Nat)
    (st : Array Nat × Array (DbItem p) × Array Bool) :
    Array Nat × Array (DbItem p) × Array Bool :=
  if h : k < cs.size then
    let ⟨regs, items, act⟩ := st
    let vs := csVars.getD k #[]
    let item := if (dbBoxOf T vs 0 1).isSome then DbItem.zero cs[k] else DbItem.always
    let ⟨regs, red⟩ := dbConstraintRedundant facts T item vs regs
    dbCsPhase facts T cs csVars (k + 1) ⟨regs, items.push item, act.push (!red)⟩
  else st
  termination_by cs.size - k
  decreasing_by all_goals omega

/-- Phase 5: the per-interaction scan program and its domain-redundancy verdict (same gate). -/
def dbBiItemPhase {bs : BusSemantics p} (facts : BusFacts p bs) (bc : DbBusCache p) (T : DbTab p)
    (bis : Array (BusInteraction (DenseExpr p))) (pre : Array (DbBiPre p)) (k : Nat)
    (st : Array (DbItem p) × Array Bool) : Array (DbItem p) × Array Bool :=
  if h : k < bis.size then
    let ⟨items, dred⟩ := st
    let e := pre.getD k dbBiPreEmpty
    let gather := e.usable && (dbBoxOf T e.vars 0 1).isSome
    let item := if gather then dbCompileBi facts bc bis[k] e else DbItem.always
    dbBiItemPhase facts bc T bis pre (k + 1)
      ⟨items.push item, dred.push (gather && dbBiDomainRedundant facts bc T bis[k] e)⟩
  else st
  termination_by bis.size - k
  decreasing_by all_goals omega

def dbBucketsOf (nv : Nat) (vars : Array (Array VarId)) : Array (Array Nat) × Array Nat :=
  vars.zipIdx.foldl (init := (Array.replicate nv (#[] : Array Nat), (#[] : Array Nat)))
    fun st vi =>
      let ⟨buckets, varless⟩ := st
      match vi.1[0]? with
      | none => ⟨buckets, varless.push vi.2⟩
      | some v => ⟨buckets.modify v.index (fun b => b.push vi.2), varless⟩

/-- `denseVarsInListF`: every variable of the item is a key of the target. The target's keys are
    stamped into `mark` with the current generation before the gather, so the test is `|vs|` array
    reads rather than `|vs| · |xs|` comparisons behind a closure. -/
def dbSubset (mark : Array Nat) (gen : Nat) (vs : Array VarId) (k : Nat) : Bool :=
  if h : k < vs.size then
    if mark.getD vs[k].index 0 == gen then dbSubset mark gen vs (k + 1) else false
  else true
  termination_by vs.size - k
  decreasing_by all_goals omega

def dbStamp (mark : Array Nat) (gen : Nat) (xs : Array VarId) (k : Nat) : Array Nat :=
  if h : k < xs.size then dbStamp (mark.set! xs[k].index gen) gen xs (k + 1) else mark
  termination_by xs.size - k
  decreasing_by all_goals omega

/-! ## Gather and preflight -/

structure DbGather (p : ℕ) where
  fullCount : Nat
  activeCs : Nat
  biCount : Nat
  informative : Bool
  domRed : Bool
  items : Array (DbItem p)
  /-- Each gathered item's distinct variables, parallel to `items`; the scan reads them to place
      the item at the depth of its innermost key. -/
  ivars : Array (Array VarId)

def dbGatherCsAt (ctx : DbCtx p) (mark : Array Nat) (gen : Nat) (g : DbGather p) (pos : Nat) :
    DbGather p :=
  if dbSubset mark gen (ctx.csVars.getD pos #[]) 0 then
    let ⟨fullCount, activeCs, biCount, informative, domRed, items, ivars⟩ := g
    if ctx.csActive.getD pos false then
      ⟨fullCount + 1, activeCs + 1, biCount, informative, domRed,
        items.push (ctx.csItems.getD pos .always), ivars.push (ctx.csVars.getD pos #[])⟩
    else ⟨fullCount + 1, activeCs, biCount, informative, domRed, items, ivars⟩
  else g

def dbGatherBiAt (ctx : DbCtx p) (mark : Array Nat) (gen : Nat) (g : DbGather p) (pos : Nat) :
    DbGather p :=
  if ctx.biUsable.getD pos false && dbSubset mark gen (ctx.biVars.getD pos #[]) 0 then
    let ⟨fullCount, activeCs, biCount, informative, domRed, items, ivars⟩ := g
    ⟨fullCount, activeCs, biCount + 1, informative || ctx.biInformative.getD pos false,
      domRed && ctx.biDomRed.getD pos false, items.push (ctx.biItems.getD pos .always),
      ivars.push (ctx.biVars.getD pos #[])⟩
  else g

def dbGather (ctx : DbCtx p) (mark : Array Nat) (gen : Nat) (xs : Array VarId) : DbGather p :=
  let g0 : DbGather p :=
    { fullCount := ctx.csVarlessCount, activeCs := ctx.csVarlessItems.size,
      biCount := ctx.biVarlessCount, informative := ctx.biVarlessInformative,
      domRed := ctx.biVarlessDomRed, items := ctx.csVarlessItems,
      ivars := ctx.csVarlessVars }
  xs.foldl (init := g0) fun g v =>
    let g := (ctx.csBucket.getD v.index #[]).foldl (dbGatherCsAt ctx mark gen) g
    (ctx.biBucket.getD v.index #[]).foldl (dbGatherBiAt ctx mark gen) g

/-- Constant-domain answers for a target that needs no scan (`denseConstantDomainsV`). -/
def dbConstantDomains (p : ℕ) (keys : Array VarId) (doms : Array (DbDom)) :
    List (VarId × ZMod p) :=
  (keys.zipIdx.foldr (init := []) fun ki acc =>
    match DbDom.const? p (doms.getD ki.2 (.range 0)) with
    | some c => (ki.1, zmodOfNatP p c) :: acc
    | none => acc)

def dbPreflight (ctx : DbCtx p) (mark : Array Nat) (gen : Nat) (xs : Array VarId) :
    Option (DbPlan p) :=
  match dbDomsOf ctx.T xs with
  | none => none
  | some doms =>
    let box := doms.foldl (fun acc d => acc * d.size) 1
    if box ≤ maxEnumSize then
      let g := dbGather ctx mark gen xs
      let informative := g.fullCount != 0 || g.informative
      if informative && box * (g.fullCount + g.biCount) ≤ maxEnumWork then
        if g.activeCs == 0 && g.domRed && doms.all (fun d => d.size != 0) then
          some (.done (dbConstantDomains p xs doms))
        else
          let ⟨keys, kdoms⟩ := dbOrderKeys ctx.T xs doms
          let ⟨items, ilev⟩ := dbLevelItems keys g.items g.ivars 0 #[] #[]
          some (.scan keys kdoms items ilev ctx.constOk)
      else none
    else none

/-! ## The target loop: gate, then dedup, then preflight -/

/-- The target loop's state: the dedup table, the membership stamps with their generation, and the
    plans built so far (in reverse). -/
structure DbTargetSt (p : ℕ) where
  seen : DbSeen
  mark : Array Nat
  gen : Nat
  plans : List (DbPlan p)

def dbTargetStep (ctx : DbCtx p) (xs : Array VarId) (st : DbTargetSt p) : DbTargetSt p :=
  if xs.isEmpty then st
  else
    -- cheap gate first: every variable domained, and the box within the enumeration cap
    match dbBoxOf ctx.T xs 0 1 with
    | none => st
    | some box =>
      if maxEnumSize < box then st
      else
        let ⟨seen, mark, gen, plans⟩ := st
        let ⟨isNew, seen⟩ := seen.insertNew (dbKeyHash xs) xs
        if !isNew then ⟨seen, mark, gen, plans⟩
        else
          let gen := gen + 1
          let mark := dbStamp mark gen xs 0
          match dbPreflight ctx mark gen xs with
          | none => ⟨seen, mark, gen, plans⟩
          | some plan => ⟨seen, mark, gen, plan :: plans⟩

def dbTargetsCs (ctx : DbCtx p) (k : Nat) (st : DbTargetSt p) : DbTargetSt p :=
  if h : k < ctx.csVars.size then
    dbTargetsCs ctx (k + 1) (dbTargetStep ctx ctx.csVars[k] st)
  else st
  termination_by ctx.csVars.size - k
  decreasing_by all_goals omega

def dbTargetsBis (ctx : DbCtx p) (k : Nat) (st : DbTargetSt p) : DbTargetSt p :=
  if h : k < ctx.biVars.size then
    dbTargetsBis ctx (k + 1) (dbTargetStep ctx ctx.biVars[k] st)
  else st
  termination_by ctx.biVars.size - k
  decreasing_by all_goals omega

/-! ## The invocation -/

/-- Build the context: variable lists, the three table phases, the flags and the buckets. -/
def dbBuildCtx (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    DbCtx p :=
  let cs := d.algebraicConstraints.toArray
  let bis := d.busInteractions.toArray
  let csVars := cs.map (fun c => dbVarsOf c (Array.emptyWithCapacity 4))
  let biVars := bis.map dbBiVars
  let nv := dbNvOf biVars (dbNvOf csVars 0)
  let T0 : DbTab p := ⟨Array.replicate nv none⟩
  let T1 := dbConstraintPhase cs csVars 0 T0
  let bc := dbBusCacheOf facts (bis.foldl (fun m b => max m (b.busId + 1)) 0)
  let pre := dbPrePhase facts bc bis biVars 0 #[]
  let ⟨T2, biInf⟩ := dbBusPhase facts bis pre 0 ⟨T1, #[]⟩
  let T := dbBytePhase pre 0 T2
  let ⟨_, csItems, csActive⟩ := dbCsPhase facts T cs csVars 0 ⟨Array.replicate nv 0, #[], #[]⟩
  let ⟨biItems, biDomRed⟩ := dbBiItemPhase facts bc T bis pre 0 ⟨#[], #[]⟩
  let ⟨csBucket, csVarless⟩ := dbBucketsOf nv csVars
  let ⟨biBucket, biVarless⟩ := dbBucketsOf nv biVars
  let csVarlessItems := csVarless.filterMap (fun i =>
    if csActive.getD i false then some (csItems.getD i .always) else none)
  -- the variable-free usable interactions' summary (entry 155): count, flags and the constant
  -- verdict their obligations already decide
  let biSummary := biVarless.foldl (init := (0, false, true, true)) fun s i =>
    let e := pre.getD i dbBiPreEmpty
    if e.usable then
      (s.1 + 1, s.2.1 || biInf.getD i false, s.2.2.1 && biDomRed.getD i false,
        s.2.2.2 && dbItemOk facts #[] (biItems.getD i .always))
    else s
  { nv, T, csVars, csItems, csActive, csBucket,
    csVarlessCount := csVarless.size, csVarlessItems,
    csVarlessVars := Array.replicate csVarlessItems.size #[],
    biVars, biItems,
    biUsable := pre.map (fun e => e.usable),
    biInformative := biInf,
    biDomRed, biBucket,
    biVarlessCount := biSummary.1, biVarlessInformative := biSummary.2.1,
    biVarlessDomRed := biSummary.2.2.1, constOk := biSummary.2.2.2 }

/-! ## The fused context build

`dbBuildCtx` makes eleven passes over the system (two `toArray`s, two var-list maps, two `dbNvOf`
folds, four table/item phases, two `zipIdx` bucket folds). The fused build makes four, walking
the lists directly: constraints (vars + roots + the running variable bound in one pass),
interactions (vars + resolved facts + slot bounds in one pass), then — once the table is final —
one item pass per side that also fills the buckets and the varless summaries in place. The
domain table grows on demand (`insertG`), since the variable bound is not known until the walks
finish; every read is a `getD`, so a short table reads exactly like the `nv`-sized one. -/

def DbTab.insertG (T : DbTab p) (i : Nat) (d : DbDom) : DbTab p :=
  let ⟨dom⟩ := T
  let dom := if i < dom.size then dom
    else dom ++ Array.replicate (max (dom.size * 2) (i + 1) - dom.size) none
  match dom.getD i none with
  | some d0 => if d.size < d0.size then ⟨dom.set! i (some d)⟩ else ⟨dom⟩
  | none => ⟨dom.set! i (some d)⟩

def dbAddConstraintVarsG (e : DenseExpr p) (vs : Array VarId) (k : Nat) (T : DbTab p) :
    DbTab p :=
  if h : k < vs.size then
    match dbRootsAt vs k e with
    | some rs =>
      dbAddConstraintVarsG e vs (k + 1) (T.insertG vs[k].index (.explicit (rs.map ZMod.val).toArray))
    | none => dbAddConstraintVarsG e vs (k + 1) T
  else T
  termination_by vs.size - k
  decreasing_by all_goals omega

def dbBusSlotsG {bs : BusSemantics p} (facts : BusFacts p bs) (bi : BusInteraction (DenseExpr p))
    (mult? : Option (ZMod p)) (pat : List (Option (ZMod p))) :
    List (DenseExpr p) → List (Option (ZMod p)) → Nat → Array VarId → Bool → DbTab p →
      Bool × DbTab p
  | [], _, _, _, inf, T => (inf, T)
  | e :: rest, ps, slot, seen, inf, T =>
    let pRest := ps.tail
    match e with
    | .var i =>
      if seen.contains i then dbBusSlotsG facts bi mult? pat rest pRest (slot + 1) seen inf T
      else
        match dbSlotBound facts bi mult? pat slot with
        | none => dbBusSlotsG facts bi mult? pat rest pRest (slot + 1) (seen.push i) true T
        | some bound =>
          let T := if bound ≤ maxDomainBound then T.insertG i.index (.range bound) else T
          dbBusSlotsG facts bi mult? pat rest pRest (slot + 1) (seen.push i) inf T
    | _ =>
      dbBusSlotsG facts bi mult? pat rest pRest (slot + 1) seen
        (inf || !(ps.head?.getD none).isSome) T

/-- Walk 1: variable lists, constraint roots and the running variable bound, one pass. -/
def dbCsWalk (cs : List (DenseExpr p)) (csVars : Array (Array VarId)) (nv : Nat) (T : DbTab p) :
    Array (Array VarId) × Nat × DbTab p :=
  match cs with
  | [] => (csVars, nv, T)
  | c :: rest =>
    let vs := dbVarsOf c (Array.emptyWithCapacity 4)
    let nv := vs.foldl (init := nv) fun b v => max b (v.index + 1)
    let T := if vs.size ≤ 3 then dbAddConstraintVarsG c vs 0 T else T
    dbCsWalk rest (csVars.push vs) nv T

/-- Walk 2: per-interaction variables, resolved facts and slot bounds, one pass. -/
def dbBiWalk {bs : BusSemantics p} (facts : BusFacts p bs) (bc : DbBusCache p)
    (bis : List (BusInteraction (DenseExpr p))) (biVars : Array (Array VarId))
    (pre : Array (DbBiPre p)) (inf : Array Bool) (nv : Nat) (T : DbTab p) :
    Array (Array VarId) × Array (DbBiPre p) × Array Bool × Nat × DbTab p :=
  match bis with
  | [] => (biVars, pre, inf, nv, T)
  | bi :: rest =>
    let vars := dbBiVars bi
    let nv := vars.foldl (init := nv) fun b v => max b (v.index + 1)
    let e := dbPreOne facts bc bi vars
    let (i, T) := dbBusSlotsG facts bi e.mult? e.pat bi.payload e.pat 0
      (Array.emptyWithCapacity 4) false T
    dbBiWalk facts bc rest (biVars.push vars) (pre.push e) (inf.push i) nv T

/-- Walk 3: per-constraint items, `active` verdicts, buckets and the varless items, one pass
    over the final table. -/
def dbCsWalk2 {bs : BusSemantics p} (facts : BusFacts p bs) (T : DbTab p)
    (cs : List (DenseExpr p)) (csVars : Array (Array VarId)) (k : Nat) (regs : Array Nat)
    (items : Array (DbItem p)) (act : Array Bool) (buckets : Array (Array Nat))
    (vlCount : Nat) (vlItems : Array (DbItem p)) :
    Array (DbItem p) × Array Bool × Array (Array Nat) × Nat × Array (DbItem p) :=
  match cs with
  | [] => (items, act, buckets, vlCount, vlItems)
  | c :: rest =>
    let vs := csVars.getD k #[]
    let item := if (dbBoxOf T vs 0 1).isSome then DbItem.zero c else DbItem.always
    let (regs, red) := dbConstraintRedundant facts T item vs regs
    match vs[0]? with
    | some v =>
      dbCsWalk2 facts T rest csVars (k + 1) regs (items.push item) (act.push (!red))
        (buckets.modify v.index (fun b => b.push k)) vlCount vlItems
    | none =>
      dbCsWalk2 facts T rest csVars (k + 1) regs (items.push item) (act.push (!red)) buckets
        (vlCount + 1) (if !red then vlItems.push item else vlItems)

/-- Walk 4: per-interaction items, domain-redundancy verdicts, buckets and the varless summary
    (count, informative, domain-redundant, constant verdict), one pass over the final table. -/
def dbBiWalk2 {bs : BusSemantics p} (facts : BusFacts p bs) (bc : DbBusCache p) (T : DbTab p)
    (bis : List (BusInteraction (DenseExpr p))) (pre : Array (DbBiPre p)) (biInf : Array Bool)
    (k : Nat) (items : Array (DbItem p)) (dred : Array Bool) (buckets : Array (Array Nat))
    (summary : Nat × Bool × Bool × Bool) :
    Array (DbItem p) × Array Bool × Array (Array Nat) × (Nat × Bool × Bool × Bool) :=
  match bis with
  | [] => (items, dred, buckets, summary)
  | bi :: rest =>
    let e := pre.getD k dbBiPreEmpty
    let gather := e.usable && (dbBoxOf T e.vars 0 1).isSome
    let item := if gather then dbCompileBi facts bc bi e else DbItem.always
    let dr := gather && dbBiDomainRedundant facts bc T bi e
    match e.vars[0]? with
    | some v =>
      dbBiWalk2 facts bc T rest pre biInf (k + 1) (items.push item) (dred.push dr)
        (buckets.modify v.index (fun b => b.push k)) summary
    | none =>
      let summary := if e.usable then
          (summary.1 + 1, summary.2.1 || biInf.getD k false, summary.2.2.1 && dr,
            summary.2.2.2 && dbItemOk facts #[] item)
        else summary
      dbBiWalk2 facts bc T rest pre biInf (k + 1) (items.push item) (dred.push dr) buckets
        summary

/-- `dbBuildCtx` in four passes (behaviorally identical: same arrays, same table content). -/
def dbBuildCtxFast (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    DbCtx p :=
  let (csVars, nv1, T1) := dbCsWalk d.algebraicConstraints #[] 0 ⟨#[]⟩
  let bc := dbBusCacheOf facts (d.busInteractions.foldl (fun m b => max m (b.busId + 1)) 0)
  let (biVars, pre, biInf, nv, T2) := dbBiWalk facts bc d.busInteractions #[] #[] #[] nv1 T1
  let T := dbBytePhase pre 0 T2
  let (csItems, csActive, csBucket, csVlCount, csVarlessItems) :=
    dbCsWalk2 facts T d.algebraicConstraints csVars 0 (Array.replicate nv 0) #[] #[]
      (Array.replicate nv #[]) 0 #[]
  let (biItems, biDomRed, biBucket, biSummary) :=
    dbBiWalk2 facts bc T d.busInteractions pre biInf 0 #[] #[] (Array.replicate nv #[])
      (0, false, true, true)
  { nv, T, csVars, csItems, csActive, csBucket,
    csVarlessCount := csVlCount, csVarlessItems,
    csVarlessVars := Array.replicate csVarlessItems.size #[],
    biVars, biItems,
    biUsable := pre.map (fun e => e.usable),
    biInformative := biInf,
    biDomRed, biBucket,
    biVarlessCount := biSummary.1, biVarlessInformative := biSummary.2.1,
    biVarlessDomRed := biSummary.2.2.1, constOk := biSummary.2.2.2 }

/-! ## The exit substitution

`applyσ` probes a `Std.HashMap` at every variable leaf of every expression. The solution map holds a
few thousand entries against tens of thousands of live variables, so the forced constants are
collected into a `VarId.index`-keyed array instead and the substitution reads that. -/

/-- The forced constants as a `VarId.index`-keyed array, and whether anything was forced. -/
def dbSolvedOf (nv : Nat) (results : List (List (VarId × ZMod p))) :
    Array (Option (ZMod p)) × Bool :=
  results.foldl (init := (Array.replicate nv none, false)) fun st forced =>
    forced.foldl (init := st) fun st f => (st.1.set! f.1.index (some f.2), true)

@[inline] def dbSubstFn (σ : Array (Option (ZMod p))) (i : VarId) : Option (DenseExpr p) :=
  (σ.getD i.index none).map DenseExpr.const

/-- Domain-batch: builds a finite domain per variable (from constraints like `x*(x-1)=0` giving
    `x ∈ {0,1}`, and from bus range checks), enumerates the small Cartesian product of those
    domains, and for each variable that takes the same value in every surviving assignment infers
    that forced constant. Returns the map of all such `var := const` substitutions. -/
def dbDomainBatchσ (bs : BusSemantics p) (facts : BusFacts p bs) (d : DenseConstraintSystem p) :
    Array (Option (ZMod p)) × Bool :=
  let ctx := dbBuildCtx bs facts d
  let st0 : DbTargetSt p := ⟨⟨∅⟩, Array.replicate ctx.nv 0, 0, []⟩
  let plans := (dbTargetsBis ctx 0 (dbTargetsCs ctx 0 st0)).plans.reverse
  -- run serially: handing plans to `Task.spawn` marks the shared objects multi-threaded, and every
  -- later refcount touch on them — in this pass and in every pass after it — becomes atomic
  dbSolvedOf ctx.nv (dbRunPlans facts ctx.nv plans)

/-- The value-only dense domain-batch transform, over the rebuilt engine. -/
def dbDomainBatchTransform (pw : PrimeWitness p) (bs : BusSemantics p)
    (facts : BusFacts p bs) (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  if pw.isPrime = true then
    let r := dbDomainBatchσ bs facts d
    if r.2 then d.substF (dbSubstFn r.1) else d
  else d

/-- `dbDomainBatchTransform` with the σ-array allocation skipped when nothing was forced. The
    substitution itself stays a full rebuild: a mention-gated variant that keeps unchanged items
    as shared pointers measures faster in-pass and slower end-to-end (sharing disables Lean's
    reset/reuse in every downstream pass — the entry-169 dead end, reproduced here). -/
def dbDomainBatchTransformFast (pw : PrimeWitness p) (bs : BusSemantics p)
    (facts : BusFacts p bs) (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  if pw.isPrime = true then
    let ctx := dbBuildCtxFast bs facts d
    let st0 : DbTargetSt p := ⟨⟨∅⟩, Array.replicate ctx.nv 0, 0, []⟩
    let plans := (dbTargetsBis ctx 0 (dbTargetsCs ctx 0 st0)).plans.reverse
    -- run serially: handing plans to `Task.spawn` marks the shared objects multi-threaded, and
    -- every later refcount touch on them — here and in every pass after — becomes atomic
    let results := dbRunPlans facts ctx.nv plans
    if results.all List.isEmpty then d
    else d.substF (dbSubstFn (dbSolvedOf ctx.nv results).1)
  else d

attribute [implemented_by dbDomainBatchTransformFast] dbDomainBatchTransform

end ApcOptimizer.Dense
