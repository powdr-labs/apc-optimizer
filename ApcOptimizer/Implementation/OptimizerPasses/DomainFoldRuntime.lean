import ApcOptimizer.Implementation.OptimizerPasses.DomainFold
import ApcOptimizer.Implementation.OptimizerPasses.DomainTable

set_option autoImplicit false

/-! # Dense `domainFold`

For a group of variables pinned to finite domains by "covered" constraints, enumerate the surviving
joint assignments and replace every maximal wholly-in-group subexpression that is constant across all
survivors by that constant: if the covered constraints force `x + y = 1` on every survivor, each
`x + y` subterm folds to `1`.

One invocation builds three index-keyed tables — the candidate groups and per-item variable lists
(`dfScanGo`), the position buckets (`dfCsBuckets`/`dfBisBuckets`) and the per-variable domains
(`dfDoms`) — and then folds each group in turn through one fused traversal (`dfGo`), which carries
both the survivor value of every node and the rewrite. Runtime only — correctness is in
`Proofs/DomainFold.lean`, `domainFoldRedesign.md` has the design. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- Insert into a `VarId.index`-ascending, duplicate-free list; `none` if `v` is already there, so a
    repeated occurrence costs a walk and no allocation. -/
def dfInsVar (v : VarId) : List VarId → Option (List VarId)
  | [] => some [v]
  | x :: rest =>
    if v.index < x.index then some (v :: x :: rest)
    else if v.index == x.index then none
    else (dfInsVar v rest).map (x :: ·)

/-- Is the list longer than `cap`? Walks at most `cap + 1` cells. -/
def dfLongerThan (cap : Nat) : List VarId → Bool
  | [] => false
  | _ :: rest => match cap with
    | 0 => true
    | cap + 1 => dfLongerThan cap rest

/-- The distinct variables of `e`, ascending by `VarId.index`; `none` once past `cap` of them, so
    oversized items abort instead of being fully deduplicated. -/
def dfVarsGo (cap : Nat) : DenseExpr p → Option (List VarId) → Option (List VarId)
  | _, none => none
  | .const _, acc => acc
  | .var i, some acc =>
      match dfInsVar i acc with
      | none => some acc
      | some a => if dfLongerThan cap a then none else some a
  | .add a b, acc => dfVarsGo cap b (dfVarsGo cap a acc)
  | .mul a b, acc => dfVarsGo cap b (dfVarsGo cap a acc)

/-- The largest index of an ascending `VarId` list. -/
def dfLastIdx : List VarId → Nat
  | [] => 0
  | [x] => x.index
  | _ :: rest => dfLastIdx rest

/-- One traversal of the constraints: the single-variable constraints' `(position, variable)` in
    reverse order (both `denseSvSet` and the domain sources), the 2–8-variable target candidate keys
    in reverse order (already in `denseVarSetKey` form), and the largest index seen. -/
def dfScanGo : List (DenseExpr p) → Nat → Nat → List (Nat × VarId) → List (List VarId) →
    Array (Option (List VarId)) → Nat × List (Nat × VarId) × List (List VarId) ×
      Array (Option (List VarId))
  | [], _, mx, sv, cand, dvs => (mx, sv, cand, dvs)
  | c :: rest, q, mx, sv, cand, dvs =>
    match dfVarsGo 8 c (some []) with
    | some [x] => dfScanGo rest (q + 1) (max mx x.index) ((q, x) :: sv) cand (dvs.push (some [x]))
    | some (x :: y :: more) =>
        dfScanGo rest (q + 1) (max mx (dfLastIdx (x :: y :: more))) sv ((x :: y :: more) :: cand)
          (dvs.push (some (x :: y :: more)))
    | some [] => dfScanGo rest (q + 1) mx sv cand (dvs.push (some []))
    | none => dfScanGo rest (q + 1) mx sv cand (dvs.push none)

/-- Mark a variable list in an index-keyed `Bool` table. -/
def dfMarkVars (vs : List VarId) (a : Array Bool) : Array Bool :=
  match vs with
  | [] => a
  | v :: rest => dfMarkVars rest (a.setIfInBounds v.index true)

/-- Mark every variable of every target key. -/
def dfMarkKeys (ks : List (Array VarId)) (a : Array Bool) : Array Bool :=
  match ks with
  | [] => a
  | k :: rest => dfMarkKeys rest (dfMarkVars k.toList a)

/-- The target keys: the candidates all of whose variables are `isSv`, deduplicated keeping each
    key's last occurrence (`dedupHash`'s order) — the input is the *reversed* candidate list, and the
    seen set is bucketed by the key's smallest variable index, so no key is ever hashed. -/
def dfDedupKeys (isSv : Array Bool) : List (List VarId) → Array (List (List VarId)) →
    List (Array VarId) → List (Array VarId)
  | [], _, acc => acc
  | vs :: rest, buckets, acc =>
    let h := (vs.head?.map VarId.index).getD 0
    let b := buckets.getD h []
    if b.contains vs then dfDedupKeys isSv rest buckets acc
    else
      let buckets := buckets.setIfInBounds h (vs :: b)
      if vs.all (fun v => isSv.getD v.index false) then
        dfDedupKeys isSv rest buckets (vs.toArray :: acc)
      else dfDedupKeys isSv rest buckets acc

/-- Push item position `q` under every target variable `e` mentions; duplicates are dropped against
    the bucket's last entry, so each bucket is strictly ascending. -/
def dfBucketGo (isTgt : Array Bool) (q : Nat) : DenseExpr p → Array (Array Nat) → Array (Array Nat)
  | .const _, bs => bs
  | .var v, bs =>
      if isTgt.getD v.index false then
        bs.modify v.index (fun b => if b.back? == some q then b else b.push q)
      else bs
  | .add a b, bs => dfBucketGo isTgt q b (dfBucketGo isTgt q a bs)
  | .mul a b, bs => dfBucketGo isTgt q b (dfBucketGo isTgt q a bs)

/-- Push `q` under every target variable of a known distinct-variable list. -/
def dfBucketVars (isTgt : Array Bool) (q : Nat) : List VarId → Array (Array Nat) →
    Array (Array Nat)
  | [], bs => bs
  | v :: rest, bs =>
      dfBucketVars isTgt q rest
        (if isTgt.getD v.index false then bs.modify v.index (fun b => b.push q) else bs)

/-- The constraint buckets, served from the scan's per-constraint distinct-variable lists; only the
    items the scan gave up on (over the 8-variable cap) are walked again. -/
def dfCsBuckets (isTgt : Array Bool) (dvs : Array (Option (List VarId))) :
    Nat → List (DenseExpr p) → Array (Array Nat) → Array (Array Nat)
  | _, [], bs => bs
  | q, c :: rest, bs =>
    match dvs.getD q none with
    | some vs => dfCsBuckets isTgt dvs (q + 1) rest (dfBucketVars isTgt q vs bs)
    | none => dfCsBuckets isTgt dvs (q + 1) rest (dfBucketGo isTgt q c bs)

def dfBiBucketGo (isTgt : Array Bool) (q : Nat) : List (DenseExpr p) → Array (Array Nat) →
    Array (Array Nat)
  | [], bs => bs
  | e :: rest, bs => dfBiBucketGo isTgt q rest (dfBucketGo isTgt q e bs)

def dfBisBuckets (isTgt : Array Bool) : Nat → List (BusInteraction (DenseExpr p)) →
    Array (Array Nat) → Array (Array Nat)
  | _, [], bs => bs
  | q, bi :: rest, bs =>
      dfBisBuckets isTgt (q + 1) rest
        (dfBiBucketGo isTgt q bi.payload (dfBucketGo isTgt q bi.multiplicity bs))

/-- A key's finite domain: the values, plus the position and the expression of the single-variable
    constraint that entails them. The pass never trusts the table — `dfKeyDoms` re-checks that the
    constraint is still there, which is what makes the domain entailed by the *current* system. -/
structure DfDom (p : ℕ) where
  vals : List (ZMod p)
  pos : Nat
  src : DenseExpr p

/-- The domain table and the 1-based source positions, from the single-variable constraints in
    position order: one `denseRootsIn` per target variable (first roots win), none for a variable no
    target needs. -/
def dfDoms (cs : Array (DenseExpr p)) (isTgt : Array Bool) (sv : List (Nat × VarId))
    (doms : Array (Option (DfDom p))) (src : Array Nat) :
    Array (Option (DfDom p)) × Array Nat :=
  match sv with
  | [] => (doms, src)
  | (q, x) :: rest =>
    if isTgt.getD x.index false && (doms.getD x.index none).isNone then
      if h : q < cs.size then
        match denseRootsIn x cs[q] with
        | some ds =>
            dfDoms cs isTgt rest (doms.setIfInBounds x.index (some ⟨ds, q, cs[q]⟩))
              (src.setIfInBounds x.index (q + 1))
        | none => dfDoms cs isTgt rest doms src
      else dfDoms cs isTgt rest doms src
    else dfDoms cs isTgt rest doms src

/-! ### Per-target key lookup and the covered test -/

/-- The position of `y` in the ascending key array, or `none`. -/
def dfSlotGo (keys : Array VarId) (y : Nat) (j : Nat) : Option Nat :=
  if h : j < keys.size then
    if keys[j].index == y then some j
    else if y < keys[j].index then none
    else dfSlotGo keys y (j + 1)
  else none
termination_by keys.size - j
decreasing_by all_goals omega

/-- `0` if a non-key variable occurs, `2` if every variable is a key and at least one occurs, `1` if
    variable-free — one short-circuiting walk for `denseCoveredBy`'s two. -/
def dfCovGo (keys : Array VarId) : DenseExpr p → Nat
  | .const _ => 1
  | .var y => if (dfSlotGo keys y.index 0).isSome then 2 else 0
  | .add a b | .mul a b =>
      let ra := dfCovGo keys a
      if ra == 0 then 0 else
      let rb := dfCovGo keys b
      if rb == 0 then 0 else max ra rb

def dfCoveredBy (keys : Array VarId) (c : DenseExpr p) : Bool := dfCovGo keys c == 2

/-! ### The survivor enumeration -/

/-- The largest key slot `e` reads — the level at which it becomes fully assigned, keys being
    assigned in increasing order. `none` if it reads no key. -/
def dfMaxSlot (keys : Array VarId) : DenseExpr p → Option Nat
  | .const _ => none
  | .var y => dfSlotGo keys y.index 0
  | .add a b | .mul a b =>
      match dfMaxSlot keys a, dfMaxSlot keys b with
      | some x, some y => some (max x y)
      | some x, none => some x
      | none, r => r

/-- The keys assigned up to level `m`, newest first — the key list a level-`m` partial point is the
    values of, so compiling a filter against it *is* the level-relative re-indexing. -/
def dfRKeys (keys : Array VarId) : Nat → List VarId
  | 0 => [keys.getD 0 ⟨0⟩]
  | m + 1 => keys.getD (m + 1) ⟨0⟩ :: dfRKeys keys m

/-- Evaluate a level-shifted filter on `v :: pt` without building the cons cell. Calls the field
    primitives directly: a `DenseZModOps` field is a closure, and this is the hottest loop of the
    pass. -/
def dfEvalCons (zero v : ZMod p) (pt : List (ZMod p)) : IExpr p → ZMod p
  | .const n => n
  | .ix 0 => v
  | .ix (i + 1) => denseLookupIxV zero pt i
  | .add a b => zmodAddP (dfEvalCons zero v pt a) (dfEvalCons zero v pt b)
  | .mul a b => zmodMulP (dfEvalCons zero v pt a) (dfEvalCons zero v pt b)

/-- Do all of this level's filters vanish on `v :: pt`? Closure-free. -/
def dfAllZero (zero v : ZMod p) (pt : List (ZMod p)) : List (IExpr p) → Bool
  | [] => true
  | ie :: rest => zmodIsZero (dfEvalCons zero v pt ie) && dfAllZero zero v pt rest

/-- Extend one partial point by every domain value, keeping those that pass this level's filters. -/
def dfExtOne (zero : ZMod p) (ies : List (IExpr p)) (pt : List (ZMod p)) :
    List (ZMod p) → Array (List (ZMod p)) → Array (List (ZMod p))
  | [], out => out
  | v :: vs, out =>
      dfExtOne zero ies pt vs (if dfAllZero zero v pt ies then out.push (v :: pt) else out)

def dfExtLevel (zero : ZMod p) (ies : List (IExpr p)) (dom : List (ZMod p))
    (i : Nat) (pts : Array (List (ZMod p))) (out : Array (List (ZMod p))) :
    Array (List (ZMod p)) :=
  if h : i < pts.size then
    dfExtLevel zero ies dom (i + 1) pts (dfExtOne zero ies pts[i] dom out)
  else out
termination_by pts.size - i
decreasing_by all_goals omega

/-- The surviving joint assignments, as reversed prefixes: each partial point is shared by every
    extension of it (one cons per surviving point, no allocation for a rejected one), and every
    filter is checked the moment its largest-index variable is assigned. -/
def dfEnumGo (zero : ZMod p) (byLevel : Array (List (IExpr p))) (doms : Array (List (ZMod p)))
    (k : Nat) (j : Nat) (pts : Array (List (ZMod p))) : Array (List (ZMod p)) :=
  if pts.isEmpty then pts
  else if h : j < k then
    dfEnumGo zero byLevel doms k (j + 1)
      (dfExtLevel zero (byLevel.getD j []) (doms.getD j []) 0 pts #[])
  else pts
termination_by k - j
decreasing_by all_goals omega

/-! ### The fused gate-and-rewrite traversal -/

/-- A subexpression's rewrite together with its value across the survivors: `out` mentions a non-key
    variable, `uni` is constant on every survivor, `vec` holds the per-survivor values and is
    normalized (never constant). `out` — by far the most common result — carries nothing, and a
    folded node's rewrite is always `.const c`, so it is rebuilt on demand rather than stored:
    together that leaves the traversal allocation-free at every node it does not change. -/
inductive DfRes (p : ℕ) where
  | out
  | outCh (e : DenseExpr p)
  | uni (c : ZMod p) (fold : Bool)
  | vec (a : Array (ZMod p)) (e? : Option (DenseExpr p))

def DfRes.e? : DfRes p → Option (DenseExpr p)
  | .out => none
  | .outCh e => some e
  | .uni c fold => if fold then some (.const c) else none
  | .vec _ e? => e?

/-- `decide (a = b)` for `p = 0`, where `ZMod.val` is `Int.natAbs` and identifies `1` with `-1`;
    kept in its own function so its dictionary stays off `dfEqZ`. Dead at runtime (`p` is prime). -/
def dfEqSlow (a b : ZMod p) : Bool := decide (a = b)

/-- Dictionary-free `ZMod` equality; see `zmodIsOne`. -/
def dfEqZ (a b : ZMod p) : Bool := if p = 0 then dfEqSlow a b else a.val == b.val

/-- The constant value of a survivor vector, if it has one. -/
def dfUni (a : Array (ZMod p)) : Option (ZMod p) :=
  if h : 0 < a.size then
    if a.all (fun v => dfEqZ v a[0]) then some a[0] else none
  else none

/-- Rebuild a node only if a child changed. -/
@[inline] def dfRebuild (isAdd : Bool) (a b : DenseExpr p) (ra rb : Option (DenseExpr p)) :
    Option (DenseExpr p) :=
  match ra, rb with
  | none, none => none
  | _, _ => some (if isAdd then .add (ra.getD a) (rb.getD b) else .mul (ra.getD a) (rb.getD b))

/-- The field primitive selected by the node kind (see `dfEvalCons` on why not `DenseZModOps`). -/
@[inline] def dfOp (isAdd : Bool) (x y : ZMod p) : ZMod p :=
  if isAdd then zmodAddP x y else zmodMulP x y

/-- Combine an operation node's children: a `uni` result *is* "constant on every survivor", so the
    node folds to that constant. -/
@[inline] def dfComb (isAdd : Bool) (a b : DenseExpr p) (ra rb : DfRes p) : DfRes p :=
  match ra, rb with
  | .uni x _, .uni y _ => .uni (dfOp isAdd x y) true
  | .uni x _, .vec vb eb =>
      let s := vb.map (fun v => dfOp isAdd x v)
      match dfUni s with
      | some c => .uni c true
      | none => .vec s (dfRebuild isAdd a b ra.e? eb)
  | .vec va ea, .uni y _ =>
      let s := va.map (fun v => dfOp isAdd v y)
      match dfUni s with
      | some c => .uni c true
      | none => .vec s (dfRebuild isAdd a b ea rb.e?)
  | .vec va ea, .vec vb eb =>
      let s := Array.zipWith (dfOp isAdd) va vb
      match dfUni s with
      | some c => .uni c true
      | none => .vec s (dfRebuild isAdd a b ea eb)
  | _, _ =>
      match dfRebuild isAdd a b ra.e? rb.e? with
      | none => .out
      | some e => .outCh e

/-- The per-target fold context: the keys and each key's precomputed survivor column
    classification. -/
structure DfCtx (p : ℕ) where
  keys : Array VarId
  colRes : Array (DfRes p)

/-- The fused walk: one pass computes every node's survivor value and the rewrite in which every
    maximal constant in-key subexpression is replaced by its constant. -/
def dfGo (ctx : DfCtx p) : DenseExpr p → DfRes p
  | .const c => .uni c false
  | .var y =>
      match dfSlotGo ctx.keys y.index 0 with
      | some j => ctx.colRes.getD j .out
      | none => .out
  | .add a b => dfComb true a b (dfGo ctx a) (dfGo ctx b)
  | .mul a b => dfComb false a b (dfGo ctx a) (dfGo ctx b)

/-- Fold one expression. -/
def dfRewrite (ctx : DfCtx p) (e : DenseExpr p) : Option (DenseExpr p) := (dfGo ctx e).e?

def dfRewriteList (ctx : DfCtx p) : List (DenseExpr p) → Option (List (DenseExpr p))
  | [] => none
  | e :: rest =>
    match dfRewrite ctx e, dfRewriteList ctx rest with
    | none, none => none
    | r, rs => some (r.getD e :: rs.getD rest)

def dfRewriteBi (ctx : DfCtx p) (bi : BusInteraction (DenseExpr p)) :
    Option (BusInteraction (DenseExpr p)) :=
  match dfRewrite ctx bi.multiplicity, dfRewriteList ctx bi.payload with
  | none, none => none
  | m, pl => some { bi with multiplicity := m.getD bi.multiplicity, payload := pl.getD bi.payload }

/-! ### The per-target step -/

/-- The per-invocation index: the two position bucket tables, the domain table and the 1-based
    domain-source positions, all keyed by `VarId.index`. -/
structure DfIdx (p : ℕ) where
  csB : Array (Array Nat)
  bisB : Array (Array Nat)
  doms : Array (Option (DfDom p))
  src : Array Nat

/-- The nonempty buckets of the target's keys. -/
def dfSlices (buckets : Array (Array Nat)) (keys : Array VarId) : Array (Array Nat) :=
  keys.foldl (init := #[]) fun acc v =>
    let b := buckets.getD v.index #[]
    if b.isEmpty then acc else acc.push b

/-- The smallest unconsumed bucket head. -/
def dfMinHead (bs : Array (Array Nat)) (cur : Array Nat) (i : Nat) (best : Nat) (found : Bool) :
    Option Nat :=
  if h : i < bs.size then
    let b := bs[i]
    let c := cur.getD i 0
    if hc : c < b.size then
      let v := b[c]
      if !found || v < best then dfMinHead bs cur (i + 1) v true
      else dfMinHead bs cur (i + 1) best found
    else dfMinHead bs cur (i + 1) best found
  else if found then some best else none
termination_by bs.size - i
decreasing_by all_goals omega

/-- Consume `m` from every bucket whose head is `m`. -/
def dfAdvance (bs : Array (Array Nat)) (m : Nat) (i : Nat) (cur : Array Nat) : Array Nat :=
  if h : i < bs.size then
    let b := bs[i]
    let c := cur.getD i 0
    if hc : c < b.size then
      if b[c] == m then dfAdvance bs m (i + 1) (cur.setIfInBounds i (c + 1))
      else dfAdvance bs m (i + 1) cur
    else dfAdvance bs m (i + 1) cur
  else cur
termination_by bs.size - i
decreasing_by all_goals omega

def dfMergeGo (bs : Array (Array Nat)) (cur : Array Nat) (out : Array Nat) (fuel : Nat) :
    Array Nat :=
  match fuel with
  | 0 => out
  | fuel + 1 =>
    match dfMinHead bs cur 0 0 false with
    | none => out
    | some m => dfMergeGo bs (dfAdvance bs m 0 cur) (out.push m) fuel

/-- The target's touched positions: the ascending, deduplicated union of its keys' buckets. -/
def dfTouched (buckets : Array (Array Nat)) (keys : Array VarId) : Array Nat :=
  let bs := dfSlices buckets keys
  dfMergeGo bs (Array.replicate bs.size 0) #[] (bs.foldl (fun n b => n + b.size) 0)

/-- The keys' domains, all-or-nothing, each re-checked against the current system: the entailing
    single-variable constraint must still sit at its position and be covered by the keys (so the fold
    keeps it verbatim, and the domain is entailed by the system the fold is applied to). -/
def dfKeyDomsGo (tbl : Array (Option (DfDom p))) (keys : Array VarId) (cs : Array (DenseExpr p)) :
    List VarId → Option (List (List (ZMod p)))
  | [] => some []
  | v :: rest =>
    match tbl.getD v.index none with
    | some dm =>
        if dm.pos < cs.size && cs.getD dm.pos (.const (zmodZeroP p)) == dm.src &&
            dfCoveredBy keys dm.src then
          (dfKeyDomsGo tbl keys cs rest).map (fun ds => dm.vals :: ds)
        else none
    | none => none

def dfKeyDoms (tbl : Array (Option (DfDom p))) (keys : Array VarId) (cs : Array (DenseExpr p)) :
    Option (Array (List (ZMod p))) :=
  (dfKeyDomsGo tbl keys cs keys.toList).map List.toArray

/-- Is position `q` the domain source of one of the keys? Such a constraint is zero at every box
    point by construction, so it never rejects one. -/
def dfIsSrc (src : Array Nat) (keys : Array VarId) (q : Nat) : Bool :=
  keys.any (fun v => src.getD v.index 0 == q + 1)

/-- Walk the touched constraints once: the positions the fold has to rewrite (the non-covered ones),
    and the compiled filters the enumeration needs (the covered ones that are not domain sources,
    each compiled against its own level's reversed key prefix). -/
def dfCovScan (keys : Array VarId) (src : Array Nat) (cs : Array (DenseExpr p))
    (touched : Array Nat) (i : Nat) (fold : List Nat) (filters : List (Nat × IExpr p)) :
    List Nat × List (Nat × IExpr p) :=
  if h : i < touched.size then
    let q := touched[i]
    let c := cs.getD q (.const (zmodZeroP p))
    if dfCoveredBy keys c then
      if dfIsSrc src keys q then dfCovScan keys src cs touched (i + 1) fold filters
      else
        match dfMaxSlot keys c with
        | some m =>
            match denseCompileE (dfRKeys keys m) c with
            | some ie => dfCovScan keys src cs touched (i + 1) fold ((m, ie) :: filters)
            | none => dfCovScan keys src cs touched (i + 1) fold filters
        | none => dfCovScan keys src cs touched (i + 1) fold filters
    else dfCovScan keys src cs touched (i + 1) (q :: fold) filters
  else (fold, filters)
termination_by touched.size - i
decreasing_by all_goals omega

/-- Bucket the filters by the level at which they become fully assigned. -/
def dfLevels (k : Nat) : List (Nat × IExpr p) → Array (List (IExpr p)) → Array (List (IExpr p))
  | [], a => a
  | mie :: rest, a => dfLevels k rest (a.modify (min mie.1 (k - 1)) (mie.2 :: ·))

/-- Each key's survivor column, classified once per target; a survivor is the reversed assignment,
    so key `j` sits at offset `k - 1 - j`. -/
def dfColRes (survs : Array (List (ZMod p))) (k : Nat) : Array (DfRes p) :=
  (Array.range k).map fun j =>
    let col := survs.map (fun s => denseLookupIxV (zmodZeroP p) s (k - 1 - j))
    match dfUni col with
    | some c => .uni c false
    | none => .vec col none

def dfCollectCs (ctx : DfCtx p) (cs : Array (DenseExpr p)) :
    List Nat → List (Nat × DenseExpr p) → List (Nat × DenseExpr p)
  | [], acc => acc
  | q :: rest, acc =>
    match dfRewrite ctx (cs.getD q (.const (zmodZeroP p))) with
    | some e => dfCollectCs ctx cs rest ((q, e) :: acc)
    | none => dfCollectCs ctx cs rest acc

def dfCollectBis (ctx : DfCtx p) (bis : Array (BusInteraction (DenseExpr p))) :
    Nat → Array Nat → List (Nat × BusInteraction (DenseExpr p)) →
    List (Nat × BusInteraction (DenseExpr p))
  | i, touched, acc =>
    if h : i < touched.size then
      let q := touched[i]
      if hq : q < bis.size then
        match dfRewriteBi ctx bis[q] with
        | some bi => dfCollectBis ctx bis (i + 1) touched ((q, bi) :: acc)
        | none => dfCollectBis ctx bis (i + 1) touched acc
      else dfCollectBis ctx bis (i + 1) touched acc
    else acc
termination_by i touched => touched.size - i
decreasing_by all_goals omega

/-- One target: domains, box gate, survivors, and the items it rewrites. Reads the system arrays
    only — the caller applies the changes, so a rejected target costs no copy. A target that
    touches nothing rewritable (no fold position, no touched interaction) skips the enumeration:
    both collect results would be empty regardless of the survivors. -/
def dfPlan (ix : DfIdx p) (keys : Array VarId) (cs : Array (DenseExpr p))
    (bis : Array (BusInteraction (DenseExpr p))) :
    List (Nat × DenseExpr p) × List (Nat × BusInteraction (DenseExpr p)) :=
  match dfKeyDoms ix.doms keys cs with
  | none => ([], [])
  | some doms =>
    if doms.foldl (fun n d => n * d.length) 1 > 256 then ([], [])
    else
      let fs := dfCovScan keys ix.src cs (dfTouched ix.csB keys) 0 [] []
      let touchedBis := dfTouched ix.bisB keys
      if fs.1.isEmpty && touchedBis.isEmpty then ([], [])
      else
        let survs := dfEnumGo (zmodZeroP p)
          (dfLevels keys.size fs.2 (Array.replicate keys.size [])) doms keys.size 0 #[[]]
        if survs.isEmpty then ([], [])
        else
          let ctx : DfCtx p := ⟨keys, dfColRes survs keys.size⟩
          (dfCollectCs ctx cs fs.1 [], dfCollectBis ctx bis 0 touchedBis [])

def dfApplyCs (cs : Array (DenseExpr p)) (ch : List (Nat × DenseExpr p)) : Array (DenseExpr p) :=
  match ch with
  | [] => cs
  | (q, e) :: rest => dfApplyCs (cs.setIfInBounds q e) rest

def dfApplyBis (bis : Array (BusInteraction (DenseExpr p)))
    (ch : List (Nat × BusInteraction (DenseExpr p))) : Array (BusInteraction (DenseExpr p)) :=
  match ch with
  | [] => bis
  | (q, bi) :: rest => dfApplyBis (bis.setIfInBounds q bi) rest

/-- Process the targets in order, applying each accepted fold in place. -/
def dfLoop (ix : DfIdx p) (targets : List (Array VarId)) (cs : Array (DenseExpr p))
    (bis : Array (BusInteraction (DenseExpr p))) (ch : Bool) :
    Array (DenseExpr p) × Array (BusInteraction (DenseExpr p)) × Bool :=
  match targets with
  | [] => (cs, bis, ch)
  | keys :: rest =>
    let pl := dfPlan ix keys cs bis
    if pl.1.isEmpty && pl.2.isEmpty then dfLoop ix rest cs bis ch
    else dfLoop ix rest (dfApplyCs cs pl.1) (dfApplyBis bis pl.2) true

/-- The pass body once the targets are known: build the per-invocation index and fold every target,
    keeping the input unless something changed. -/
def dfRunWith (d : DenseConstraintSystem p) (n : Nat) (svRev : List (Nat × VarId))
    (dvs : Array (Option (List VarId))) (targets : List (Array VarId)) : DenseConstraintSystem p :=
  let cs := d.algebraicConstraints.toArray
  let isTgt := dfMarkKeys targets (Array.replicate n false)
  let tbl := dfDoms cs isTgt svRev (Array.replicate n none) (Array.replicate n 0)
  let ix : DfIdx p :=
    ⟨dfCsBuckets isTgt dvs 0 d.algebraicConstraints (Array.replicate n #[]),
     dfBisBuckets isTgt 0 d.busInteractions (Array.replicate n #[]), tbl.1, tbl.2⟩
  let r := dfLoop ix targets cs d.busInteractions.toArray false
  if r.2.2 then { algebraicConstraints := r.1.toList, busInteractions := r.2.1.toList } else d

/-- Domain-constant subexpression folding; see `denseDomainFoldFV` for what the pass does and
    `domainFoldRedesign.md` for the engine. -/
def dfRun (pw : PrimeWitness p) (d : DenseConstraintSystem p) : DenseConstraintSystem p :=
  if pw.isPrime = true then
    let sc := dfScanGo d.algebraicConstraints 0 0 [] [] #[]
    let n := sc.1 + 1
    let targets := dfDedupKeys (dfMarkVars (sc.2.1.map Prod.snd) (Array.replicate n false))
      sc.2.2.1 (Array.replicate n []) []
    if targets.isEmpty then d else dfRunWith d n sc.2.1.reverse sc.2.2.2 targets
  else d

end ApcOptimizer.Dense
