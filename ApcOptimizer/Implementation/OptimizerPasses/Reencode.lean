import ApcOptimizer.Implementation.OptimizerPasses.DomainBatch
import ApcOptimizer.Implementation.OptimizerPasses.DomainFold
import ApcOptimizer.Implementation.OptimizerPasses.AddrDiseq

set_option autoImplicit false

/-! # Witness re-encoding — dense expression ops and the build/step/loop/pass layer.

Impl-only: no theorem is stated here. Correctness and the `ofExtending` wiring live in
`Proofs/Reencode.lean`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

/-- Override `denv` on the keys of `pairs` (first match wins). -/
def denseEnvExt : List (VarId × ZMod p) → (VarId → ZMod p) → VarId → ZMod p
  | [], denv, y => denv y
  | (x, v) :: rest, denv, y => if y = x then v else denseEnvExt rest denv y

/-- `DenseExpr.eval` with the ring operations passed in. -/
def DenseExpr.evalWith (add mul : ZMod p → ZMod p → ZMod p) (denv : VarId → ZMod p) :
    DenseExpr p → ZMod p
  | .const n => n
  | .var i => denv i
  | .add a b => add (a.evalWith add mul denv) (b.evalWith add mul denv)
  | .mul a b => mul (a.evalWith add mul denv) (b.evalWith add mul denv)

/-- `DenseExpr.eval`, deriving the field operations once per call instead of per node. -/
def DenseExpr.evalFast (e : DenseExpr p) (denv : VarId → ZMod p) : ZMod p :=
  let addI : Add (ZMod p) := inferInstance
  let mulI : Mul (ZMod p) := inferInstance
  e.evalWith addI.add mulI.mul denv

/-- `b · (b − 1)`. -/
def denseBoolConstraint (b : VarId) : DenseExpr p :=
  .mul (.var b) (.add (.var b) (.const (-1)))

/-- Substitution defined only on the group `xs`, backed by `hm`. -/
def denseGroupSubst (xs : List VarId) (hm : Std.HashMap VarId (DenseExpr p)) :
    VarId → Option (DenseExpr p) :=
  fun y => if denseContainsFast xs y then hm[y]? else none

/-- The `{0,1}` domain box of the fresh bits. -/
def denseBitBox (bits : List VarId) : List (VarId × List (ZMod p)) :=
  bits.map (fun b => (b, ([0, 1] : List (ZMod p))))

/-! ## Degree-aware group rewriting -/

/-- `Π_j (bit_j or its complement)`: `1` exactly at the given pattern. -/
def denseIndicatorExpr (aβ : List (VarId × ZMod p)) : DenseExpr p :=
  aβ.foldl (fun acc bv =>
    .mul acc (if bv.2 = 1 then .var bv.1
              else .add (.const 1) (.mul (.const (-1)) (.var bv.1)))) (.const 1)

/-- Interpolate a subexpression over the bit patterns from its precomputed per-pattern values. -/
def denseInterpOfV (patts : List (List (VarId × ZMod p))) (vals : List (ZMod p)) : DenseExpr p :=
  match vals with
  | [] => .const 0
  | v₀ :: _ =>
    if vals.all (fun v => decide (v = v₀)) then .const v₀
    else (patts.zip vals).foldl (fun acc av =>
      .add acc (.mul (denseIndicatorExpr av.1) (.const av.2))) (.const 0)

/-- Take `cand` if its variables lie in the bits and it agrees with the substitution values on
    every pattern; otherwise fall back to the plain substitution `sub`. -/
def denseCandSelect (bits : List VarId) (patts : List (List (VarId × ZMod p)))
    (sub cand : DenseExpr p) (vals : List (ZMod p)) : DenseExpr p :=
  if cand.varsInF bits &&
      (patts.zip vals).all (fun av => decide (cand.evalFast (denseEnvOfFast av.1) = av.2))
  then cand
  else sub

/-- Interpolation candidate with the checked fallback to plain substitution. -/
def denseGroupRewriteCand (bits : List VarId) (σfn : VarId → Option (DenseExpr p))
    (patts : List (List (VarId × ZMod p))) (e : DenseExpr p) : DenseExpr p :=
  let sub := e.substF σfn
  let vals := patts.map (fun aβ => sub.evalFast (denseEnvOfFast aβ))
  denseCandSelect bits patts sub ((denseInterpOfV patts vals).fold) vals

/-- Replace maximal wholly-in-group subexpressions by their interpolations; substitute
    variable-wise everywhere else. -/
def denseGroupRewrite (xs bits : List VarId) (σfn : VarId → Option (DenseExpr p))
    (patts : List (List (VarId × ZMod p))) : DenseExpr p → DenseExpr p
  | .const n => .const n
  | .var y =>
      if denseContainsFast xs y then denseGroupRewriteCand bits σfn patts (.var y) else .var y
  | .add a b =>
      if (DenseExpr.add a b).varsInF xs then denseGroupRewriteCand bits σfn patts (.add a b)
      else .add (denseGroupRewrite xs bits σfn patts a) (denseGroupRewrite xs bits σfn patts b)
  | .mul a b =>
      if (DenseExpr.mul a b).varsInF xs then denseGroupRewriteCand bits σfn patts (.mul a b)
      else .mul (denseGroupRewrite xs bits σfn patts a) (denseGroupRewrite xs bits σfn patts b)

/-! ## The re-encoded system -/

/-- The re-encoded system: substitute the group everywhere, drop the now-covered constraints, and
    add booleanity constraints for the bits. -/
def denseReencodeOut (d : DenseConstraintSystem p) (xs bits : List VarId)
    (hm : Std.HashMap VarId (DenseExpr p)) : DenseConstraintSystem p :=
  { algebraicConstraints :=
      ((d.algebraicConstraints.filter (fun c => !denseCoveredBy xs c)).map
        (denseGroupRewrite xs bits (denseGroupSubst xs hm) (denseAssignments (denseBitBox bits))))
        ++ bits.map denseBoolConstraint,
    busInteractions := d.busInteractions.map (fun bi => { bi with
      multiplicity :=
        denseGroupRewrite xs bits (denseGroupSubst xs hm) (denseAssignments (denseBitBox bits))
          bi.multiplicity,
      payload := bi.payload.map
        (denseGroupRewrite xs bits (denseGroupSubst xs hm) (denseAssignments (denseBitBox bits))) }) }

/-! ## The group's surviving values -/

/-- All covered constraints zero at a point (ring ops hoisted out of the per-point eval). -/
def denseSurvZeroCW (add mul : ZMod p → ZMod p → ZMod p) (ces : List (IExpr p))
    (a : List (VarId × ZMod p)) : Bool :=
  ces.all (fun ie => decide (denseIExprEvalWith add mul a ie = 0))

/-- The surviving group values: enumerate the group's domains, keep those satisfying the covered
    constraints. -/
def denseGroupSurvivorsE (es : List (DenseExpr p)) (doms : List (VarId × List (ZMod p))) :
    List (List (VarId × ZMod p)) :=
  match denseCompileEs (doms.map Prod.fst) es with
  | some ces =>
    (denseAssignments doms).filter
      (denseSurvZeroCW (inferInstance : Add (ZMod p)).add (inferInstance : Mul (ZMod p)).mul ces)
  | none =>
    (denseAssignments doms).filter
      (fun a => es.all (fun c => decide (c.evalFast (denseEnvOfFast a) = 0)))

/-- `filter P l` if it keeps at most `cap` elements, `none` as soon as a `cap + 1`-st hit shows
    up — the tail is not scanned. -/
def denseFilterCap {α : Type} (P : α → Bool) : Nat → List α → Option (List α)
  | _, [] => some []
  | cap, x :: rest =>
    if P x then
      match cap with
      | 0 => none
      | cap + 1 =>
        match denseFilterCap P cap rest with
        | some l => some (x :: l)
        | none => none
    else denseFilterCap P cap rest

/-- `denseGroupSurvivorsE`, stopping as soon as more than `cap` survivors exist. The build uses
    `cap = 2 ^ (xs.length − 1)`: any larger survivor count makes `Nat.clog 2` reach the group
    size and the `k < xs.length` gate reject, so the outcome is the full enumeration's. -/
def denseGroupSurvivorsECap (es : List (DenseExpr p)) (doms : List (VarId × List (ZMod p)))
    (cap : Nat) : Option (List (List (VarId × ZMod p))) :=
  match denseCompileEs (doms.map Prod.fst) es with
  | some ces =>
    denseFilterCap
      (denseSurvZeroCW (inferInstance : Add (ZMod p)).add (inferInstance : Mul (ZMod p)).mul ces)
      cap (denseAssignments doms)
  | none =>
    denseFilterCap (fun a => es.all (fun c => decide (c.evalFast (denseEnvOfFast a) = 0)))
      cap (denseAssignments doms)

/-! ## The checked re-encoding certificate -/

/-- All checked side conditions for one re-encoding step. The freshness conjunct is deliberately
    last: it is the only `O(bits × system)` one, so short-circuiting runs it only for groups that
    already passed the cheap checks. -/
def denseCheckReencode (d : DenseConstraintSystem p) (xs bits : List VarId)
    (hm : Std.HashMap VarId (DenseExpr p)) : Bool :=
  match denseGroupDoms (denseCoveredCsOf d xs) xs with
  | none => false
  | some doms =>
    let es := denseCoveredCsOf d xs
    let survs := denseGroupSurvivorsE es doms
    let patts := denseAssignments (denseBitBox bits)
    decide ((doms.map (fun yd => yd.2.length)).prod ≤ 256) &&
    decide (2 ≤ survs.length) &&
    decide (bits.length < xs.length) &&
    decide (bits.Nodup) &&
    -- the substituted group variables only mention bits
    xs.all (fun x =>
      ((DenseExpr.var x).substF (denseGroupSubst xs hm)).vars.all (fun v => bits.contains v)) &&
    -- completeness: every surviving group value is hit by some bit pattern
    survs.all (fun s => patts.any (fun aβ =>
      xs.all (fun x =>
        decide (((DenseExpr.var x).substF (denseGroupSubst xs hm)).evalFast (denseEnvOfFast aβ)
          = denseEnvOfFast s x)))) &&
    -- soundness: every bit pattern's image satisfies the covered constraints
    patts.all (fun aβ => es.all (fun c =>
      decide ((c.substF (denseGroupSubst xs hm)).evalFast (denseEnvOfFast aβ) = 0))) &&
    -- freshness: no bit occurs anywhere in the system
    bits.all (fun b =>
      d.algebraicConstraints.all (fun c => !c.mentions b) &&
      d.busInteractions.all (fun bi =>
        !bi.multiplicity.mentions b && bi.payload.all (fun e => !e.mentions b)))

/-! ### Compiled twin of the certificate

`denseCheckReencode` walks the whole system once per bit for the freshness conjunct and scans the
covered set twice; the twin computes the covered set once and decides freshness in a single walk
against the bit set. -/

theorem DenseExpr.mentionsAny_ofList_false_iff (bits : List VarId) (e : DenseExpr p) :
    e.mentionsAny (Std.HashSet.ofList bits) = false ↔ ∀ b ∈ bits, e.mentions b = false := by
  induction e with
  | const c => simp [DenseExpr.mentionsAny, DenseExpr.mentions]
  | var y =>
      simp only [DenseExpr.mentionsAny, DenseExpr.mentions, Std.HashSet.contains_ofList]
      constructor
      · intro h b hb
        cases hyb : y == b with
        | false => rfl
        | true =>
            rw [show y = b from eq_of_beq hyb] at h
            rw [List.contains_eq_mem, decide_eq_false_iff_not] at h
            exact absurd hb h
      · intro h
        rw [List.contains_eq_mem, decide_eq_false_iff_not]
        intro hy
        exact absurd (h y hy) (by simp)
  | add a b iha ihb =>
      simp only [DenseExpr.mentionsAny, DenseExpr.mentions, Bool.or_eq_false_iff, iha, ihb]
      constructor
      · rintro ⟨ha, hb⟩ x hx
        exact ⟨ha x hx, hb x hx⟩
      · exact fun h => ⟨fun x hx => (h x hx).1, fun x hx => (h x hx).2⟩
  | mul a b iha ihb =>
      simp only [DenseExpr.mentionsAny, DenseExpr.mentions, Bool.or_eq_false_iff, iha, ihb]
      constructor
      · rintro ⟨ha, hb⟩ x hx
        exact ⟨ha x hx, hb x hx⟩
      · exact fun h => ⟨fun x hx => (h x hx).1, fun x hx => (h x hx).2⟩

theorem denseFreshFused_eq (d : DenseConstraintSystem p) (bits : List VarId) :
    (d.algebraicConstraints.all (fun c => !c.mentionsAny (Std.HashSet.ofList bits)) &&
      d.busInteractions.all (fun bi =>
        !bi.multiplicity.mentionsAny (Std.HashSet.ofList bits) &&
        bi.payload.all (fun e => !e.mentionsAny (Std.HashSet.ofList bits))))
      = bits.all (fun b =>
          d.algebraicConstraints.all (fun c => !c.mentions b) &&
          d.busInteractions.all (fun bi =>
            !bi.multiplicity.mentions b && bi.payload.all (fun e => !e.mentions b))) := by
  have hiff : ∀ {a b : Bool}, ((a = true) ↔ (b = true)) → a = b := by
    intro a b h; cases a <;> cases b <;> simp_all
  apply hiff
  simp only [List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true',
    DenseExpr.mentionsAny_ofList_false_iff]
  constructor
  · rintro ⟨hcs, hbis⟩ b hb
    exact ⟨fun c hc => hcs c hc b hb, fun bi hbi =>
      ⟨(hbis bi hbi).1 b hb, fun e he => (hbis bi hbi).2 e he b hb⟩⟩
  · intro h
    exact ⟨fun c hc b hb => (h b hb).1 c hc, fun bi hbi =>
      ⟨fun b hb => ((h b hb).2 bi hbi).1, fun e he b hb => ((h b hb).2 bi hbi).2 e he⟩⟩

/-- `denseCheckReencode` with the covered set shared between the domain and soundness conjuncts
    and the freshness conjunct decided in one system walk. -/
def denseCheckReencodeFast (d : DenseConstraintSystem p) (xs bits : List VarId)
    (hm : Std.HashMap VarId (DenseExpr p)) : Bool :=
  let es := denseCoveredCsOf d xs
  match denseGroupDoms es xs with
  | none => false
  | some doms =>
    let survs := denseGroupSurvivorsE es doms
    let patts := denseAssignments (denseBitBox bits)
    decide ((doms.map (fun yd => yd.2.length)).prod ≤ 256) &&
    decide (2 ≤ survs.length) &&
    decide (bits.length < xs.length) &&
    decide (bits.Nodup) &&
    xs.all (fun x =>
      ((DenseExpr.var x).substF (denseGroupSubst xs hm)).vars.all (fun v => bits.contains v)) &&
    survs.all (fun s => patts.any (fun aβ =>
      xs.all (fun x =>
        decide (((DenseExpr.var x).substF (denseGroupSubst xs hm)).evalFast (denseEnvOfFast aβ)
          = denseEnvOfFast s x)))) &&
    patts.all (fun aβ => es.all (fun c =>
      decide ((c.substF (denseGroupSubst xs hm)).evalFast (denseEnvOfFast aβ) = 0))) &&
    (d.algebraicConstraints.all (fun c => !c.mentionsAny (Std.HashSet.ofList bits)) &&
      d.busInteractions.all (fun bi =>
        !bi.multiplicity.mentionsAny (Std.HashSet.ofList bits) &&
        bi.payload.all (fun e => !e.mentionsAny (Std.HashSet.ofList bits))))

@[csimp] theorem denseCheckReencode_eq_fast : @denseCheckReencode = @denseCheckReencodeFast := by
  funext q d xs bits hm
  unfold denseCheckReencode denseCheckReencodeFast
  simp only [denseFreshFused_eq]

/-! ## Derived-variable methods for the fresh bits

Each bit is recovered from the group by a decision tree over the bit patterns: at the first
pattern whose interpolation image equals the group's values, output that pattern's bit. -/

/-- The interpolation image of group variable `x` at pattern `aβ` (a field constant). -/
def denseImgVal (xs : List VarId) (hm : Std.HashMap VarId (DenseExpr p))
    (aβ : List (VarId × ZMod p)) (x : VarId) : ZMod p :=
  ((DenseExpr.var x).substF (denseGroupSubst xs hm)).evalFast (denseEnvOfFast aβ)

/-- `thenM` if every `x ∈ xs` has `imgFn x = env x`, else `elseM`, as nested `ifEqZero`. -/
def denseMatchCM (xs : List VarId) (imgFn : VarId → ZMod p)
    (thenM elseM : DenseComputationMethod p) : DenseComputationMethod p :=
  match xs with
  | [] => thenM
  | x :: rest =>
      .ifEqZero (.add (.var x) (.const (-(imgFn x)))) (denseMatchCM rest imgFn thenM elseM) elseM

/-- The derivation of bit `b`: scan the patterns, output the first matching pattern's `b`-bit. -/
def denseBitCM (patts : List (List (VarId × ZMod p))) (xs : List VarId)
    (hm : Std.HashMap VarId (DenseExpr p)) (b : VarId) : DenseComputationMethod p :=
  match patts with
  | [] => .const 0
  | aβ :: rest =>
      denseMatchCM xs (denseImgVal xs hm aβ) (.const (denseEnvOfFast aβ b)) (denseBitCM rest xs hm b)

/-- Interpolation polynomial for group variable `x` over pattern/survivor pairs. -/
def denseInterpPoly (pz : List (List (VarId × ZMod p) × List (VarId × ZMod p))) (x : VarId) :
    DenseExpr p :=
  pz.foldl (fun acc az => .add acc (.mul (denseIndicatorExpr az.1) (.const (denseEnvOfFast az.2 x))))
    (.const 0)

/-- Does the expression share a variable with `xs`? -/
def DenseExpr.sharesVarIn (xs : List VarId) : DenseExpr p → Bool
  | .const _ => false
  | .var y => denseContainsFast xs y
  | .add a b => a.sharesVarIn xs || b.sharesVarIn xs
  | .mul a b => a.sharesVarIn xs || b.sharesVarIn xs

/-! ### Compiled twin of the system rewrite

`denseGroupRewrite` is the identity on an item that shares no variable with the group and has no
variable-free composite node (`denseGroupRewrite_eq_self`), so the compiled `denseReencodeOut`
guards every item with a read-only gate and rebuilds only the few that can change — the plain
definition rebuilds every expression of the system per accepted group. Installed with `@[csimp]`
below, so callers compile to the gated form while the proofs keep the plain `denseReencodeOut`. -/

theorem DenseExpr.varsInF_eq_false {xs : List VarId} {e : DenseExpr p}
    (hv : e.hasVar = true) (hs : e.sharesVarIn xs = false) : e.varsInF xs = false := by
  induction e with
  | const n => simp [DenseExpr.hasVar] at hv
  | var y =>
      simp only [DenseExpr.sharesVarIn] at hs
      simp [DenseExpr.varsInF, hs]
  | add a b iha ihb =>
      simp only [DenseExpr.hasVar, Bool.or_eq_true] at hv
      simp only [DenseExpr.sharesVarIn, Bool.or_eq_false_iff] at hs
      rcases hv with hv | hv
      · simp [DenseExpr.varsInF, iha hv hs.1]
      · simp [DenseExpr.varsInF, ihb hv hs.2]
  | mul a b iha ihb =>
      simp only [DenseExpr.hasVar, Bool.or_eq_true] at hv
      simp only [DenseExpr.sharesVarIn, Bool.or_eq_false_iff] at hs
      rcases hv with hv | hv
      · simp [DenseExpr.varsInF, iha hv hs.1]
      · simp [DenseExpr.varsInF, ihb hv hs.2]

theorem denseGroupRewrite_eq_self {xs bits : List VarId} {σfn : VarId → Option (DenseExpr p)}
    {patts : List (List (VarId × ZMod p))} {e : DenseExpr p}
    (hs : e.sharesVarIn xs = false) (hf : e.hasConstFoldableNode = false) :
    denseGroupRewrite xs bits σfn patts e = e := by
  induction e with
  | const n => rfl
  | var y =>
      simp only [DenseExpr.sharesVarIn] at hs
      simp [denseGroupRewrite, hs]
  | add a b iha ihb =>
      simp only [DenseExpr.hasConstFoldableNode, Bool.or_eq_false_iff, Bool.not_eq_false'] at hf
      obtain ⟨⟨hv, hfa⟩, hfb⟩ := hf
      simp only [DenseExpr.sharesVarIn, Bool.or_eq_false_iff] at hs
      rw [denseGroupRewrite, if_neg (by
        rw [DenseExpr.varsInF_eq_false hv
          (by simp [DenseExpr.sharesVarIn, hs.1, hs.2])]; simp)]
      rw [iha hs.1 hfa, ihb hs.2 hfb]
  | mul a b iha ihb =>
      simp only [DenseExpr.hasConstFoldableNode, Bool.or_eq_false_iff, Bool.not_eq_false'] at hf
      obtain ⟨⟨hv, hfa⟩, hfb⟩ := hf
      simp only [DenseExpr.sharesVarIn, Bool.or_eq_false_iff] at hs
      rw [denseGroupRewrite, if_neg (by
        rw [DenseExpr.varsInF_eq_false hv
          (by simp [DenseExpr.sharesVarIn, hs.1, hs.2])]; simp)]
      rw [iha hs.1 hfa, ihb hs.2 hfb]

/-- `denseGroupRewrite` behind the read-only gate. -/
def denseGroupRewriteGate (xs bits : List VarId) (σfn : VarId → Option (DenseExpr p))
    (patts : List (List (VarId × ZMod p))) (e : DenseExpr p) : DenseExpr p :=
  if e.sharesVarIn xs || e.hasConstFoldableNode then denseGroupRewrite xs bits σfn patts e else e

theorem denseGroupRewriteGate_eq (xs bits : List VarId) (σfn : VarId → Option (DenseExpr p))
    (patts : List (List (VarId × ZMod p))) :
    denseGroupRewriteGate xs bits σfn patts = denseGroupRewrite xs bits σfn patts := by
  funext e
  unfold denseGroupRewriteGate
  split
  · rfl
  · next h =>
      rw [Bool.or_eq_true, not_or, Bool.not_eq_true, Bool.not_eq_true] at h
      exact (denseGroupRewrite_eq_self h.1 h.2).symm

/-- Per-interaction gate: an interaction none of whose expressions can change is kept as-is. -/
def denseBIRewriteGate (xs bits : List VarId) (σfn : VarId → Option (DenseExpr p))
    (patts : List (List (VarId × ZMod p))) (bi : BusInteraction (DenseExpr p)) :
    BusInteraction (DenseExpr p) :=
  if bi.multiplicity.sharesVarIn xs || bi.multiplicity.hasConstFoldableNode
      || bi.payload.any (fun e => e.sharesVarIn xs || e.hasConstFoldableNode) then
    { bi with multiplicity := denseGroupRewriteGate xs bits σfn patts bi.multiplicity,
              payload := bi.payload.map (denseGroupRewriteGate xs bits σfn patts) }
  else bi

theorem denseBIRewriteGate_eq (xs bits : List VarId) (σfn : VarId → Option (DenseExpr p))
    (patts : List (List (VarId × ZMod p))) :
    denseBIRewriteGate xs bits σfn patts
      = fun bi => { bi with
          multiplicity := denseGroupRewrite xs bits σfn patts bi.multiplicity,
          payload := bi.payload.map (denseGroupRewrite xs bits σfn patts) } := by
  funext bi
  unfold denseBIRewriteGate
  split
  · rw [denseGroupRewriteGate_eq]
  · next h =>
      rw [Bool.or_eq_true, not_or, Bool.or_eq_true, not_or,
        Bool.not_eq_true, Bool.not_eq_true, List.any_eq_true] at h
      obtain ⟨⟨hm, hf⟩, hp⟩ := h
      have hpl : bi.payload.map (denseGroupRewrite xs bits σfn patts) = bi.payload := by
        have hcg : bi.payload.map (denseGroupRewrite xs bits σfn patts) = bi.payload.map id :=
          List.map_congr_left (fun e he => by
            have he' : ¬(e.sharesVarIn xs = true ∨ e.hasConstFoldableNode = true) := fun hor =>
              hp ⟨e, he, by rw [Bool.or_eq_true]; exact hor⟩
            rw [not_or, Bool.not_eq_true, Bool.not_eq_true] at he'
            exact denseGroupRewrite_eq_self he'.1 he'.2)
        rw [hcg, List.map_id]
      rw [denseGroupRewrite_eq_self hm hf, hpl]

/-- The gated twin of `denseReencodeOut`, with the substitution and pattern list hoisted out of the
    per-interaction closures. -/
def denseReencodeOutFast (d : DenseConstraintSystem p) (xs bits : List VarId)
    (hm : Std.HashMap VarId (DenseExpr p)) : DenseConstraintSystem p :=
  let σfn := denseGroupSubst xs hm
  let patts := denseAssignments (denseBitBox bits)
  { algebraicConstraints :=
      ((d.algebraicConstraints.filter (fun c => !denseCoveredBy xs c)).map
        (denseGroupRewriteGate xs bits σfn patts)) ++ bits.map denseBoolConstraint,
    busInteractions := d.busInteractions.map (denseBIRewriteGate xs bits σfn patts) }

@[csimp]
theorem denseReencodeOut_eq_fast : @denseReencodeOut = @denseReencodeOutFast := by
  funext p d xs bits hm
  simp only [denseReencodeOut, denseReencodeOutFast, denseBIRewriteGate_eq,
    denseGroupRewriteGate_eq]

/-! ## The build/step/loop/pass layer -/

inductive DenseReencodeRootPlan (p : ℕ)
  | any (roots : List (ZMod p))
  | one (var : VarId) (roots : List (ZMod p))

def denseReencodeRootPlanMul :
    DenseReencodeRootPlan p → DenseReencodeRootPlan p → Option (DenseReencodeRootPlan p)
  | .any left, .any right => some (.any (left ++ right))
  | .any left, .one var right => some (.one var (left ++ right))
  | .one var left, .any right => some (.one var (left ++ right))
  | .one leftVar left, .one rightVar right =>
      if leftVar = rightVar then some (.one leftVar (left ++ right)) else none

def denseBuildReencodeRootPlan : DenseExpr p → Option (DenseReencodeRootPlan p)
  | .mul a b =>
      match denseBuildReencodeRootPlan a, denseBuildReencodeRootPlan b with
      | some left, some right => denseReencodeRootPlanMul left right
      | _, _ => none
  | e =>
      match denseLinearize e with
      | none => none
      | some l =>
          let l := l.norm
          match l.terms with
          | [] => if l.const = 0 then none else some (.any [])
          | [(i, _)] => (denseRootsOfTerms i l.const l.terms).map (.one i)
          | _ => none

def denseReencodeRootPlanLookup (i : VarId) :
    DenseReencodeRootPlan p → Option (List (ZMod p))
  | .any roots => some roots
  | .one var roots => if var = i then some roots else none

abbrev DenseReencodeRootCache (p : ℕ) :=
  Std.HashMap Nat (Option (DenseReencodeRootPlan p))

def denseReencodeRootAt (cache : DenseReencodeRootCache p) (pos : Nat) (c : DenseExpr p) :
    Option (DenseReencodeRootPlan p) × DenseReencodeRootCache p :=
  match cache[pos]? with
  | some plan => (plan, cache)
  | none =>
      let plan := denseBuildReencodeRootPlan c
      (plan, cache.insert pos plan)

def denseFindDomainCached (i : VarId) :
    List (Nat × DenseExpr p) → DenseReencodeRootCache p →
      Option (List (ZMod p)) × DenseReencodeRootCache p
  | [], cache => (none, cache)
  | c :: rest, cache =>
      if c.2.mentions i then
        let (plan, cache) := denseReencodeRootAt cache c.1 c.2
        match plan.bind (denseReencodeRootPlanLookup i) with
        | some roots => (some roots, cache)
        | none => denseFindDomainCached i rest cache
      else denseFindDomainCached i rest cache

def denseGroupDomsCached (es : List (Nat × DenseExpr p)) :
    List VarId → DenseReencodeRootCache p →
      Option (List (VarId × List (ZMod p))) × DenseReencodeRootCache p
  | [], cache => (some [], cache)
  | i :: rest, cache =>
      let (head, cache) := denseFindDomainCached i es cache
      let (tail, cache) := denseGroupDomsCached es rest cache
      match head, tail with
      | some d, some ds => (some ((i, d) :: ds), cache)
      | _, _ => (none, cache)

def denseCoveredIdxPos (idx : DenseCovIndex) (arr : Array (DenseExpr p))
    (xs : List VarId) : List (Nat × DenseExpr p) :=
  let uniq := ((denseCandidates idx xs).foldl (·.insert ·) (∅ : Std.HashSet Nat)).toList
  (uniq.mergeSort (· ≤ ·)).filterMap (fun i =>
    if h : i < arr.size then
      if denseCoveredBy xs arr[i] then some (i, arr[i]) else none
    else none)

/-- Build the inverted index (`VarId`-keyed twin of `CoveredIndex.buildPruned`), skipping items
    with more than `maxVars` distinct variables. -/
def denseBuildPruned {α : Type} (varsOf : α → List VarId) (maxVars : Nat) (items : List α) :
    DenseCovIndex :=
  items.zipIdx.foldr (fun ai idx =>
    if (HashedDedup.hashedEraseDups (hash ·) (varsOf ai.1)).length ≤ maxVars then
      denseBuildStep varsOf ai idx
    else idx) ⟨∅, []⟩

/-- Register the `k` fresh bit variables `freshBase ++ "_0", …, freshBase ++ "_(k-1)"` into `reg`,
    in order. -/
def denseRegisterBits (reg : VarRegistry) (freshBase : String) (k : Nat) :
    VarRegistry × List VarId :=
  (List.range k).foldl
    (fun (acc : VarRegistry × List VarId) (j : Nat) =>
      let (r, bs) := acc
      let (r', i) := r.register ({ name := freshBase ++ "_" ++ toString j } : Variable)
      (r', bs ++ [i]))
    (reg, [])

/-- Construct the bits and the substitution map for a candidate group (proof-free — the checked
    certificate re-verifies everything). Registers fresh bits only on the single accepting path. -/
def denseBuildReencode (reg : VarRegistry) (useIdx : Bool) (csIdx : DenseCovIndex)
    (arrCs : Array (DenseExpr p)) (xs : List VarId) (freshBase : String) :
    VarRegistry × Option (List VarId × Std.HashMap VarId (DenseExpr p)) :=
  let es := if useIdx then denseCoveredIdx csIdx arrCs (denseCoveredBy xs) xs
    else arrCs.foldr (fun c acc => if denseCoveredBy xs c then c :: acc else acc) []
  match denseGroupDoms es xs with
  | none => (reg, none)
  | some doms =>
    let boxSize := (doms.map (fun yd => yd.2.length)).prod
    if boxSize ≤ 256 then
      if es.length == xs.length && es.all (fun c => c.vars.eraseDups.length == 1)
          && xs.length ≤ Nat.clog 2 boxSize then
        -- single-var-only covered set (one per variable): survivors = box; unencodable
        (reg, none)
      else
      match denseGroupSurvivorsECap es doms (2 ^ (xs.length - 1)) with
      | none => (reg, none)
      | some survs =>
      if 2 ≤ survs.length then
        let k := Nat.clog 2 survs.length
        if k < xs.length then
          let (reg1, bits) := denseRegisterBits reg freshBase k
          let patts := denseAssignments (denseBitBox bits)
          let survsP := survs ++ List.replicate (patts.length - survs.length) (survs.headD [])
          let pz := patts.zip survsP
          (reg1, some (bits, Std.HashMap.ofList (xs.map (fun x => (x, (denseInterpPoly pz x).fold)))))
        else (reg, none)
      else (reg, none)
    else (reg, none)

/-- Construct a candidate using the retained per-constraint root cache. -/
def denseBuildReencodeCached (reg : VarRegistry) (useIdx : Bool) (csIdx : DenseCovIndex)
    (arrCs : Array (DenseExpr p)) (cache : DenseReencodeRootCache p)
    (xs : List VarId) (freshBase : String) :
    VarRegistry × Option (List VarId × Std.HashMap VarId (DenseExpr p)) ×
      DenseReencodeRootCache p :=
  let planned := if useIdx then denseCoveredIdxPos csIdx arrCs xs
    else arrCs.toList.zipIdx.foldr
      (fun c acc => if denseCoveredBy xs c.1 then (c.2, c.1) :: acc else acc) []
  let es := planned.map Prod.snd
  let (doms?, cache) := denseGroupDomsCached planned xs cache
  match doms? with
  | none => (reg, none, cache)
  | some doms =>
    let boxSize := (doms.map (fun yd => yd.2.length)).prod
    if boxSize ≤ 256 then
      if es.length == xs.length && es.all (fun c => c.vars.eraseDups.length == 1)
          && xs.length ≤ Nat.clog 2 boxSize then
        (reg, none, cache)
      else
      match denseGroupSurvivorsECap es doms (2 ^ (xs.length - 1)) with
      | none => (reg, none, cache)
      | some survs =>
      if 2 ≤ survs.length then
        let k := Nat.clog 2 survs.length
        if k < xs.length then
          let (reg1, bits) := denseRegisterBits reg freshBase k
          let patts := denseAssignments (denseBitBox bits)
          let survsP := survs ++ List.replicate (patts.length - survs.length) (survs.headD [])
          let pz := patts.zip survsP
          (reg1,
            some (bits, Std.HashMap.ofList (xs.map (fun x => (x, (denseInterpPoly pz x).fold)))),
            cache)
        else (reg, none, cache)
      else (reg, none, cache)
    else (reg, none, cache)

/-- Whole-system posting index for the degree pre-gate, thunked so only runs that construct a
    candidate pay for it. Positions are `d`'s list order, so they index `arrCs` and `arrBis`. -/
structure DenseReencodeUseIdx (p : ℕ) where
  csIdx : DenseCovIndex
  biIdx : DenseCovIndex
  arrBis : Array (BusInteraction (DenseExpr p))

def denseBuildUseIdx (d : DenseConstraintSystem p) : DenseReencodeUseIdx p :=
  ⟨denseCovBuild DenseExpr.vars d.algebraicConstraints,
   denseCovBuild denseBIVars d.busInteractions,
   d.busInteractions.toArray⟩

/-- The index's candidate positions for `xs`, each once (an item is bucketed per variable
    occurrence, and the gate below rewrites every position it visits). -/
def denseUsePositions (idx : DenseCovIndex) (xs : List VarId) : List Nat :=
  ((denseCandidates idx xs).foldl (·.insert ·) (∅ : Std.HashSet Nat)).toList

/-- Degree pre-gate (untrusted): rewrite only the items sharing a variable with the group and fire
    when a rewritten item already exceeds the bound. Only the indexed candidate positions are
    visited — the buckets are complete, so every item outside them is variable-disjoint from `xs`
    and cannot fire. Stale bucket entries (the cached loop's indexes are grow-only) are harmless:
    each position's current content is re-tested. -/
def denseDegPreRejectIdx (b : DegreeBound) (csIdxUse biIdxUse : DenseCovIndex)
    (arrBis : Array (BusInteraction (DenseExpr p)))
    (arrCs : Array (DenseExpr p)) (xs bits : List VarId)
    (hm : Std.HashMap VarId (DenseExpr p)) : Bool :=
  let σ := denseGroupSubst xs hm
  let patts := denseAssignments (denseBitBox bits)
  (denseUsePositions csIdxUse xs).any (fun i =>
    match arrCs[i]? with
    | some c =>
      c.sharesVarIn xs && !denseCoveredBy xs c &&
        decide (b.identities < (denseGroupRewrite xs bits σ patts c).degree)
    | none => false) ||
  (denseUsePositions biIdxUse xs).any (fun i =>
    match arrBis[i]? with
    | some bi =>
      (bi.multiplicity.sharesVarIn xs &&
        decide (b.busInteractions < (denseGroupRewrite xs bits σ patts bi.multiplicity).degree)) ||
      bi.payload.any (fun e =>
        e.sharesVarIn xs &&
          decide (b.busInteractions < (denseGroupRewrite xs bits σ patts e).degree))
    | none => false)

def denseDegPreReject (b : DegreeBound) (use : Thunk (DenseReencodeUseIdx p))
    (arrCs : Array (DenseExpr p)) (xs bits : List VarId)
    (hm : Std.HashMap VarId (DenseExpr p)) : Bool :=
  denseDegPreRejectIdx b use.get.csIdx use.get.biIdx use.get.arrBis arrCs xs bits hm

/-- One checked re-encoding step (identity if construction or the certificate fails). Applies the
    gates in order, minting fresh bits and rewriting `d` only on full acceptance. -/
def denseReencodeStep (b : DegreeBound) (useIdx : Bool)
    (reg : VarRegistry) (d : DenseConstraintSystem p) (csIdx : DenseCovIndex)
    (arrCs : Array (DenseExpr p)) (varSet : Std.HashSet VarId)
    (use : Thunk (DenseReencodeUseIdx p)) (xs : List VarId)
    (freshBase : String) :
    VarRegistry × DenseConstraintSystem p × DenseDerivations p × DenseCovIndex ×
      Array (DenseExpr p) × Std.HashSet VarId :=
  if xs.all (fun x => reg.isInput x) then
  if (match reg.idOf? ({ name := freshBase ++ "_0" } : Variable) with
      | some i => varSet.contains i
      | none => false) then
    -- fresh-name collision: `denseCheckReencode` would reject after the full freshness scan anyway
    (reg, d, [], csIdx, arrCs, varSet)
  else
  match denseBuildReencode reg useIdx csIdx arrCs xs freshBase with
  | (reg1, none) => (reg1, d, [], csIdx, arrCs, varSet)
  | (reg1, some (bits, hm)) =>
    -- Degree pre-gate: reject early what the final `withinDegreeB` gate would reject anyway.
    if denseDegPreReject b use arrCs xs bits hm then (reg1, d, [], csIdx, arrCs, varSet)
    else
    if xs.all (fun x => varSet.contains x) then
    if xs.all (fun x => decide (x ∉ bits)) then
    if bits.all (fun b => decide ((reg1.resolve b).powdrId? = none)) then
    if denseCheckReencode d xs bits hm then
      let ro := denseReencodeOut d xs bits hm
      if ro.withinDegreeB b then
        -- `d` changed: rebuild the index and variable set for `ro`.
        (reg1, ro,
         bits.map (fun b => (b, denseBitCM (denseAssignments (denseBitBox bits)) xs hm b)),
         (if useIdx then denseBuildPruned DenseExpr.vars 8 ro.algebraicConstraints else ⟨∅, []⟩),
         ro.algebraicConstraints.toArray,
         Std.HashSet.ofList ro.occ)
      else (reg1, d, [], csIdx, arrCs, varSet)
    else (reg1, d, [], csIdx, arrCs, varSet)
    else (reg1, d, [], csIdx, arrCs, varSet)
    else (reg1, d, [], csIdx, arrCs, varSet)
    else (reg1, d, [], csIdx, arrCs, varSet)
  else (reg, d, [], csIdx, arrCs, varSet)

/-- The cached loop's candidate-state, kept on stable positions across accepts: dropped
    constraints become `.const 0` tombstones (variable-free, so every index query skips them),
    the bucket indexes are grow-only, and `denseReencodeStateUpdate` touches only the positions
    an accept can change — nothing here is rebuilt per accepted group. `varSet` only ever gains
    the fresh bits, so it over-approximates the live variables; a group whose variable was
    eliminated by an earlier accept passes that gate and is then rejected by the certificate
    (no covered constraint mentions the variable), the same outcome the exact set produces. -/
structure DenseReencodeCacheState (p : ℕ) where
  csIdx : DenseCovIndex
  arrCs : Array (DenseExpr p)
  rootCache : DenseReencodeRootCache p
  varSet : Std.HashSet VarId
  useCs : DenseCovIndex
  useBis : DenseCovIndex
  arrBis : Array (BusInteraction (DenseExpr p))
  foldCs : Std.HashSet Nat

/-- Apply an accepted rewrite to the threaded state in place, mirroring `denseReencodeOut` on the
    stable-position arrays: only positions holding a group variable (bucket candidates) or a
    variable-free composite node (`foldCs`) can change. The root cache keeps every untouched
    position (it memoizes a pure function of the position's content). -/
def denseReencodeStateUpdate (state : DenseReencodeCacheState p) (xs bits : List VarId)
    (hm : Std.HashMap VarId (DenseExpr p)) : DenseReencodeCacheState p :=
  let σfn := denseGroupSubst xs hm
  let patts := denseAssignments (denseBitBox bits)
  let bucketAdd : DenseCovIndex → List VarId → Nat → DenseCovIndex := fun idx vs i =>
    ⟨vs.foldl (fun m v => m.insert v (i :: m.getD v [])) idx.buckets, idx.varless⟩
  let posC := (denseCandidates state.useCs xs).foldl (·.insert ·) state.foldCs
  let st := posC.fold (fun st i =>
    if h : i < st.arrCs.size then
      let c := st.arrCs[i]
      if denseCoveredBy xs c then
        { st with arrCs := st.arrCs.set i (.const 0), rootCache := st.rootCache.erase i,
                  foldCs := st.foldCs.erase i }
      else if c.sharesVarIn xs || c.hasConstFoldableNode then
        let c' := denseGroupRewrite xs bits σfn patts c
        let vs := HashedDedup.hashedDedup (hash ·) c'.vars
        { st with
          arrCs := st.arrCs.set i c'
          rootCache := st.rootCache.erase i
          csIdx := if vs.length ≤ 8 then bucketAdd st.csIdx vs i else st.csIdx
          useCs := bucketAdd st.useCs vs i
          foldCs := if c'.hasConstFoldableNode then st.foldCs.insert i else st.foldCs.erase i }
      else st
    else st) state
  let st := bits.foldl (fun st b =>
    let i := st.arrCs.size
    { st with arrCs := st.arrCs.push (denseBoolConstraint b),
              csIdx := bucketAdd st.csIdx [b] i,
              useCs := bucketAdd st.useCs [b] i }) st
  let posB := (denseCandidates state.useBis xs).foldl (·.insert ·) (∅ : Std.HashSet Nat)
  let st := posB.fold (fun st i =>
    if h : i < st.arrBis.size then
      let bi := st.arrBis[i]
      if bi.multiplicity.sharesVarIn xs || bi.multiplicity.hasConstFoldableNode
          || bi.payload.any (fun e => e.sharesVarIn xs || e.hasConstFoldableNode) then
        let bi' : BusInteraction (DenseExpr p) :=
          { bi with multiplicity := denseGroupRewriteGate xs bits σfn patts bi.multiplicity,
                    payload := bi.payload.map (denseGroupRewriteGate xs bits σfn patts) }
        { st with arrBis := st.arrBis.set i bi',
                  useBis := bucketAdd st.useBis
                    (HashedDedup.hashedDedup (hash ·) (denseBIVars bi')) i }
      else st
    else st) st
  { st with varSet := bits.foldl (·.insert ·) st.varSet }

def denseReencodeStepCached (b : DegreeBound) (useIdx : Bool)
    (reg : VarRegistry) (d : DenseConstraintSystem p) (state : DenseReencodeCacheState p)
    (xs : List VarId) (freshBase : String) :
    VarRegistry × DenseConstraintSystem p × DenseDerivations p × DenseReencodeCacheState p :=
  if xs.all (fun x => reg.isInput x) then
  if (match reg.idOf? ({ name := freshBase ++ "_0" } : Variable) with
      | some i => state.varSet.contains i
      | none => false) then
    (reg, d, [], state)
  else
  match denseBuildReencodeCached reg useIdx state.csIdx state.arrCs state.rootCache xs freshBase with
  | (reg1, none, rootCache) => (reg1, d, [], { state with rootCache })
  | (reg1, some (bits, hm), rootCache) =>
    let state := { state with rootCache }
    if denseDegPreRejectIdx b state.useCs state.useBis state.arrBis state.arrCs xs bits hm then
      (reg1, d, [], state)
    else
    if xs.all (fun x => state.varSet.contains x) then
    if xs.all (fun x => decide (x ∉ bits)) then
    if bits.all (fun b => decide ((reg1.resolve b).powdrId? = none)) then
    if denseCheckReencode d xs bits hm then
      let ro := denseReencodeOut d xs bits hm
      if ro.withinDegreeB b then
        (reg1, ro,
         bits.map (fun b => (b, denseBitCM (denseAssignments (denseBitBox bits)) xs hm b)),
         denseReencodeStateUpdate state xs bits hm)
      else (reg1, d, [], state)
    else (reg1, d, [], state)
    else (reg1, d, [], state)
    else (reg1, d, [], state)
    else (reg1, d, [], state)
  else (reg, d, [], state)

/-- `d`'s item counts for the fresh-name prefix, re-read only after a step that rewrote `d`
    (a step derives one method per minted bit, so nonempty derivations mark exactly the accepts). -/
def denseReencodeNameCounts (derivs : DenseDerivations p) (d : DenseConstraintSystem p)
    (nc nb : Nat) : Nat × Nat :=
  if derivs.isEmpty then (nc, nb)
  else (d.algebraicConstraints.length, d.busInteractions.length)

/-- The pre-gate index for the next step: kept while the steps leave `d` alone (see
    `denseReencodeNameCounts` for the accept marker), rebuilt for a rewritten system. -/
def denseReencodeUseNext (derivs : DenseDerivations p) (d : DenseConstraintSystem p)
    (use : Thunk (DenseReencodeUseIdx p)) : Thunk (DenseReencodeUseIdx p) :=
  if derivs.isEmpty then use else Thunk.mk (fun _ => denseBuildUseIdx d)

/-- Process the candidate groups sequentially, threading the registry, indexes, variable set, and
    `d`'s item counts (`nc`/`nb`, the fresh-name prefix). -/
def denseReencodeLoop (b : DegreeBound) (useIdx : Bool) :
    List (List VarId) → Nat → VarRegistry → DenseConstraintSystem p → DenseCovIndex →
      Array (DenseExpr p) → Std.HashSet VarId → Thunk (DenseReencodeUseIdx p) → Nat → Nat →
      VarRegistry × DenseConstraintSystem p × DenseDerivations p
  | [], _, reg, d, _, _, _, _, _, _ => (reg, d, [])
  | xs :: rest, idx, reg, d, csIdx, arrCs, varSet, use, nc, nb =>
    let (reg1, d1, derivs1, csIdx1, arrCs1, varSet1) :=
      denseReencodeStep b useIdx reg d csIdx arrCs varSet use xs s!"rnc{nc}_{nb}_{idx}"
    let (nc1, nb1) := denseReencodeNameCounts derivs1 d1 nc nb
    let (reg2, d2, derivs2) :=
      denseReencodeLoop b useIdx rest (idx + 1) reg1 d1 csIdx1 arrCs1 varSet1
        (denseReencodeUseNext derivs1 d1 use) nc1 nb1
    (reg2, d2, derivs1 ++ derivs2)

def denseReencodeLoopCached (b : DegreeBound) (useIdx : Bool) :
    List (List VarId) → Nat → VarRegistry → DenseConstraintSystem p →
      DenseReencodeCacheState p → Nat → Nat →
      VarRegistry × DenseConstraintSystem p × DenseDerivations p
  | [], _, reg, d, _, _, _ => (reg, d, [])
  | xs :: rest, idx, reg, d, state, nc, nb =>
    let (reg1, d1, derivs1, state1) :=
      denseReencodeStepCached b useIdx reg d state xs s!"rnc{nc}_{nb}_{idx}"
    let (nc1, nb1) := denseReencodeNameCounts derivs1 d1 nc nb
    let (reg2, d2, derivs2) :=
      denseReencodeLoopCached b useIdx rest (idx + 1) reg1 d1 state1 nc1 nb1
    (reg2, d2, derivs1 ++ derivs2)

/-- Witness re-encoding. When a group of variables `xs` is so constrained that only a few value
    combinations survive, mint `Nat.clog 2 #survivors` fresh boolean bits, rewrite each group
    variable as an interpolation polynomial over the bits, drop the now-covered constraints, and add
    booleanity constraints — e.g. a group with 3 surviving combinations becomes 2 bits, cutting the
    variable count. The transform is shaped for `DenseVerifiedPassW.ofExtending`; `facts` is unused
    (reencode is fact-free). -/
def denseReencodeF (pw : PrimeWitness p) (b : DegreeBound) (reg : VarRegistry)
    (bsem : BusSemantics p) (_facts : BusFacts p bsem) (d : DenseConstraintSystem p) :
    VarRegistry × DenseConstraintSystem p × DenseDerivations p :=
  if pw.isPrime = true then
    -- Each constraint's deduped variable list, shared between `svSet` and `targets`.
    let csVs := d.algebraicConstraints.map (fun c => HashedDedup.hashedDedup (hash ·) c.vars)
    let svSet : Std.HashSet VarId := csVs.foldl (init := ∅) fun s vs =>
      match vs with
      | [x] => s.insert x
      | _ => s
    let targets := dedupHash (csVs.filterMap (fun vs =>
      if 2 ≤ vs.length && vs.length ≤ 8 && vs.all (svSet.contains ·) then
        -- Sort by the resolved `Variable`'s order: `denseReencodeLoop` below is a greedy,
        -- order-sensitive accept/reject sequence, so the group order determines the outcome.
        some (vs.mergeSort (fun a b => compare (reg.resolve a) (reg.resolve b) != .gt))
      else none))
    let targetSlots := (targets.map List.length).sum
    let targetVars := targets.foldl
      (fun vars xs => xs.foldl (fun vars x => vars.insert x) vars)
      (∅ : Std.HashSet VarId)
    let useRootCache := 64 ≤ targetSlots - targetVars.size
    let useIdx := 8192 ≤ d.algebraicConstraints.length
    if useIdx ∧ useRootCache then
      denseReencodeLoopCached b useIdx targets 0 reg d
        { csIdx := denseBuildPruned DenseExpr.vars 8 d.algebraicConstraints
          arrCs := d.algebraicConstraints.toArray
          rootCache := ∅
          varSet := Std.HashSet.ofList d.occ
          useCs := denseCovBuild DenseExpr.vars d.algebraicConstraints
          useBis := denseCovBuild denseBIVars d.busInteractions
          arrBis := d.busInteractions.toArray
          foldCs := d.algebraicConstraints.zipIdx.foldl
            (fun s ci => if ci.1.hasConstFoldableNode then s.insert ci.2 else s) ∅ }
        d.algebraicConstraints.length d.busInteractions.length
    else
      denseReencodeLoop b useIdx targets 0 reg d
        (if useIdx then denseBuildPruned DenseExpr.vars 8 d.algebraicConstraints else ⟨∅, []⟩)
        d.algebraicConstraints.toArray
        (Std.HashSet.ofList d.occ)
        (Thunk.mk (fun _ => denseBuildUseIdx d))
        d.algebraicConstraints.length d.busInteractions.length
  else (reg, d, [])

end ApcOptimizer.Dense
