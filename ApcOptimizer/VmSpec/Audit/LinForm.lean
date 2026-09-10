import ApcOptimizer.VmSpec.Audit.SendOnlyPolarity

set_option autoImplicit false

/-! **Linear normal forms for `Expression`.**

    A step layout is read off a circuit by comparing *payload expressions*: two bus interactions
    cancel when their payloads agree, and a bridge send sits `d` ticks after the receive when the
    two timestamp expressions differ by the constant `d`. Neither comparison is syntactic — powdr
    writes `2105016 + (p-1) * (192 * cmp)` where a reader sees `2105016 - 192 * cmp`.

    So expressions are normalized to a constant plus a coefficient **vector**, one entry per
    variable of a fixed list. A vector rather than an association list because that makes addition
    `zipWith (+)`, equality list equality, and "is this constant?" `all (· = 0)` — all decidable,
    all with one-line evaluation lemmas, and none of them needing a `Nodup` invariant on the
    variable list.

    Everything here is a *checker*: it either succeeds and hands back a fact, or fails. It is
    audited only through `LinForm.eval_toLin`, which is what every use cashes out to. -/

variable {p : ℕ}

/-- A linear form over a fixed variable list: a constant, and one coefficient per variable. -/
structure LinForm (p : ℕ) where
  /-- The constant term. -/
  const : ZMod p
  /-- One coefficient per variable of the ambient list, in the same order. -/
  coefs : List (ZMod p)
  deriving DecidableEq

/-- What a linear form denotes under an assignment. -/
def LinForm.eval (vs : List Variable) (f : LinForm p) (asg : Variable → ZMod p) : ZMod p :=
  f.const + (List.zipWith (fun v k => k * asg v) vs f.coefs).sum

/-- The zero-length-safe pointwise sum. -/
def LinForm.add (a b : LinForm p) : LinForm p :=
  ⟨a.const + b.const, List.zipWith (· + ·) a.coefs b.coefs⟩

/-- Scaling by a field constant. -/
def LinForm.smul (c : ZMod p) (a : LinForm p) : LinForm p :=
  ⟨c * a.const, a.coefs.map (c * ·)⟩

/-- The constant form, over `n` variables. -/
def LinForm.constF (n : ℕ) (c : ZMod p) : LinForm p := ⟨c, List.replicate n (0 : ZMod p)⟩

/-- The indicator vector for `v`: `1` at its first occurrence in `vs`, `0` elsewhere. -/
def oneHotFor (vs : List Variable) (v : Variable) : List (ZMod p) :=
  match vs with
  | [] => []
  | w :: t => if w = v then 1 :: List.replicate t.length 0 else 0 :: oneHotFor t v

/-- A single variable, as the form `0 + 1 * v`. All-zero when `v` is not in the list, which is why
    `Expression.toLin` refuses such an expression rather than normalizing it. -/
def LinForm.varF (vs : List Variable) (v : Variable) : LinForm p := ⟨0, oneHotFor vs v⟩

/-- Whether a form is the constant `c`: same constant, and every coefficient zero. -/
def LinForm.isConst (f : LinForm p) (c : ZMod p) : Bool :=
  f.const == c && f.coefs.all (· == 0)

--------- Evaluation ---------

theorem LinForm.eval_add (vs : List Variable) (a b : LinForm p) (asg : Variable → ZMod p)
    (ha : a.coefs.length = vs.length) (hb : b.coefs.length = vs.length) :
    (a.add b).eval vs asg = a.eval vs asg + b.eval vs asg := by
  simp only [LinForm.eval, LinForm.add]
  have hsum : ∀ (l : List Variable) (x y : List (ZMod p)), l.length = x.length →
      l.length = y.length →
      (List.zipWith (fun v k => k * asg v) l (List.zipWith (· + ·) x y)).sum
        = (List.zipWith (fun v k => k * asg v) l x).sum
          + (List.zipWith (fun v k => k * asg v) l y).sum := by
    intro l
    induction l with
    | nil => intro x y _ _; simp
    | cons v t ih =>
      intro x y hx hy
      match x, y with
      | xh :: xt, yh :: yt =>
        simp only [List.zipWith_cons_cons, List.sum_cons]
        rw [ih xt yt (by simpa using hx) (by simpa using hy)]
        ring
  rw [hsum vs a.coefs b.coefs ha.symm hb.symm]
  ring

theorem LinForm.eval_smul (vs : List Variable) (c : ZMod p) (a : LinForm p)
    (asg : Variable → ZMod p) :
    (LinForm.smul c a).eval vs asg = c * a.eval vs asg := by
  simp only [LinForm.eval, LinForm.smul]
  have hsum : ∀ (l : List Variable) (x : List (ZMod p)),
      (List.zipWith (fun v k => k * asg v) l (x.map (c * ·))).sum
        = c * (List.zipWith (fun v k => k * asg v) l x).sum := by
    intro l
    induction l with
    | nil => intro x; simp
    | cons v t ih =>
      intro x
      match x with
      | [] => simp
      | xh :: xt =>
        simp only [List.map_cons, List.zipWith_cons_cons, List.sum_cons]
        rw [ih xt]
        ring
  rw [hsum vs a.coefs]
  ring

/-- A zero coefficient vector denotes zero, at any length. -/
theorem zipWith_replicate_zero (asg : Variable → ZMod p) :
    ∀ (l : List Variable) (n : ℕ),
      (List.zipWith (fun v k => k * asg v) l (List.replicate n (0 : ZMod p))).sum = 0 := by
  intro l
  induction l with
  | nil => intro n; simp
  | cons v t ih =>
    intro n
    cases n with
    | zero => simp
    | succ n =>
      rw [List.replicate_succ, List.zipWith_cons_cons, List.sum_cons, ih n]
      ring

theorem LinForm.eval_constF (vs : List Variable) (c : ZMod p) (asg : Variable → ZMod p) :
    (LinForm.constF (p := p) vs.length c).eval vs asg = c := by
  simp only [LinForm.eval, LinForm.constF, add_eq_left]
  exact zipWith_replicate_zero asg vs vs.length

theorem LinForm.eval_varF (vs : List Variable) (v : Variable) (asg : Variable → ZMod p)
    (hv : v ∈ vs) : (LinForm.varF (p := p) vs v).eval vs asg = asg v := by
  simp only [LinForm.eval, LinForm.varF, zero_add]
  induction vs with
  | nil => exact absurd hv (by simp)
  | cons w t ih =>
    simp only [oneHotFor]
    by_cases hw : w = v
    · rw [if_pos hw, List.zipWith_cons_cons, List.sum_cons, zipWith_replicate_zero, hw]
      ring
    · rw [if_neg hw, List.zipWith_cons_cons, List.sum_cons]
      have hvt : v ∈ t := by
        rcases List.mem_cons.mp hv with h | h
        · exact absurd h.symm hw
        · exact h
      rw [ih hvt]
      ring

--------- Lengths ---------

theorem oneHotFor_length (vs : List Variable) (v : Variable) :
    (oneHotFor (p := p) vs v).length = vs.length := by
  induction vs with
  | nil => rfl
  | cons w t ih =>
    simp only [oneHotFor]
    by_cases hw : w = v <;> simp [hw, ih]

/-- Every form `Expression.toLin` builds has one coefficient per variable, which is what
    `LinForm.eval_add` needs. -/
def LinForm.Sized (n : ℕ) (f : LinForm p) : Prop := f.coefs.length = n

theorem LinForm.sized_constF (n : ℕ) (c : ZMod p) : (LinForm.constF n c).Sized n := by
  simp [LinForm.Sized, LinForm.constF]

theorem LinForm.sized_varF (vs : List Variable) (v : Variable) :
    (LinForm.varF (p := p) vs v).Sized vs.length := oneHotFor_length vs v

theorem LinForm.sized_add {n : ℕ} {a b : LinForm p} (ha : a.Sized n) (hb : b.Sized n) :
    (a.add b).Sized n := by
  simp only [LinForm.Sized, LinForm.add] at *
  rw [List.length_zipWith, ha, hb, Nat.min_self]

theorem LinForm.sized_smul {n : ℕ} {c : ZMod p} {a : LinForm p} (ha : a.Sized n) :
    (LinForm.smul c a).Sized n := by
  simpa [LinForm.Sized, LinForm.smul] using ha

/-- A form with every coefficient zero denotes its constant. -/
theorem LinForm.eval_of_coefs_zero (vs : List Variable) (f : LinForm p)
    (asg : Variable → ZMod p) (h : f.coefs.all (· == 0) = true) : f.eval vs asg = f.const := by
  simp only [LinForm.eval, add_eq_left]
  have hz : ∀ (l : List Variable) (x : List (ZMod p)), x.all (· == 0) = true →
      (List.zipWith (fun v k => k * asg v) l x).sum = 0 := by
    intro l
    induction l with
    | nil => intro x _; simp
    | cons v t ih =>
      intro x hx
      match x with
      | [] => simp
      | xh :: xt =>
        simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at hx
        rw [List.zipWith_cons_cons, List.sum_cons, ih xt hx.2, hx.1]
        ring
  exact hz vs f.coefs h

--------- The normalizer ---------

/-- **Normalize an expression to a linear form** over `vs`, folding any subexpression the pin rules
    pin to a constant. Fails on a genuine nonlinearity, and on a variable outside `vs`. -/
def Expression.toLin (vs : List Variable) (rules : List (PinRule p)) :
    Expression p → Option (LinForm p)
  | .const c => some (LinForm.constF vs.length c)
  | .var v =>
    match lookupPin rules (.var v) with
    | some c => some (LinForm.constF vs.length c)
    | none => if vs.contains v then some (LinForm.varF vs v) else none
  | .add a b =>
    match Expression.toLin vs rules a, Expression.toLin vs rules b with
    | some fa, some fb => some (fa.add fb)
    | _, _ => none
  | .mul a b =>
    match Expression.toLin vs rules a, Expression.toLin vs rules b with
    | some fa, some fb =>
      if fa.coefs.all (· == 0) then some (LinForm.smul fa.const fb)
      else if fb.coefs.all (· == 0) then some (LinForm.smul fb.const fa)
      else none
    | _, _ => none

theorem Expression.toLin_sized {vs : List Variable} {rules : List (PinRule p)} :
    ∀ {e : Expression p} {f : LinForm p}, e.toLin vs rules = some f → f.Sized vs.length := by
  intro e
  induction e with
  | const c => intro f h; cases h; exact LinForm.sized_constF _ _
  | var v =>
    intro f h
    simp only [Expression.toLin] at h
    cases hp : lookupPin rules (.var v) with
    | some c => rw [hp] at h; cases h; exact LinForm.sized_constF _ _
    | none =>
      rw [hp] at h
      by_cases hv : vs.contains v
      · rw [if_pos hv] at h; cases h; exact LinForm.sized_varF _ _
      · rw [if_neg hv] at h; cases h
  | add a b iha ihb =>
    intro f h
    simp only [Expression.toLin] at h
    cases h1 : a.toLin vs rules with
    | none => rw [h1] at h; cases h
    | some fa =>
      cases h2 : b.toLin vs rules with
      | none => rw [h1, h2] at h; cases h
      | some fb => rw [h1, h2] at h; cases h; exact LinForm.sized_add (iha h1) (ihb h2)
  | mul a b iha ihb =>
    intro f h
    simp only [Expression.toLin] at h
    cases h1 : a.toLin vs rules with
    | none => rw [h1] at h; cases h
    | some fa =>
      cases h2 : b.toLin vs rules with
      | none => rw [h1, h2] at h; cases h
      | some fb =>
        rw [h1, h2] at h
        dsimp only at h
        by_cases hza : fa.coefs.all (· == 0)
        · rw [if_pos hza] at h; cases h; exact LinForm.sized_smul (ihb h2)
        · rw [if_neg hza] at h
          by_cases hzb : fb.coefs.all (· == 0)
          · rw [if_pos hzb] at h; cases h; exact LinForm.sized_smul (iha h1)
          · rw [if_neg hzb] at h; cases h

/-- **What the normalizer promises**: the form denotes the expression, on any assignment the pin
    rules hold at. -/
theorem Expression.toLin_eval {vs : List Variable} {rules : List (PinRule p)}
    {asg : Variable → ZMod p} (hrules : ∀ q ∈ rules, q.1.eval asg = q.2) :
    ∀ {e : Expression p} {f : LinForm p}, e.toLin vs rules = some f →
      e.eval asg = f.eval vs asg := by
  intro e
  induction e with
  | const c => intro f h; cases h; rw [LinForm.eval_constF]; rfl
  | var v =>
    intro f h
    simp only [Expression.toLin] at h
    cases hp : lookupPin rules (.var v) with
    | some c =>
      rw [hp] at h; cases h
      rw [LinForm.eval_constF]
      exact hrules _ (lookupPin_mem hp)
    | none =>
      rw [hp] at h
      by_cases hv : vs.contains v
      · rw [if_pos hv] at h; cases h
        exact (LinForm.eval_varF vs v asg (List.mem_of_elem_eq_true hv)).symm
      · rw [if_neg hv] at h; cases h
  | add a b iha ihb =>
    intro f h
    simp only [Expression.toLin] at h
    cases h1 : a.toLin vs rules with
    | none => rw [h1] at h; cases h
    | some fa =>
      cases h2 : b.toLin vs rules with
      | none => rw [h1, h2] at h; cases h
      | some fb =>
        rw [h1, h2] at h; cases h
        rw [LinForm.eval_add vs fa fb asg (Expression.toLin_sized h1) (Expression.toLin_sized h2)]
        exact congrArg₂ (· + ·) (iha h1) (ihb h2)
  | mul a b iha ihb =>
    intro f h
    simp only [Expression.toLin] at h
    cases h1 : a.toLin vs rules with
    | none => rw [h1] at h; cases h
    | some fa =>
      cases h2 : b.toLin vs rules with
      | none => rw [h1, h2] at h; cases h
      | some fb =>
        rw [h1, h2] at h
        dsimp only at h
        by_cases hza : fa.coefs.all (· == 0)
        · rw [if_pos hza] at h; cases h
          rw [LinForm.eval_smul, Expression.eval, iha h1, ihb h2,
            LinForm.eval_of_coefs_zero vs fa asg hza]
        · rw [if_neg hza] at h
          by_cases hzb : fb.coefs.all (· == 0)
          · rw [if_pos hzb] at h; cases h
            rw [LinForm.eval_smul, Expression.eval, iha h1, ihb h2,
              LinForm.eval_of_coefs_zero vs fb asg hzb]
            ring
          · rw [if_neg hzb] at h; cases h


--------- Reading a circuit's traffic on one bus ---------

/-- One bus interaction as the checker sees it: a folded multiplicity and a normalized payload. -/
abbrev BusEntry (p : ℕ) := ZMod p × List (LinForm p)

/-- What an entry's payload denotes. -/
def BusEntry.payloadAt (vs : List Variable) (e : BusEntry p) (asg : Variable → ZMod p) :
    List (ZMod p) :=
  e.2.map (fun f => f.eval vs asg)

/-- Normalize a payload, component by component. -/
def payloadLin (vs : List Variable) (rules : List (PinRule p)) :
    List (Expression p) → Option (List (LinForm p))
  | [] => some []
  | x :: t =>
    match Expression.toLin vs rules x, payloadLin vs rules t with
    | some f, some ft => some (f :: ft)
    | _, _ => none

theorem payloadLin_eval {vs : List Variable} {rules : List (PinRule p)}
    {asg : Variable → ZMod p} (hrules : ∀ q ∈ rules, q.1.eval asg = q.2) :
    ∀ {l : List (Expression p)} {fs : List (LinForm p)}, payloadLin vs rules l = some fs →
      l.map (fun e => e.eval asg) = fs.map (fun f => f.eval vs asg) := by
  intro l
  induction l with
  | nil => intro fs h; simp only [payloadLin, Option.some.injEq] at h; rw [← h]; rfl
  | cons x t ih =>
    intro fs h
    simp only [payloadLin] at h
    cases hx : Expression.toLin vs rules x with
    | none => rw [hx] at h; cases h
    | some f =>
      cases ht : payloadLin vs rules t with
      | none => rw [hx, ht] at h; cases h
      | some ft =>
        rw [hx, ht] at h
        simp only [Option.some.injEq] at h
        rw [← h, List.map_cons, List.map_cons, Expression.toLin_eval hrules hx, ih ht]

/-- Normalize one interaction; fails if its multiplicity does not fold or its payload does not
    linearize. -/
def busEntry (vs : List Variable) (rules : List (PinRule p))
    (bi : BusInteraction (Expression p)) : Option (BusEntry p) :=
  match bi.multiplicity.foldConstWith rules, payloadLin vs rules bi.payload with
  | some mu, some pl => some (mu, pl)
  | _, _ => none

/-- Normalize every interaction a circuit makes on bus `b`, in list order. -/
def busEntries (vs : List Variable) (rules : List (PinRule p)) (b : ℕ) :
    List (BusInteraction (Expression p)) → Option (List (BusEntry p))
  | [] => some []
  | bi :: t =>
    if bi.busId = b then
      match busEntry vs rules bi, busEntries vs rules b t with
      | some e, some es => some (e :: es)
      | _, _ => none
    else busEntries vs rules b t

theorem busEntry_eval {vs : List Variable} {rules : List (PinRule p)}
    {asg : Variable → ZMod p} (hrules : ∀ q ∈ rules, q.1.eval asg = q.2)
    {bi : BusInteraction (Expression p)} {e : BusEntry p} (h : busEntry vs rules bi = some e) :
    (bi.eval asg).multiplicity = e.1 ∧ (bi.eval asg).payload = BusEntry.payloadAt vs e asg := by
  simp only [busEntry] at h
  cases hmu : bi.multiplicity.foldConstWith rules with
  | none => rw [hmu] at h; cases h
  | some mu =>
    cases hpl : payloadLin vs rules bi.payload with
    | none => rw [hmu, hpl] at h; cases h
    | some pl =>
      rw [hmu, hpl] at h
      simp only [Option.some.injEq] at h
      rw [← h]
      exact ⟨Expression.foldConstWith_eq hrules hmu, payloadLin_eval hrules hpl⟩

/-- `Circuit.allEffects` as a sum of guarded multiplicities, one per interaction. -/
theorem allEffects_eq_mapIf (c : Circuit p) (asg : ChipAssignment p) (m : BusMessage p) :
    c.allEffects asg m
      = (c.busInteractions.map (fun bi =>
          if ((bi.eval asg).busId, (bi.eval asg).payload) = m then (bi.eval asg).multiplicity
          else 0)).sum := by
  simp only [Circuit.allEffects]
  induction c.busInteractions with
  | nil => simp
  | cons bi t ih =>
    simp only [List.map_cons, List.filter_cons, List.sum_cons, ← ih]
    by_cases h : ((bi.eval asg).busId, (bi.eval asg).payload) = m
    · rw [if_pos h, decide_eq_true h]
      simp
    · rw [if_neg h, decide_eq_false h]
      simp

theorem entrySum_eq {vs : List Variable} {rules : List (PinRule p)} {asg : ChipAssignment p}
    (hrules : ∀ q ∈ rules, q.1.eval asg = q.2) (b : ℕ) (m : BusMessage p) (hm : m.1 = b) :
    ∀ (L : List (BusInteraction (Expression p))) {es : List (BusEntry p)},
      busEntries vs rules b L = some es →
      (L.map (fun bi =>
          if ((bi.eval asg).busId, (bi.eval asg).payload) = m then (bi.eval asg).multiplicity
          else 0)).sum
        = (es.map (fun e => if BusEntry.payloadAt vs e asg = m.2 then e.1 else 0)).sum := by
  intro L
  induction L with
  | nil =>
    intro es h
    simp only [busEntries, Option.some.injEq] at h
    rw [← h]; simp
  | cons bi t ih =>
    intro es h
    simp only [busEntries] at h
    by_cases hb : bi.busId = b
    · rw [if_pos hb] at h
      cases he : busEntry vs rules bi with
      | none => rw [he] at h; cases h
      | some e =>
        cases ht : busEntries vs rules b t with
        | none => rw [he, ht] at h; cases h
        | some est =>
          rw [he, ht] at h
          simp only [Option.some.injEq] at h
          obtain ⟨hmu, hpl⟩ := busEntry_eval hrules he
          rw [← h, List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ih ht, hmu]
          congr 1
          by_cases hq : BusEntry.payloadAt vs e asg = m.2
          · refine (if_pos ?_).trans (if_pos hq).symm
            refine Prod.ext ?_ (hpl.trans hq)
            simp only [BusInteraction.eval]
            rw [hb, hm]
          · refine (if_neg ?_).trans (if_neg hq).symm
            exact fun hc => hq (hpl.symm.trans (Prod.ext_iff.mp hc).2)
    · rw [if_neg hb] at h
      rw [List.map_cons, List.sum_cons, ih h, if_neg, zero_add]
      intro hc
      refine hb ?_
      have := (Prod.ext_iff.mp hc).1
      simp only [BusInteraction.eval] at this
      rw [this, hm]

/-- **The circuit's net on a bus, read off the normalized entries.** -/
theorem allEffects_eq_entrySum {vs : List Variable} {rules : List (PinRule p)}
    {asg : ChipAssignment p} (hrules : ∀ q ∈ rules, q.1.eval asg = q.2)
    (c : Circuit p) (b : ℕ) {es : List (BusEntry p)}
    (h : busEntries vs rules b c.busInteractions = some es)
    (m : BusMessage p) (hm : m.1 = b) :
    c.allEffects asg m
      = (es.map (fun e => if BusEntry.payloadAt vs e asg = m.2 then e.1 else 0)).sum := by
  rw [allEffects_eq_mapIf]
  exact entrySum_eq hrules b m hm c.busInteractions h

--------- Linear pins: a variable known equal to a *combination* of others ---------

/-- A pin from one variable to a linear combination of others — `(from_state__timestamp_1,
    from_state__timestamp_0 + 3)` for a fused APC's chained clock, say — rather than
    `PinRule`'s variable-to-*constant* pin. Read off a constraint by hand today (see
    `Apcs/Keccak2105000/UnoptChained.lean`'s `unoptLinRules`); nothing here computes one. -/
abbrev LinPinRule (p : ℕ) := Variable × LinForm p

/-- Look one variable up among the linear pins, by name. -/
def lookupLinPin (rules : List (LinPinRule p)) (v : Variable) : Option (LinForm p) :=
  (rules.find? (fun r => decide (r.1 = v))).map Prod.snd

theorem lookupLinPin_mem {rules : List (LinPinRule p)} {v : Variable} {f : LinForm p}
    (h : lookupLinPin rules v = some f) : (v, f) ∈ rules := by
  unfold lookupLinPin at h
  cases hf : rules.find? (fun r => decide (r.1 = v)) with
  | none => rw [hf] at h; cases h
  | some r =>
    rw [hf] at h
    simp only [Option.map_some, Option.some.injEq] at h
    have hmem := List.mem_of_find?_eq_some hf
    have hp : decide (r.1 = v) = true := List.find?_some (p := fun q : LinPinRule p =>
      decide (q.1 = v)) hf
    rw [← of_decide_eq_true hp, ← h]
    exact hmem

/-- **`Expression.toLin`, additionally substituting a variable known equal to a linear combination
    of others.** Tries the constant pins first (unchanged from `Expression.toLin`), then the linear
    ones. With `linRules := []` this is exactly `Expression.toLin` — a separate definition, not a
    generalization of it, so nothing already built on `Expression.toLin` needs to change. -/
def Expression.toLinL (vs : List Variable) (rules : List (PinRule p))
    (linRules : List (LinPinRule p)) : Expression p → Option (LinForm p)
  | .const c => some (LinForm.constF vs.length c)
  | .var v =>
    match lookupPin rules (.var v) with
    | some c => some (LinForm.constF vs.length c)
    | none =>
      match lookupLinPin linRules v with
      | some f => some f
      | none => if vs.contains v then some (LinForm.varF vs v) else none
  | .add a b =>
    match Expression.toLinL vs rules linRules a, Expression.toLinL vs rules linRules b with
    | some fa, some fb => some (fa.add fb)
    | _, _ => none
  | .mul a b =>
    match Expression.toLinL vs rules linRules a, Expression.toLinL vs rules linRules b with
    | some fa, some fb =>
      if fa.coefs.all (· == 0) then some (LinForm.smul fa.const fb)
      else if fb.coefs.all (· == 0) then some (LinForm.smul fb.const fa)
      else none
    | _, _ => none

theorem Expression.toLinL_sized {vs : List Variable} {rules : List (PinRule p)}
    {linRules : List (LinPinRule p)} (hlinSized : ∀ q ∈ linRules, q.2.Sized vs.length) :
    ∀ {e : Expression p} {f : LinForm p}, e.toLinL vs rules linRules = some f →
      f.Sized vs.length := by
  intro e
  induction e with
  | const c => intro f h; cases h; exact LinForm.sized_constF _ _
  | var v =>
    intro f h
    simp only [Expression.toLinL] at h
    cases hp : lookupPin rules (.var v) with
    | some c => rw [hp] at h; cases h; exact LinForm.sized_constF _ _
    | none =>
      rw [hp] at h
      cases hl : lookupLinPin linRules v with
      | some fl => rw [hl] at h; cases h; exact hlinSized _ (lookupLinPin_mem hl)
      | none =>
        rw [hl] at h
        by_cases hv : vs.contains v
        · rw [if_pos hv] at h; cases h; exact LinForm.sized_varF _ _
        · rw [if_neg hv] at h; cases h
  | add a b iha ihb =>
    intro f h
    simp only [Expression.toLinL] at h
    cases h1 : a.toLinL vs rules linRules with
    | none => rw [h1] at h; cases h
    | some fa =>
      cases h2 : b.toLinL vs rules linRules with
      | none => rw [h1, h2] at h; cases h
      | some fb => rw [h1, h2] at h; cases h; exact LinForm.sized_add (iha h1) (ihb h2)
  | mul a b iha ihb =>
    intro f h
    simp only [Expression.toLinL] at h
    cases h1 : a.toLinL vs rules linRules with
    | none => rw [h1] at h; cases h
    | some fa =>
      cases h2 : b.toLinL vs rules linRules with
      | none => rw [h1, h2] at h; cases h
      | some fb =>
        rw [h1, h2] at h
        dsimp only at h
        by_cases hza : fa.coefs.all (· == 0)
        · rw [if_pos hza] at h; cases h; exact LinForm.sized_smul (ihb h2)
        · rw [if_neg hza] at h
          by_cases hzb : fb.coefs.all (· == 0)
          · rw [if_pos hzb] at h; cases h; exact LinForm.sized_smul (iha h1)
          · rw [if_neg hzb] at h; cases h

/-- **What `Expression.toLinL` promises**: as `Expression.toLin_eval`, plus that every linear pin
    holds under `asg`. -/
theorem Expression.toLinL_eval {vs : List Variable} {rules : List (PinRule p)}
    {linRules : List (LinPinRule p)} {asg : Variable → ZMod p}
    (hrules : ∀ q ∈ rules, q.1.eval asg = q.2)
    (hlinSized : ∀ q ∈ linRules, q.2.Sized vs.length)
    (hlinRules : ∀ q ∈ linRules, asg q.1 = q.2.eval vs asg) :
    ∀ {e : Expression p} {f : LinForm p}, e.toLinL vs rules linRules = some f →
      e.eval asg = f.eval vs asg := by
  intro e
  induction e with
  | const c => intro f h; cases h; rw [LinForm.eval_constF]; rfl
  | var v =>
    intro f h
    simp only [Expression.toLinL] at h
    cases hp : lookupPin rules (.var v) with
    | some c =>
      rw [hp] at h; cases h
      rw [LinForm.eval_constF]
      exact hrules _ (lookupPin_mem hp)
    | none =>
      rw [hp] at h
      cases hl : lookupLinPin linRules v with
      | some fl =>
        rw [hl] at h; cases h
        exact hlinRules _ (lookupLinPin_mem hl)
      | none =>
        rw [hl] at h
        by_cases hv : vs.contains v
        · rw [if_pos hv] at h; cases h
          exact (LinForm.eval_varF vs v asg (List.mem_of_elem_eq_true hv)).symm
        · rw [if_neg hv] at h; cases h
  | add a b iha ihb =>
    intro f h
    simp only [Expression.toLinL] at h
    cases h1 : a.toLinL vs rules linRules with
    | none => rw [h1] at h; cases h
    | some fa =>
      cases h2 : b.toLinL vs rules linRules with
      | none => rw [h1, h2] at h; cases h
      | some fb =>
        rw [h1, h2] at h; cases h
        rw [LinForm.eval_add vs fa fb asg (Expression.toLinL_sized hlinSized h1)
          (Expression.toLinL_sized hlinSized h2)]
        exact congrArg₂ (· + ·) (iha h1) (ihb h2)
  | mul a b iha ihb =>
    intro f h
    simp only [Expression.toLinL] at h
    cases h1 : a.toLinL vs rules linRules with
    | none => rw [h1] at h; cases h
    | some fa =>
      cases h2 : b.toLinL vs rules linRules with
      | none => rw [h1, h2] at h; cases h
      | some fb =>
        rw [h1, h2] at h
        dsimp only at h
        by_cases hza : fa.coefs.all (· == 0)
        · rw [if_pos hza] at h; cases h
          rw [LinForm.eval_smul, Expression.eval, iha h1, ihb h2,
            LinForm.eval_of_coefs_zero vs fa asg hza]
        · rw [if_neg hza] at h
          by_cases hzb : fb.coefs.all (· == 0)
          · rw [if_pos hzb] at h; cases h
            rw [LinForm.eval_smul, Expression.eval, iha h1, ihb h2,
              LinForm.eval_of_coefs_zero vs fb asg hzb]
            ring
          · rw [if_neg hzb] at h; cases h

/-- Normalize a payload, component by component, with linear pins. -/
def payloadLinL (vs : List Variable) (rules : List (PinRule p)) (linRules : List (LinPinRule p)) :
    List (Expression p) → Option (List (LinForm p))
  | [] => some []
  | x :: t =>
    match Expression.toLinL vs rules linRules x, payloadLinL vs rules linRules t with
    | some f, some ft => some (f :: ft)
    | _, _ => none

theorem payloadLinL_eval {vs : List Variable} {rules : List (PinRule p)}
    {linRules : List (LinPinRule p)} {asg : Variable → ZMod p}
    (hrules : ∀ q ∈ rules, q.1.eval asg = q.2)
    (hlinSized : ∀ q ∈ linRules, q.2.Sized vs.length)
    (hlinRules : ∀ q ∈ linRules, asg q.1 = q.2.eval vs asg) :
    ∀ {l : List (Expression p)} {fs : List (LinForm p)},
      payloadLinL vs rules linRules l = some fs →
      l.map (fun e => e.eval asg) = fs.map (fun f => f.eval vs asg) := by
  intro l
  induction l with
  | nil => intro fs h; simp only [payloadLinL, Option.some.injEq] at h; rw [← h]; rfl
  | cons x t ih =>
    intro fs h
    simp only [payloadLinL] at h
    cases hx : Expression.toLinL vs rules linRules x with
    | none => rw [hx] at h; cases h
    | some f =>
      cases ht : payloadLinL vs rules linRules t with
      | none => rw [hx, ht] at h; cases h
      | some ft =>
        rw [hx, ht] at h
        simp only [Option.some.injEq] at h
        rw [← h, List.map_cons, List.map_cons,
          Expression.toLinL_eval hrules hlinSized hlinRules hx, ih ht]

/-- Normalize one interaction; fails if its multiplicity does not fold or its payload does not
    linearize, with linear pins. -/
def busEntryL (vs : List Variable) (rules : List (PinRule p)) (linRules : List (LinPinRule p))
    (bi : BusInteraction (Expression p)) : Option (BusEntry p) :=
  match bi.multiplicity.foldConstWith rules, payloadLinL vs rules linRules bi.payload with
  | some mu, some pl => some (mu, pl)
  | _, _ => none

/-- Normalize every interaction a circuit makes on bus `b`, in list order, with linear pins. -/
def busEntriesL (vs : List Variable) (rules : List (PinRule p)) (linRules : List (LinPinRule p))
    (b : ℕ) : List (BusInteraction (Expression p)) → Option (List (BusEntry p))
  | [] => some []
  | bi :: t =>
    if bi.busId = b then
      match busEntryL vs rules linRules bi, busEntriesL vs rules linRules b t with
      | some e, some es => some (e :: es)
      | _, _ => none
    else busEntriesL vs rules linRules b t

theorem busEntryL_eval {vs : List Variable} {rules : List (PinRule p)}
    {linRules : List (LinPinRule p)} {asg : Variable → ZMod p}
    (hrules : ∀ q ∈ rules, q.1.eval asg = q.2)
    (hlinSized : ∀ q ∈ linRules, q.2.Sized vs.length)
    (hlinRules : ∀ q ∈ linRules, asg q.1 = q.2.eval vs asg)
    {bi : BusInteraction (Expression p)} {e : BusEntry p}
    (h : busEntryL vs rules linRules bi = some e) :
    (bi.eval asg).multiplicity = e.1 ∧ (bi.eval asg).payload = BusEntry.payloadAt vs e asg := by
  simp only [busEntryL] at h
  cases hmu : bi.multiplicity.foldConstWith rules with
  | none => rw [hmu] at h; cases h
  | some mu =>
    cases hpl : payloadLinL vs rules linRules bi.payload with
    | none => rw [hmu, hpl] at h; cases h
    | some pl =>
      rw [hmu, hpl] at h
      simp only [Option.some.injEq] at h
      rw [← h]
      exact ⟨Expression.foldConstWith_eq hrules hmu,
        payloadLinL_eval hrules hlinSized hlinRules hpl⟩

theorem entrySumL_eq {vs : List Variable} {rules : List (PinRule p)}
    {linRules : List (LinPinRule p)} {asg : ChipAssignment p}
    (hrules : ∀ q ∈ rules, q.1.eval asg = q.2)
    (hlinSized : ∀ q ∈ linRules, q.2.Sized vs.length)
    (hlinRules : ∀ q ∈ linRules, asg q.1 = q.2.eval vs asg)
    (b : ℕ) (m : BusMessage p) (hm : m.1 = b) :
    ∀ (L : List (BusInteraction (Expression p))) {es : List (BusEntry p)},
      busEntriesL vs rules linRules b L = some es →
      (L.map (fun bi =>
          if ((bi.eval asg).busId, (bi.eval asg).payload) = m then (bi.eval asg).multiplicity
          else 0)).sum
        = (es.map (fun e => if BusEntry.payloadAt vs e asg = m.2 then e.1 else 0)).sum := by
  intro L
  induction L with
  | nil =>
    intro es h
    simp only [busEntriesL, Option.some.injEq] at h
    rw [← h]; simp
  | cons bi t ih =>
    intro es h
    simp only [busEntriesL] at h
    by_cases hb : bi.busId = b
    · rw [if_pos hb] at h
      cases he : busEntryL vs rules linRules bi with
      | none => rw [he] at h; cases h
      | some e =>
        cases ht : busEntriesL vs rules linRules b t with
        | none => rw [he, ht] at h; cases h
        | some est =>
          rw [he, ht] at h
          simp only [Option.some.injEq] at h
          obtain ⟨hmu, hpl⟩ := busEntryL_eval hrules hlinSized hlinRules he
          rw [← h, List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ih ht, hmu]
          congr 1
          by_cases hq : BusEntry.payloadAt vs e asg = m.2
          · refine (if_pos ?_).trans (if_pos hq).symm
            refine Prod.ext ?_ (hpl.trans hq)
            simp only [BusInteraction.eval]
            rw [hb, hm]
          · refine (if_neg ?_).trans (if_neg hq).symm
            exact fun hc => hq (hpl.symm.trans (Prod.ext_iff.mp hc).2)
    · rw [if_neg hb] at h
      rw [List.map_cons, List.sum_cons, ih h, if_neg, zero_add]
      intro hc
      refine hb ?_
      have := (Prod.ext_iff.mp hc).1
      simp only [BusInteraction.eval] at this
      rw [this, hm]

/-- **The circuit's net on a bus, read off the normalized entries, with linear pins.** -/
theorem allEffects_eq_entrySumL {vs : List Variable} {rules : List (PinRule p)}
    {linRules : List (LinPinRule p)} {asg : ChipAssignment p}
    (hrules : ∀ q ∈ rules, q.1.eval asg = q.2)
    (hlinSized : ∀ q ∈ linRules, q.2.Sized vs.length)
    (hlinRules : ∀ q ∈ linRules, asg q.1 = q.2.eval vs asg)
    (c : Circuit p) (b : ℕ) {es : List (BusEntry p)}
    (h : busEntriesL vs rules linRules b c.busInteractions = some es)
    (m : BusMessage p) (hm : m.1 = b) :
    c.allEffects asg m
      = (es.map (fun e => if BusEntry.payloadAt vs e asg = m.2 then e.1 else 0)).sum := by
  rw [allEffects_eq_mapIf]
  exact entrySumL_eq hrules hlinSized hlinRules b m hm c.busInteractions h
