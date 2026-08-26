import ApcOptimizer.VmSpec.Audit.LinForm
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

/-! **A static check for `StepLayout`'s bridge conditions.**

    `StepLayout` asks a chip to receive one execution-bridge state, send one `d` ticks later, and
    put nothing else there. Read the chip's bridge traffic as normalized entries (`busEntries`) and
    that becomes a list condition: the first entry is the receive, the last is the send, and
    everything between cancels in consecutive pairs — which is exactly the shape a *fused* APC has
    once powdr's substitution pass chains its intermediate timestamps, one pair per seam.

    `bridgeCheck` decides all of it; `bridgeCheck_sound` turns a `true` into the three fields. -/

variable {p : ℕ}

--------- Cancelling pairs ---------

/-- Whether a list of entries cancels in consecutive pairs: same payload, opposite multiplicity. -/
def pairsCancel : List (BusEntry p) → Bool
  | [] => true
  | [_] => false
  | a :: b :: t => (a.2 == b.2) && (a.1 + b.1 == 0) && pairsCancel t

/-- Cancelling pairs contribute nothing to the net at *any* message: the two entries of a pair
    have the same payload, so they are counted together or not at all. -/
theorem pairsCancel_sum (vs : List Variable) (asg : Variable → ZMod p)
    (tgt : List (ZMod p)) :
    ∀ l : List (BusEntry p), pairsCancel l = true →
      (l.map (fun e => if BusEntry.payloadAt vs e asg = tgt then e.1 else 0)).sum = 0 := by
  intro l
  induction l using pairsCancel.induct with
  | case1 => intro _; simp
  | case2 _ => intro h; simp only [pairsCancel] at h; exact absurd h (by simp)
  | case3 a b t ih =>
    intro h
    simp only [pairsCancel, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hpl, hmu⟩, ht⟩ := h
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ih ht, add_zero]
    simp only [BusEntry.payloadAt, hpl]
    by_cases hq : List.map (fun f => LinForm.eval vs f asg) b.2 = tgt
    · rw [if_pos hq, if_pos hq, hmu]
    · rw [if_neg hq, if_neg hq, add_zero]

--------- Splitting off the two ends ---------

/-- The last element of a list, with everything before it. -/
def unsnoc {α : Type _} : List α → Option (List α × α)
  | [] => none
  | [a] => some ([], a)
  | a :: t => match unsnoc t with
    | some (l, x) => some (a :: l, x)
    | none => none

theorem unsnoc_eq {α : Type _} : ∀ {l : List α} {init : List α} {last : α},
    unsnoc l = some (init, last) → l = init ++ [last] := by
  intro l
  induction l using unsnoc.induct with
  | case1 => intro init last h; cases h
  | case2 a =>
    intro init last h
    simp only [unsnoc, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1, ← h.2]; rfl
  | case3 a t q l x hu ih =>
    intro init last h
    simp only [unsnoc, hu] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1, ← h.2, List.cons_append]
    exact congrArg (a :: ·) (ih hu)
  | case4 a t _ hu _ =>
    intro init last h
    simp only [unsnoc, hu] at h
    cases h

--------- Distinctness and the clock step ---------

/-- Two payloads whose forms at position `k` differ by a nonzero constant denote different
    messages. Same coefficients, different constant — which is how a step's two bridge endpoints
    differ, their timestamps being `t` and `t + d`. -/
def payloadDistinctAt (a b : List (LinForm p)) (k : ℕ) : Bool :=
  match a[k]?, b[k]? with
  | some fa, some fb => (fa.coefs == fb.coefs) && !(fa.const == fb.const)
  | _, _ => false

theorem payloadAt_ne_of_distinctAt {vs : List Variable} {asg : Variable → ZMod p}
    {a b : List (LinForm p)} {k : ℕ} (h : payloadDistinctAt a b k = true) :
    a.map (fun f => f.eval vs asg) ≠ b.map (fun f => f.eval vs asg) := by
  simp only [payloadDistinctAt] at h
  cases ha : a[k]? with
  | none => rw [ha] at h; cases h
  | some fa =>
    cases hb : b[k]? with
    | none => rw [ha, hb] at h; cases h
    | some fb =>
      rw [ha, hb] at h
      simp only [Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, beq_iff_eq,
        ne_eq] at h
      intro hc
      refine h.2 ?_
      have hka : (a.map (fun f => LinForm.eval vs f asg))[k]? = some (fa.eval vs asg) := by
        rw [List.getElem?_map, ha]; rfl
      have hkb : (b.map (fun f => LinForm.eval vs f asg))[k]? = some (fb.eval vs asg) := by
        rw [List.getElem?_map, hb]; rfl
      rw [hc, hkb] at hka
      have heq := (Option.some.inj hka).symm
      simp only [LinForm.eval, h.1] at heq
      exact add_right_cancel heq

/-- Whether `b` is `a` shifted by the constant `d`. -/
def linShiftedBy (a b : LinForm p) (d : ZMod p) : Bool :=
  (b.const == a.const + d) && (b.coefs == a.coefs)

theorem eval_of_linShiftedBy {vs : List Variable} {asg : Variable → ZMod p}
    {a b : LinForm p} {d : ZMod p} (h : linShiftedBy a b d = true) :
    b.eval vs asg = a.eval vs asg + d := by
  simp only [linShiftedBy, Bool.and_eq_true, beq_iff_eq] at h
  simp only [LinForm.eval, h.1, h.2]
  ring

--------- The check ---------

/-- **The bridge check.** Reads the chip's traffic on bus `b`, and asks that it be a receive, a
    run of cancelling pairs, and a send `d` ticks later, on payloads `[pc, timestamp]`. The three
    expressions name the step's endpoints, and are checked against the traffic — so a caller gets
    back facts about messages it wrote itself, rather than about opaque witnesses. -/
def bridgeCheck (vs : List Variable) (rules : List (PinRule p)) (b : ℕ)
    (c : Circuit p) (d : ℕ) (distPos : ℕ) (pcFromE baseE pcToE : Expression p) : Bool :=
  match busEntries vs rules b c.busInteractions with
  | none => false
  | some [] => false
  | some (recvE :: t) =>
    match unsnoc t with
    | none => false
    | some (mid, sendE) =>
      pairsCancel mid
        && (recvE.1 == -1) && (sendE.1 == 1)
        && (recvE.2.length == 2) && (sendE.2.length == 2)
        && payloadDistinctAt recvE.2 sendE.2 distPos
        && (Expression.toLin vs rules pcFromE == recvE.2[0]?)
        && (Expression.toLin vs rules baseE == recvE.2[1]?)
        && (Expression.toLin vs rules pcToE == sendE.2[0]?)
        && (match recvE.2[1]?, sendE.2[1]? with
            | some fr, some fs => linShiftedBy fr fs ((d : ℕ) : ZMod p)
            | _, _ => false)

/-- **Soundness of the bridge check.** A `true` gives the three `StepLayout` fields that speak
    about the execution bridge, on the endpoints the caller named. -/
theorem bridgeCheck_sound {vs : List Variable} {rules : List (PinRule p)} {b : ℕ}
    {c : Circuit p} {d distPos : ℕ} {pcFromE baseE pcToE : Expression p}
    (h : bridgeCheck vs rules b c d distPos pcFromE baseE pcToE = true)
    {asg : ChipAssignment p} (hrules : ∀ q ∈ rules, q.1.eval asg = q.2) :
    c.allEffects asg (b, [pcFromE.eval asg, baseE.eval asg]) = -1 ∧
    c.allEffects asg (b, [pcToE.eval asg, baseE.eval asg + ((d : ℕ) : ZMod p)]) = 1 ∧
    ∀ m : BusMessage p, m.1 = b → m ≠ (b, [pcFromE.eval asg, baseE.eval asg]) →
      m ≠ (b, [pcToE.eval asg, baseE.eval asg + ((d : ℕ) : ZMod p)]) → c.allEffects asg m = 0 := by
  simp only [bridgeCheck] at h
  cases hes : busEntries vs rules b c.busInteractions with
  | none => rw [hes] at h; cases h
  | some es =>
    rw [hes] at h
    match es, h with
    | recvE :: t, h =>
      dsimp only at h
      cases hu : unsnoc t with
      | none => rw [hu] at h; cases h
      | some q =>
        obtain ⟨mid, sendE⟩ := q
        rw [hu] at h
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hmid, hrm⟩, hsm⟩, hrl⟩, hsl⟩, hdist⟩, hpcF⟩, hbase⟩, hpcT⟩, hshift⟩ := h
        obtain ⟨fr0, fr1, hrE⟩ := List.length_eq_two.mp hrl
        obtain ⟨fs0, fs1, hsE⟩ := List.length_eq_two.mp hsl
        rw [hrE] at hpcF hbase
        rw [hsE] at hpcT
        rw [hrE, hsE] at hshift
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at hpcF hbase hpcT hshift
        have hvF := Expression.toLin_eval hrules hpcF
        have hvB := Expression.toLin_eval hrules hbase
        have hvT := Expression.toLin_eval hrules hpcT
        have hsplit : (recvE :: t) = recvE :: (mid ++ [sendE]) := by rw [unsnoc_eq hu]
        have hrp : BusEntry.payloadAt vs recvE asg = [pcFromE.eval asg, baseE.eval asg] := by
          simp [BusEntry.payloadAt, hrE, hvF, hvB]
        have hsp : BusEntry.payloadAt vs sendE asg
            = [pcToE.eval asg, baseE.eval asg + ((d : ℕ) : ZMod p)] := by
          simp [BusEntry.payloadAt, hsE, hvT, hvB, eval_of_linShiftedBy hshift]
        have hne : BusEntry.payloadAt vs recvE asg ≠ BusEntry.payloadAt vs sendE asg :=
          payloadAt_ne_of_distinctAt (vs := vs) (asg := asg) hdist
        have hsum : ∀ m : BusMessage p, m.1 = b →
            c.allEffects asg m
              = (if BusEntry.payloadAt vs recvE asg = m.2 then recvE.1 else 0)
                + (if BusEntry.payloadAt vs sendE asg = m.2 then sendE.1 else 0) := by
          intro m hm
          rw [allEffects_eq_entrySum hrules c b hes m hm, hsplit, List.map_cons,
            List.sum_cons, List.map_append, List.sum_append, List.map_cons, List.map_nil,
            List.sum_cons, List.sum_nil, add_zero, pairsCancel_sum vs asg m.2 mid hmid]
          ring
        refine ⟨?_, ?_, ?_⟩
        · rw [hsum _ rfl, if_pos hrp, if_neg (fun hc => hne (hrp.trans hc.symm)), hrm]
          ring
        · rw [hsum _ rfl, if_neg (fun hc => hne (hc.trans hsp.symm)), if_pos hsp, hsm]
          ring
        · intro m hm hr hs
          rw [hsum m hm,
            if_neg (fun hc => hr (Prod.ext hm (by rw [← hc]; exact hrp))),
            if_neg (fun hc => hs (Prod.ext hm (by rw [← hc]; exact hsp)))]
          ring

--------- The check, with linear pins ---------

/-- **`bridgeCheck`, with linear pins in scope for the normalization.** Otherwise identical:
    receive, cancelling pairs, send, on payloads `[pc, timestamp]`. This is what lets a *fused*
    APC's own bridge check see that a later step's receive timestamp is the same message as the
    previous step's send, when that fact is `from_state__timestamp_{i+1} = from_state__timestamp_i
    + d_i` rather than a literal. -/
def bridgeCheckL (vs : List Variable) (rules : List (PinRule p)) (linRules : List (LinPinRule p))
    (b : ℕ) (c : Circuit p) (d : ℕ) (distPos : ℕ) (pcFromE baseE pcToE : Expression p) : Bool :=
  match busEntriesL vs rules linRules b c.busInteractions with
  | none => false
  | some [] => false
  | some (recvE :: t) =>
    match unsnoc t with
    | none => false
    | some (mid, sendE) =>
      pairsCancel mid
        && (recvE.1 == -1) && (sendE.1 == 1)
        && (recvE.2.length == 2) && (sendE.2.length == 2)
        && payloadDistinctAt recvE.2 sendE.2 distPos
        && (Expression.toLinL vs rules linRules pcFromE == recvE.2[0]?)
        && (Expression.toLinL vs rules linRules baseE == recvE.2[1]?)
        && (Expression.toLinL vs rules linRules pcToE == sendE.2[0]?)
        && (match recvE.2[1]?, sendE.2[1]? with
            | some fr, some fs => linShiftedBy fr fs ((d : ℕ) : ZMod p)
            | _, _ => false)

/-- **Soundness of the bridge check, with linear pins.** As `bridgeCheck_sound`, with the extra
    hypotheses `Expression.toLinL` needs of `linRules`. -/
theorem bridgeCheckL_sound {vs : List Variable} {rules : List (PinRule p)}
    {linRules : List (LinPinRule p)} {b : ℕ}
    {c : Circuit p} {d distPos : ℕ} {pcFromE baseE pcToE : Expression p}
    (h : bridgeCheckL vs rules linRules b c d distPos pcFromE baseE pcToE = true)
    {asg : ChipAssignment p} (hrules : ∀ q ∈ rules, q.1.eval asg = q.2)
    (hlinSized : ∀ q ∈ linRules, q.2.Sized vs.length)
    (hlinRules : ∀ q ∈ linRules, asg q.1 = q.2.eval vs asg) :
    c.allEffects asg (b, [pcFromE.eval asg, baseE.eval asg]) = -1 ∧
    c.allEffects asg (b, [pcToE.eval asg, baseE.eval asg + ((d : ℕ) : ZMod p)]) = 1 ∧
    ∀ m : BusMessage p, m.1 = b → m ≠ (b, [pcFromE.eval asg, baseE.eval asg]) →
      m ≠ (b, [pcToE.eval asg, baseE.eval asg + ((d : ℕ) : ZMod p)]) → c.allEffects asg m = 0 := by
  simp only [bridgeCheckL] at h
  cases hes : busEntriesL vs rules linRules b c.busInteractions with
  | none => rw [hes] at h; cases h
  | some es =>
    rw [hes] at h
    match es, h with
    | recvE :: t, h =>
      dsimp only at h
      cases hu : unsnoc t with
      | none => rw [hu] at h; cases h
      | some q =>
        obtain ⟨mid, sendE⟩ := q
        rw [hu] at h
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hmid, hrm⟩, hsm⟩, hrl⟩, hsl⟩, hdist⟩, hpcF⟩, hbase⟩, hpcT⟩, hshift⟩ := h
        obtain ⟨fr0, fr1, hrE⟩ := List.length_eq_two.mp hrl
        obtain ⟨fs0, fs1, hsE⟩ := List.length_eq_two.mp hsl
        rw [hrE] at hpcF hbase
        rw [hsE] at hpcT
        rw [hrE, hsE] at hshift
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at hpcF hbase hpcT hshift
        have hvF := Expression.toLinL_eval hrules hlinSized hlinRules hpcF
        have hvB := Expression.toLinL_eval hrules hlinSized hlinRules hbase
        have hvT := Expression.toLinL_eval hrules hlinSized hlinRules hpcT
        have hsplit : (recvE :: t) = recvE :: (mid ++ [sendE]) := by rw [unsnoc_eq hu]
        have hrp : BusEntry.payloadAt vs recvE asg = [pcFromE.eval asg, baseE.eval asg] := by
          simp [BusEntry.payloadAt, hrE, hvF, hvB]
        have hsp : BusEntry.payloadAt vs sendE asg
            = [pcToE.eval asg, baseE.eval asg + ((d : ℕ) : ZMod p)] := by
          simp [BusEntry.payloadAt, hsE, hvT, hvB, eval_of_linShiftedBy hshift]
        have hne : BusEntry.payloadAt vs recvE asg ≠ BusEntry.payloadAt vs sendE asg :=
          payloadAt_ne_of_distinctAt (vs := vs) (asg := asg) hdist
        have hsum : ∀ m : BusMessage p, m.1 = b →
            c.allEffects asg m
              = (if BusEntry.payloadAt vs recvE asg = m.2 then recvE.1 else 0)
                + (if BusEntry.payloadAt vs sendE asg = m.2 then sendE.1 else 0) := by
          intro m hm
          rw [allEffects_eq_entrySumL hrules hlinSized hlinRules c b hes m hm, hsplit,
            List.map_cons, List.sum_cons, List.map_append, List.sum_append, List.map_cons,
            List.map_nil, List.sum_cons, List.sum_nil, add_zero, pairsCancel_sum vs asg m.2 mid hmid]
          ring
        refine ⟨?_, ?_, ?_⟩
        · rw [hsum _ rfl, if_pos hrp, if_neg (fun hc => hne (hrp.trans hc.symm)), hrm]
          ring
        · rw [hsum _ rfl, if_neg (fun hc => hne (hc.trans hsp.symm)), if_pos hsp, hsm]
          ring
        · intro m hm hr hs
          rw [hsum m hm,
            if_neg (fun hc => hr (Prod.ext hm (by rw [← hc]; exact hrp))),
            if_neg (fun hc => hs (Prod.ext hm (by rw [← hc]; exact hsp)))]
          ring
