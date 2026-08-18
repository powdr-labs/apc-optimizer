import ApcOptimizer.Implementation.OptimizerPasses.DigitFold
import ApcOptimizer.Implementation.OptimizerPasses.BusPairCancelLive
import ApcOptimizer.Implementation.OptimizerPasses.BusPairCancelCheck

set_option autoImplicit false

/-! # Dense witness/form indices for `busPairCancel`

The per-invocation position indices the acceptance test consults for bound-deriving witnesses
(`denseBuildBoundIdx`/`denseDropWits`) and range-checked-form witnesses
(`denseBuildFormIdx`/`denseDropFormBasis`), plus the `_mem` layer proving every returned witness is a
live interaction other than the dropped pair (the `hwits`/`hfwits` shape `denseCheckCancel_sound`
takes).

The builders are **untrusted**: a stale or wrong entry costs time, never soundness, because the
lookups re-check at every use that the position is in range, still live, distinct from the pair, and
(for the bound witness) still derives a `denseInteractionBound`. -/

namespace ApcOptimizer.Dense

variable {p : ℕ}

def denseInteractionBoundPatImpl (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (mval? : Option (ZMod p))
    (pat : List (Option (ZMod p))) (i : VarId) : Option Nat :=
  match mval? with
  | none => none
  | some mval =>
    if zmodIsZero mval then none
    else
      match denseVarSlot i bi.payload with
      | none => none
      | some slot => facts.slotBound bi.busId mval pat slot

/-- `denseInteractionBound` with the multiplicity constant and constant-payload pattern hoisted out
    of the caller's per-payload-variable loop (they are per-interaction values). Definitionally the
    same function at the canonical arguments (`denseInteractionBoundPat_eq`). -/
def denseInteractionBoundPat (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (mval? : Option (ZMod p))
    (pat : List (Option (ZMod p))) (i : VarId) : Option Nat :=
  match mval? with
  | none => none
  | some mval =>
    if mval = 0 then none
    else
      match denseVarSlot i bi.payload with
      | none => none
      | some slot => facts.slotBound bi.busId mval pat slot

@[csimp] theorem denseInteractionBoundPat_eq_impl :
    @denseInteractionBoundPat = @denseInteractionBoundPatImpl := by
  funext q bs facts bi m pat i
  simp [denseInteractionBoundPat, denseInteractionBoundPatImpl]

def denseBuildBoundStep (bs : BusSemantics p) (facts : BusFacts p bs)
    (bi : BusInteraction (DenseExpr p)) (k : Nat) (m : Array (List Nat)) : Array (List Nat) :=
  match bi.multiplicity.constValue? with
  | none => m
  | some mval =>
    if zmodIsZero mval then m
    else
      let pat := bi.payload.map DenseExpr.constValue?
      bi.payload.foldl (fun m e =>
        match e with
        | .var v =>
          -- skip repeated occurrences of the same variable within one payload
          if ((m[v.index]?).getD []).head? = some k then m
          else
            match denseInteractionBoundPat bs facts bi (some mval) pat v with
            | some _ => m.modify v.index (k :: ·)
            | none => m
        | _ => m) m

def denseBuildBoundGo (bs : BusSemantics p) (facts : BusFacts p bs)
    (arr : Array (BusInteraction (DenseExpr p))) : Nat → Array (List Nat) → Array (List Nat)
  | 0, m => m
  | n + 1, m =>
    denseBuildBoundGo bs facts arr n
      (match arr[n]? with
       | none => m
       | some bi => denseBuildBoundStep bs facts bi n m)

/-- Candidate positions of bound-deriving interactions, per variable (ascending), built once per
    invocation. Untrusted — `denseDropWitsIdxGo` re-checks liveness, the dropped pair, and the bound
    at every use. -/
def denseBuildBoundIdx (bs : BusSemantics p) (facts : BusFacts p bs) (nvars : Nat)
    (arr : Array (BusInteraction (DenseExpr p))) : Array (List Nat) :=
  denseBuildBoundGo bs facts arr arr.size (Array.replicate nvars [])

/-- The scan behind `denseDropWits`: the first of `v`'s indexed candidate positions (ascending,
    skipping dead entries and the dropped pair) that still derives a `denseInteractionBound` for
    `v`. -/
def denseDropWitsIdxGo {bs : BusSemantics p} (facts : BusFacts p bs)
    (arr : Array (BusInteraction (DenseExpr p))) (alive : Array Bool)
    (S R : BusInteraction (DenseExpr p))
    (v : VarId) : List Nat → Option (BusInteraction (DenseExpr p))
  | [] => none
  | k :: ks =>
    if h : k < arr.size then
      if alive[k]?.getD false && !decide (arr[k] = S) && !decide (arr[k] = R) then
        match denseInteractionBound bs facts arr[k] v with
        | some _ => some arr[k]
        | none => denseDropWitsIdxGo facts arr alive S R v ks
      else denseDropWitsIdxGo facts arr alive S R v ks
    else denseDropWitsIdxGo facts arr alive S R v ks

/-- First interaction of a plain list deriving a `denseInteractionBound` for `v` — used to consult
    the emitted byte checks `checksOld`, which live outside the stable array. -/
def denseFirstBoundIn {bs : BusSemantics p} (facts : BusFacts p bs) (v : VarId) :
    List (BusInteraction (DenseExpr p)) → Option (BusInteraction (DenseExpr p))
  | [] => none
  | bi :: rest =>
    match denseInteractionBound bs facts bi v with
    | some _ => some bi
    | none => denseFirstBoundIn facts v rest

/-- The witness lookup for a candidate drop: the first bound-deriving interaction other than the
    dropped pair — first among the live stable-array entries (via `bidx`), then among the
    previously-emitted checks `checksOld` — followed by this drop's emitted checks. -/
def denseDropWits {bs : BusSemantics p} (facts : BusFacts p bs)
    (bidx : Array (List Nat))
    (arr : Array (BusInteraction (DenseExpr p))) (alive : Array Bool)
    (S R : BusInteraction (DenseExpr p))
    (checksOld emitted : List (BusInteraction (DenseExpr p))) (v : VarId) :
    List (BusInteraction (DenseExpr p)) :=
  match denseDropWitsIdxGo facts arr alive S R v ((bidx[v.index]?).getD []) with
  | some bi => bi :: emitted
  | none =>
    match denseFirstBoundIn facts v checksOld with
    | some bi => bi :: emitted
    | none => emitted

def denseBuildFormStep (bs : BusSemantics p) (bi : BusInteraction (DenseExpr p)) (k : Nat)
    (m : Array (List Nat)) : Array (List Nat) :=
  if bs.isStateful bi.busId then m
  else
    bi.payload.foldl (fun m e =>
      if e.isSingleVar then m
      else
        e.vars.dedup.foldl (fun m v =>
          let cur := (m[v.index]?).getD []
          if cur.length < 4 then m.modify v.index (k :: ·) else m) m) m

def denseBuildFormGo (bs : BusSemantics p) (arr : Array (BusInteraction (DenseExpr p)))
    (n : Nat) (m : Array (List Nat)) : Array (List Nat) :=
  if h : n < arr.size then
    denseBuildFormGo bs arr (n + 1) (denseBuildFormStep bs arr[n] n m)
  else m
  termination_by arr.size - n

/-- Candidate positions for range-checked forms, per variable: interactions on a *stateless* bus
    carrying a compound payload slot mentioning the variable, at most four per variable. Untrusted —
    `denseDropFormBasis` re-checks liveness and the dropped pair at every use. -/
def denseBuildFormIdx (bs : BusSemantics p) (nvars : Nat)
    (arr : Array (BusInteraction (DenseExpr p))) : Array (List Nat) :=
  denseBuildFormGo bs arr 0 (Array.replicate nvars [])

/-- One lazily-derived checked-form record per position, shared across every candidate and every
    node of every basis reduction of this invocation. `denseFormBoundAt` is a pure function of
    `(interaction, slot)`, and the reduction re-asked for it at every node of its fuel-bounded DFS —
    this is the memo that removes that. Forced only at the positions a query reaches. -/
def denseBuildFormBounds (bs : BusSemantics p) (facts : BusFacts p bs)
    (arr : Array (BusInteraction (DenseExpr p))) :
    Array (Thunk (List (DenseLinExpr p × Nat))) :=
  arr.map (fun bi => Thunk.mk (fun _ => denseFormBoundsOf facts bi))

/-- The basis channel for a candidate drop: the prepared checked forms of `v`'s indexed positions,
    under the live / distinct-from-the-pair gate the reduction's soundness needs. -/
def denseDropFormBasis (fidx : Array (List Nat))
    (fbnd : Array (Thunk (List (DenseLinExpr p × Nat))))
    (arr : Array (BusInteraction (DenseExpr p))) (alive : Array Bool)
    (S R : BusInteraction (DenseExpr p)) (v : VarId) : List (DenseLinExpr p × Nat) :=
  ((fidx[v.index]?).getD []).flatMap (fun k =>
    if h : k < arr.size then
      if alive[k]?.getD false && !decide (arr[k] = S) && !decide (arr[k] = R) then
        (fbnd[k]?).elim [] Thunk.get
      else []
    else [])

/-- `denseDropFormBasis` extended with the emitted byte checks' own payload forms (this drop's and
    earlier drops'): a check's slot is `slotBound`-bounded like any other interaction's, which is
    what lets a check emitted for an *expression* slot justify that slot in the basis reduction —
    the variable-level witness channel (`denseDropWits`) only ever bounds whole variables. -/
def denseDropFormBasisE {bs : BusSemantics p} (facts : BusFacts p bs) (fidx : Array (List Nat))
    (fbnd : Array (Thunk (List (DenseLinExpr p × Nat))))
    (arr : Array (BusInteraction (DenseExpr p))) (alive : Array Bool)
    (S R : BusInteraction (DenseExpr p))
    (checksOld emitted : List (BusInteraction (DenseExpr p))) (v : VarId) :
    List (DenseLinExpr p × Nat) :=
  denseDropFormBasis fidx fbnd arr alive S R v
    ++ (checksOld ++ emitted).flatMap (denseFormBoundsOf facts)

/-! ### The `_mem` proof layer

Every returned witness is a live interaction at a position `≠ S`/`≠ R`, mapped into
`A ++ B ++ C ++ emitted` — the `hwits`/`hfwits` hypotheses `denseCheckCancel_sound` consumes. -/

/-- Every witness the indexed scan returns is a live entry other than the dropped pair. -/
theorem denseDropWitsIdxGo_mem {bs : BusSemantics p} (facts : BusFacts p bs)
    (arr : Array (BusInteraction (DenseExpr p))) (alive : Array Bool)
    (S R : BusInteraction (DenseExpr p))
    (v : VarId) :
    ∀ (ks : List Nat) {bi : BusInteraction (DenseExpr p)},
      denseDropWitsIdxGo facts arr alive S R v ks = some bi →
      bi ∈ denseLiveSeg arr alive 0 arr.size ∧ bi ≠ S ∧ bi ≠ R := by
  intro ks
  induction ks with
  | nil =>
    intro bi h
    exact absurd h (by simp [denseDropWitsIdxGo])
  | cons k rest ih =>
    intro bi h
    rw [denseDropWitsIdxGo] at h
    split_ifs at h with hk hcond
    ·
      revert h
      cases hb : denseInteractionBound bs facts arr[k] v with
      | some b =>
        intro h
        obtain rfl := Option.some.inj h
        rw [Bool.and_eq_true, Bool.and_eq_true] at hcond
        obtain ⟨⟨hal, hnS⟩, hnR⟩ := hcond
        refine ⟨denseLiveSeg_mem arr alive 0 arr.size k arr[k] (Nat.zero_le _) (by omega) hal
            (Array.getElem?_eq_getElem hk), ?_, ?_⟩
        · exact fun he => by simp [he] at hnS
        · exact fun he => by simp [he] at hnR
      | none =>
        intro h
        exact ih h
    · exact ih h
    · exact ih h

/-- Every interaction `denseFirstBoundIn` returns is a member of the scanned list. -/
theorem denseFirstBoundIn_mem {bs : BusSemantics p} (facts : BusFacts p bs) (v : VarId) :
    ∀ (l : List (BusInteraction (DenseExpr p))) {bi : BusInteraction (DenseExpr p)},
      denseFirstBoundIn facts v l = some bi → bi ∈ l := by
  intro l
  induction l with
  | nil => intro bi h; simp [denseFirstBoundIn] at h
  | cons hd tl ih =>
    intro bi h
    rw [denseFirstBoundIn] at h
    cases hb : denseInteractionBound bs facts hd v with
    | some b => rw [hb] at h; obtain rfl := Option.some.inj h; exact List.mem_cons.2 (Or.inl rfl)
    | none => rw [hb] at h; exact List.mem_cons_of_mem _ (ih h)

/-- Every witness the lookup returns is in the remaining region, given that the live stable-array
    entries other than the dropped pair are in `A ++ B ++ C`, and so are the previously-emitted
    checks `checksOld`. -/
theorem denseDropWits_mem {bs : BusSemantics p} (facts : BusFacts p bs)
    (bidx : Array (List Nat))
    (arr : Array (BusInteraction (DenseExpr p))) (alive : Array Bool)
    (S R : BusInteraction (DenseExpr p))
    (checksOld emitted : List (BusInteraction (DenseExpr p)))
    {A B C : List (BusInteraction (DenseExpr p))}
    (horig : ∀ bi ∈ denseLiveSeg arr alive 0 arr.size, bi ≠ S → bi ≠ R → bi ∈ A ++ B ++ C)
    (hchecks : ∀ bi ∈ checksOld, bi ∈ A ++ B ++ C) :
    ∀ v, ∀ bi ∈ denseDropWits facts bidx arr alive S R checksOld emitted v,
      bi ∈ A ++ B ++ C ++ emitted := by
  intro v bi hbi
  unfold denseDropWits at hbi
  cases hgo : denseDropWitsIdxGo facts arr alive S R v ((bidx[v.index]?).getD []) with
  | some bi' =>
    rw [hgo] at hbi
    rcases List.mem_cons.1 hbi with rfl | hbi
    · obtain ⟨hmem, hne1, hne2⟩ := denseDropWitsIdxGo_mem facts arr alive S R v _ hgo
      exact List.mem_append_left _ (horig bi hmem hne1 hne2)
    · exact List.mem_append_right _ hbi
  | none =>
    rw [hgo] at hbi
    cases hfb : denseFirstBoundIn facts v checksOld with
    | some bi' =>
      rw [hfb] at hbi
      rcases List.mem_cons.1 hbi with rfl | hbi
      · exact List.mem_append_left _ (hchecks bi (denseFirstBoundIn_mem facts v checksOld hfb))
      · exact List.mem_append_right _ hbi
    | none =>
      rw [hfb] at hbi
      exact List.mem_append_right _ hbi

end ApcOptimizer.Dense
