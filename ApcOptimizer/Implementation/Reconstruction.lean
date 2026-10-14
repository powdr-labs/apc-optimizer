import ApcOptimizer.Spec

set_option autoImplicit false

variable {p : ℕ} {α β : Type}

def WitnessExpr.subst (f : α → WitnessExpr β p) : WitnessExpr α p → WitnessExpr β p
  | .const c => .const c
  | .var x => f x
  | .add a b => .add (a.subst f) (b.subst f)
  | .mul a b => .mul (a.subst f) (b.subst f)
  | .ifZero c a b => .ifZero (c.subst f) (a.subst f) (b.subst f)

@[simp] theorem WitnessExpr.subst_id (e : WitnessExpr α p) : e.subst WitnessExpr.var = e := by
  induction e <;> simp_all [WitnessExpr.subst]

@[simp] theorem WitnessExpr.eval_subst (e : WitnessExpr α p) (f : α → WitnessExpr β p)
    (env : β → ZMod p) : (e.subst f).eval env = e.eval (fun x => (f x).eval env) := by
  induction e <;> simp_all [WitnessExpr.subst, WitnessExpr.eval]

@[simp] theorem Reconstruction.eval_append [DecidableEq α] (a b : Reconstruction α p)
    (env : α → ZMod p) : (a ++ b).eval env = b.eval (a.eval env) :=
  List.foldl_append

theorem Reconstruction.lookup_map [DecidableEq α] (xs : List α) (f : α → WitnessExpr α p)
    {x : α} (hx : x ∈ xs) : (xs.map (fun x => (x, f x))).lookup x = some (f x) := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
      simp only [List.map_cons, List.lookup_cons]
      by_cases h : x = y
      · subst y; simp
      · simp [BEq.beq, h, ih (List.mem_of_ne_of_mem h hx)]

theorem Reconstruction.eval_block [DecidableEq α] (xs : List α)
    (f : α → WitnessExpr α p) (env : α → ZMod p) {x : α} (hx : x ∈ xs) :
    Reconstruction.eval [xs.map (fun x => (x, f x))] env x = (f x).eval env := by
  simp [Reconstruction.eval, Reconstruction.lookup_map xs f hx]

def WitnessExpr.isCopy [DecidableEq α] (x : α) : WitnessExpr α p → Bool
  | .var y => decide (y = x)
  | _ => false

theorem WitnessExpr.isCopy_eval [DecidableEq α] {x : α} {e : WitnessExpr α p}
    (h : e.isCopy x = true) (env : α → ZMod p) : e.eval env = env x := by
  cases e <;> simp_all [WitnessExpr.isCopy, WitnessExpr.eval]

def Reconstruction.ofMap [DecidableEq α] (xs : List α) (f : α → WitnessExpr α p) :
    Reconstruction α p :=
  [(xs.filter (fun x => !(f x).isCopy x)).map (fun x => (x, f x))]

theorem Reconstruction.ofMap_eval [DecidableEq α] (xs : List α) (f : α → WitnessExpr α p)
    (env : α → ZMod p) {x : α} (hx : x ∈ xs) :
    (Reconstruction.ofMap xs f).eval env x = (f x).eval env := by
  by_cases hc : (f x).isCopy x = true
  · have hn : ((xs.filter (fun x => !(f x).isCopy x)).map (fun x => (x, f x))).lookup x = none := by
      apply List.lookup_eq_none_iff.mpr
      intro pair hp
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hp
      have hxy : x ≠ y := by
        intro h; subst y
        simp [hc] at hy
      simp [hxy]
    simp only [Reconstruction.ofMap, Reconstruction.eval, List.foldl_cons, List.foldl_nil, hn]
    exact (WitnessExpr.isCopy_eval hc env).symm
  · exact Reconstruction.eval_block _ f env (List.mem_filter.mpr ⟨hx, by simpa using hc⟩)

namespace Reconstruction

/-- Materialized values prevent repeated evaluation of earlier assignments. -/
def readValues [DecidableEq α] (values : List (α × ZMod p))
    (env : α → ZMod p) (x : α) : ZMod p :=
  match values.lookup x with
  | some value => value
  | none => env x

def evalValues [DecidableEq α] (hints : Reconstruction α p) (env : α → ZMod p)
    (values : List (α × ZMod p)) : List (α × ZMod p) :=
  hints.foldl (fun values block =>
    block.map (fun (v, e) => (v, e.eval (readValues values env))) ++ values) values

@[inline] def evalEager [DecidableEq α] (hints : Reconstruction α p)
    (env : α → ZMod p) : α → ZMod p :=
  readValues (evalValues hints env []) env

theorem lookup_values [DecidableEq α] (block : List (α × WitnessExpr α p))
    (env : α → ZMod p) (x : α) :
    (block.map (fun (v, e) => (v, e.eval env))).lookup x =
      (block.lookup x).map (fun e => e.eval env) := by
  induction block with
  | nil => rfl
  | cons pair rest ih =>
    obtain ⟨v, e⟩ := pair
    by_cases h : x = v
    · subst v; simp
    · simpa [List.lookup_cons, BEq.beq, h] using ih

theorem evalValues_correct [DecidableEq α] (hints : Reconstruction α p)
    (env : α → ZMod p) (values : List (α × ZMod p)) :
    readValues (evalValues hints env values) env = hints.eval (readValues values env) := by
  induction hints generalizing values with
  | nil => rfl
  | cons block rest ih =>
    simp only [evalValues, List.foldl_cons, eval] at *
    rw [ih]
    congr 1
    funext x
    simp only [readValues, List.lookup_append, lookup_values]
    cases block.lookup x <;> rfl

@[csimp] theorem eval_eq_evalEager : @Reconstruction.eval = @evalEager := by
  funext p α inst hints env
  exact (evalValues_correct hints env []).symm

@[inline] def recoverEager (hints : Reconstruction Variable p) (kept : List Variable)
    (env : Variable → ZMod p) : Variable → ZMod p :=
  evalEager hints (fun v => if v ∈ kept then env v else 0)

@[csimp] theorem recover_eq_recoverEager : @Reconstruction.recover = @recoverEager := by
  funext p hints kept env
  change Reconstruction.eval hints _ = evalEager hints _
  rw [eval_eq_evalEager]

end Reconstruction
