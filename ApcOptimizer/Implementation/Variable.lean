import ApcOptimizer.Spec

set_option autoImplicit false

/-! # Implementation support for structured variables

Typeclass laws and helpers for using spec-level `OutputVariable` values in parsers and hash maps; kept
out of `Spec.lean` to minimize the audited surface. -/

instance : Ord OutputVariable := ⟨fun a b =>
  match compare a.name b.name with
  | .eq => compare a.powdrId? b.powdrId?
  | o => o⟩

instance : Hashable OutputVariable := ⟨fun a => mixHash (hash a.name) (hash a.powdrId?)⟩

instance : Hashable InputVariable := ⟨fun a => mixHash (hash a.name) (hash a.id)⟩

/-- Parse powdr's `<name>@<id>` variable notation. A name without a numeric id fails loudly: powdr
    exports every column with its id (and so does `JsonSerializer`, for the columns passes mint), so
    an id-less name means the input is not what the optimizer's input type describes. -/
def InputVariable.ofPowdrName (raw : String) : Except String InputVariable :=
  match raw.splitOn "@" with
  | [base, id] =>
      match id.toNat? with
      | some n => .ok { name := base, id := n }
      | none => .error s!"variable without a numeric powdr id: {raw}"
  | _ => .error s!"variable without a powdr id: {raw}"

/-- Pinned to `OutputVariable`'s `DecidableEq`, so `LawfulBEq` below holds by `decide`. -/
instance : BEq OutputVariable := ⟨fun a b => decide (a = b)⟩

/-- Lawfulness of the `BEq` above, from which `EquivBEq`/`LawfulHashable` (the hash-map key
    obligations) are inferred. -/
instance : LawfulBEq OutputVariable where
  rfl := by simp [BEq.beq]
  eq_of_beq h := by simpa [BEq.beq] using h

instance : BEq InputVariable := ⟨fun a b => decide (a = b)⟩
