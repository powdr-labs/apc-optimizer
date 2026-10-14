import ApcOptimizer.Optimizer
import ApcOptimizer.Implementation.JsonSerializer

set_option autoImplicit false

namespace ReconstructionTests

abbrev F := ZMod 17

def x : Variable := ⟨"x", some 0⟩
def y : Variable := ⟨"y", some 1⟩
def z : Variable := ⟨"z", some 2⟩

def bs : BusSemantics 17 where
  isStateful := fun _ => true
  accepts := fun _ => True
  maintainsInvariants := fun _ => True
  admissible := fun _ => True

instance : DecidablePred bs.accepts := fun _ => isTrue trivial

def eqn (a b : Expression 17) : Expression 17 := .add a (.mul (.const (-1)) b)

def bus (e : Expression 17) : BusInteraction (Expression 17) := ⟨0, .const 1, [e]⟩

def assignments : List Variable → List (Variable → F)
  | [] => [fun _ => 12]
  | v :: vs => (assignments vs).flatMap (fun env =>
      (List.range 17).map (fun n => Function.update env v (n : F)))

def check (ok : Bool) (msg : String) : IO Unit :=
  unless ok do throw (IO.userError msg)

def checkCircuit (name : String) (input : Circuit 17) (mustShrink : Bool) : IO Unit := do
  let (output, _, hints) := simpleOptimizer bs ⟨4, 4⟩ input
  let vars := output.vars.eraseDups
  check (vars.length ≤ 3) s!"{name}: unexpectedly large test output"
  if mustShrink then
    check (vars.length < input.vars.eraseDups.length) s!"{name}: no variables eliminated"
  let mut count := 0
  for env in assignments vars do
    if output.algebraicConstraints.all (fun e => e.eval env == 0) then
      count := count + 1
      let recovered := hints.recover output.vars env
      check (input.algebraicConstraints.all (fun e => e.eval recovered == 0))
        s!"{name}: reconstruction violates an original constraint"
      let messages := input.busInteractions.map (fun b => b.eval recovered) ++
        output.busInteractions.map (fun b => b.eval env)
      for m in messages do
        check (input.sideEffects bs recovered (m.busId, m.payload) ==
          output.sideEffects bs env (m.busId, m.payload)) s!"{name}: side effects changed"
  check (count > 0) s!"{name}: no satisfying output witness exercised"
  IO.println s!"{name}: {count} optimized witnesses reconstructed"

end ReconstructionTests

open ReconstructionTests in
def main : IO Unit := do
  let env : Variable → F := fun v => if v = y then 5 else 12
  let simultaneous : Reconstruction Variable 17 := [[(x, .var y), (y, .const 7)]]
  check (simultaneous.eval env x == 5) "block assignments must be simultaneous"
  let sequential := simultaneous ++ [[(z, .add (.var x) (.var y))]]
  check (sequential.eval env z == 12) "blocks must execute in order"
  check (Reconstruction.recover ([[ (x, .var z) ]] : Reconstruction Variable 17) [y] env x == 0)
    "reconstruction read an unprovided witness value"
  let fresh : Variable := ⟨"fresh", none⟩
  let exported ← IO.ofExcept (Lean.Json.parse (ApcOptimizer.Serialize.serializeResult
    (⟨[.var fresh], []⟩ : Circuit 17) [] 100 [[(x, .var fresh)]]))
  let reconstruction ← IO.ofExcept (exported.getObjVal? "reconstruction")
  let inputs ← IO.ofExcept (reconstruction.getObjVal? "inputs")
  check (inputs == Lean.Json.arr #[Lean.Json.arr #[
    ApcOptimizer.Serialize.reconstructionVariable fresh, Lean.Json.str "fresh@100"]])
    "reconstruction input IDs must match the FFI machine's allocation cursor"
  checkCircuit "linear elimination chain"
    ⟨[eqn (.var x) (.add (.var y) (.const 3)),
      eqn (.var z) (.mul (.const 2) (.var x))], [bus (.var y)]⟩ true
  checkCircuit "disconnected boolean witness"
    ⟨[.mul (.var x) (.add (.var x) (.const (-1)))], [bus (.var y)]⟩ true
  checkCircuit "nonzero preimage with fixed side effect"
    ⟨[.mul (.add (.var x) (.const (-3))) (.add (.var x) (.const 3))],
      [bus (.const 9)]⟩ false
