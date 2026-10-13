import Itasca.Generated.Funs

/-!
# Literal dispatch simprocs

Simprocs that reduce the extracted opcode dispatchers (`code.step`, `code.step_memory`,
`code.visit_numeric`, `code.visit_memory`, `code.convert_types`, `code.binary_types`) and
scalar-literal pattern matches when the opcode is a concrete literal.
-/

open Lean Meta

namespace Itasca

/-- Reduces a dispatcher, whose opcode argument is at position `opcodePos`, only when the opcode is
a concrete scalar literal. The simplifier's instance transparency does not unfold the scalar
constructors in Aeneas patterns, so this unfolds at full transparency. Kernel reduction supplies
the equality proof, so it adds no assumptions. -/
meta def reduceLiteralDispatch (opcodePos : Nat) : Simp.Simproc := fun e => do
  let args := e.getAppArgs
  if opcodePos ≥ args.size then return .continue
  let opcode := args[opcodePos]!
  let n ← withTransparency .all (whnf (← mkAppM ``Aeneas.Std.UScalar.val #[opcode]))
  let .lit (.natVal _) := n | return .continue
  let some unfolded ← withTransparency .all (unfoldDefinition? e) | return .continue
  let .reduced value ← withTransparency .all (reduceMatcher? unfolded.headBeta) | return .continue
  if value == e then return .continue
  return .visit { expr := value, proof? := some (← mkEqRefl e) }

simproc ↓ reduceConvertTypes (Itasca.code.convert_types _) := reduceLiteralDispatch 0
simproc ↓ reduceBinaryTypes (Itasca.code.binary_types _) := reduceLiteralDispatch 0
simproc ↓ reduceVisitNumeric (Itasca.code.visit_numeric _ _ _ _) := reduceLiteralDispatch 4
simproc ↓ reduceVisitMemory (Itasca.code.visit_memory _ _ _ _ _) := reduceLiteralDispatch 4
simproc ↓ reduceStepMemory (Itasca.code.step_memory _ _ _ _ _ _) := reduceLiteralDispatch 5
simproc ↓ reduceStep (Itasca.code.step _ _ _ _ _ _ _) := reduceLiteralDispatch 6

/-- Reduces a single-discriminant match on a scalar literal, such as a parser dispatching on a
tag. -/
simproc ↓ reduceScalarMatcher (_) := fun e => do
  let .const declName _ := e.getAppFn | return .continue
  let some info := getMatcherInfoCore? (← getEnv) declName | return .continue
  if info.numDiscrs != 1 then return .continue
  let args := e.getAppArgs
  if info.getFirstDiscrPos ≥ args.size then return .continue
  let discr := args[info.getFirstDiscrPos]!
  let ty ← whnf (← inferType discr)
  unless ty.isAppOf ``Aeneas.Std.UScalar do return .continue
  let .reduced value ← withTransparency .all (reduceMatcher? e) | return .continue
  if value == e then return .continue
  return .visit { expr := value, proof? := some (← mkEqRefl e) }

end Itasca
