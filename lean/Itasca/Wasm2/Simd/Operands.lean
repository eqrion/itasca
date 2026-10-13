import Itasca.Wasm2.FixedOperands
import Itasca.Wasm2.Simd.Tables

/-!
# Operand types of SIMD signatures

Gives the popped and pushed value types of each pure SIMD `Signature` and shows that the
extracted `code.read_simd_signature` equals `readFixed` at those types (`signature_fixed`).
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2.Simd

/-- Operand types popped by a pure SIMD signature, listed from the top of the stack. -/
def Signature.popTypes : Signature → List types.ValueType
  | .unary | .test => [.V128]
  | .binary => [.V128, .V128]
  | .ternary => [.V128, .V128, .V128]
  | .shift => [.I32, .V128]
  | .splatI32 => [.I32]
  | .splatI64 => [.I64]
  | .splatF32 => [.F32]
  | .splatF64 => [.F64]

/-- Result type pushed by a pure SIMD signature. -/
def Signature.output : Signature → types.ValueType
  | .test => .I32
  | _ => .V128

theorem Signature.inputs_pop (sig : Signature) : inputTypes sig.popTypes = sig.inputs := by
  cases sig <;> rfl

theorem Signature.outputs_pop (sig : Signature) : outputTypes (some sig.output) = sig.outputs := by
  cases sig <;> rfl

theorem conversion_fixed (st : code.OpIterState) (input output : types.ValueType) :
    code.read_conversion st input output = readFixed st [input] (some output) := by
  simp only [code.read_conversion, readFixed]
  congr 1
  funext pair
  obtain ⟨res, s⟩ := pair
  cases res <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

theorem binary_fixed (st : code.OpIterState) (input output : types.ValueType) :
    code.read_binary st input output = readFixed st [input, input] (some output) := by
  simp only [code.read_binary, readFixed]
  congr 1
  funext pair
  obtain ⟨res, s⟩ := pair
  cases res <;> simp only [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, bind_ok, Std.uncurry, core.convert.FromSame.from]
  · congr 1
    funext pair
    obtain ⟨res, s⟩ := pair
    cases res <;> simp
  · simp

/-- The extracted SIMD operand checker is the independently normalized fixed checker. -/
theorem signature_fixed (st : code.OpIterState) (sig : Signature) :
    code.read_simd_signature st sig.runtime = readFixed st sig.popTypes (some sig.output) := by
  cases sig <;> simp only [Signature.runtime, Signature.popTypes, Signature.output,
    code.read_simd_signature]
  all_goals first | exact conversion_fixed .. | exact binary_fixed .. | skip
  all_goals simp only [readFixed]
  all_goals congr 1; funext pair; obtain ⟨res, s⟩ := pair
  all_goals cases res <;> simp only [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, bind_ok, Std.uncurry, core.convert.FromSame.from]
  all_goals first | exact conversion_fixed .. | exact binary_fixed .. | simp

end Itasca.Wasm2.Simd
