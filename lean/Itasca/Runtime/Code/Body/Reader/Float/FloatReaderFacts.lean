import Itasca.Runtime.Code.Local.Lowering.Float.FloatOpcode
import Itasca.Runtime.Code.Body.Reader.Common.ReaderValues
import Itasca.Runtime.Code.Body.Reader.Common.ReaderProfile
import Itasca.Runtime.Code.Local.Lowering.Common.LoweringArithmetic
import Itasca.Runtime.Code.Local.Relations.Common.Prefix
import Itasca.Runtime.Code.Local.Relations.Common.ResolvedPrefix
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace Abs.Float

/-- All base float instructions use the canonical scalar reader
and visitor dispatch table, with exactly the descriptor's operand types. -/
theorem float_reader_facts {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : code.OpIterState)
    (op : Instruction) (base : (floatOpcode op).val < 256) :
    ∃ (operation : Numeric.Operation) (hook : NumericHook),
      Numeric.opcodeMeaning (UScalar.cast .U8 (floatOpcode op)) = some operation ∧
      NumericHook.ofOpcode (UScalar.cast .U8 (floatOpcode op)) = some hook ∧
      operation.instruction = op.source ∧
      operation.inputs.map Translate.valueType = List.replicate op.arity (valtype_numtype op.input) ∧
      Translate.valueType operation.output = valtype_numtype op.output ∧
      invoke (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) compiler (.op state (.numeric hook)) =
        runtime.compiler.lower.FunctionCompiler.op ops compiler state (floatOpcode op) 0#u32 0#u32 0#u128 ∧
      (UScalar.cast .U8 (floatOpcode op)).val ∉ Wasm2.controlOpcodes ∧
      (UScalar.cast .U8 (floatOpcode op)).val ∉ [28, 37, 38, 208, 209, 210, 252, 253] ∧
      Wasm2.NumericExtensions.signMeaning (UScalar.cast .U8 (floatOpcode op)) = none ∧
      UScalar.cast .U8 (floatOpcode op) ≠ code.OP_MISC_PREFIX := by
  cases op with
  | unary ty operator => cases ty <;> cases operator <;> (first | (solve | norm_num [floatOpcode,Abs.Float.Instruction.opcode,Abs.Float.signIndex] at base) | (refine ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide, rfl, ?_⟩; simp only [global_simps]; decide))
  | binary ty operator => cases ty <;> cases operator <;> (first | (solve | norm_num [floatOpcode,Abs.Float.Instruction.opcode,Abs.Float.signIndex] at base) | (refine ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide, rfl, ?_⟩; simp only [global_simps]; decide))
  | compare ty operator => cases ty <;> cases operator <;> (first | (solve | norm_num [floatOpcode,Abs.Float.Instruction.opcode,Abs.Float.signIndex] at base) | (refine ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide, rfl, ?_⟩; simp only [global_simps]; decide))
  | convert source target sign => cases source <;> cases target <;> cases sign <;> (first | (solve | norm_num [floatOpcode,Abs.Float.Instruction.opcode,Abs.Float.signIndex] at base) | (refine ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide, rfl, ?_⟩; simp only [global_simps]; decide))
  | truncate source target sign saturating => cases source <;> cases target <;> cases sign <;> cases saturating <;> (first | (solve | norm_num [floatOpcode,Abs.Float.Instruction.opcode,Abs.Float.signIndex] at base) | (refine ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide, rfl, ?_⟩; simp only [global_simps]; decide))
  | reinterpretFloat source => cases source <;> (first | (solve | norm_num [floatOpcode,Abs.Float.Instruction.opcode,Abs.Float.signIndex] at base) | (refine ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide, rfl, ?_⟩; simp only [global_simps]; decide))
  | reinterpretInt source => cases source <;> (first | (solve | norm_num [floatOpcode,Abs.Float.Instruction.opcode,Abs.Float.signIndex] at base) | (refine ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide, rfl, ?_⟩; simp only [global_simps]; decide))
  | promote | demote => skip <;> (first | (solve | norm_num [floatOpcode,Abs.Float.Instruction.opcode,Abs.Float.signIndex] at base) | (refine ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide, rfl, ?_⟩; simp only [global_simps]; decide))
end Itasca.Runtime.Code
