import Itasca.Runtime.Compiler.Local.Lowering.Integer.NumericOpcode
import Itasca.Runtime.Compiler.Body.Reader.Stacks.Values
import Itasca.Runtime.Compiler.Body.Reader.Replay.ProfileAgreement
import Itasca.Runtime.Compiler.Local.Lowering.Integer.LoweringArithmetic
import Itasca.Runtime.Compiler.Local.Relations.Prefix.Prefix
import Itasca.Runtime.Compiler.Local.Relations.Prefix.ResolvedPrefix

/-!
All non-extension integer instructions use the canonical scalar reader and visitor dispatch table, with exactly the descriptor's operand types.

Main declarations: `integer_reader_facts`. A direct consumer is `Compiler.Body.Reader.Acceptance.ReachedNumericAcceptance`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace SourceMachine.Numeric

/-- All non-extension integer instructions use the canonical scalar reader
and visitor dispatch table, with exactly the descriptor's operand types. -/
theorem integer_reader_facts {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : code.OpIterState)
    (op : Instruction) (base : (integerOpcode op).val < 192) :
    ∃ (operation : Numeric.Operation) (hook : NumericHook),
      Numeric.opcodeMeaning (UScalar.cast .U8 (integerOpcode op)) = some operation ∧
      NumericHook.ofOpcode (UScalar.cast .U8 (integerOpcode op)) = some hook ∧
      operation.instruction = op.source ∧
      operation.inputs.map Translate.valueType = List.replicate op.arity (integerType op.input) ∧
      Translate.valueType operation.output = integerType op.output ∧
      invoke (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) compiler (.op state (.numeric hook)) =
        runtime.compiler.lower.FunctionCompiler.op ops compiler state (integerOpcode op) 0#u32 0#u32 0#u128 ∧
      (UScalar.cast .U8 (integerOpcode op)).val ∉ Wasm2.controlOpcodes ∧
      (UScalar.cast .U8 (integerOpcode op)).val ∉ [28, 37, 38, 208, 209, 210, 252, 253] ∧
      Wasm2.NumericExtensions.signMeaning (UScalar.cast .U8 (integerOpcode op)) = none ∧
      UScalar.cast .U8 (integerOpcode op) ≠ code.OP_MISC_PREFIX := by
  cases op with
  | binary ty operator =>
    cases ty <;> cases operator <;> (try (rename_i sign; cases sign)) <;>
      refine ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide, rfl, ?_⟩ <;>
      simp only [global_simps] <;> decide
  | compare ty operator =>
    cases ty <;> cases operator <;> (try (rename_i sign; cases sign)) <;>
      refine ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide, rfl, ?_⟩ <;>
      simp only [global_simps] <;> decide
  | unary ty operator =>
    cases ty <;> cases operator
    all_goals try (norm_num [integerOpcode] at base)
    all_goals
      refine ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide, rfl, ?_⟩
      simp only [global_simps]
      decide
  | eqz ty =>
    cases ty <;>
      refine ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide, rfl, ?_⟩ <;>
      simp only [global_simps] <;> decide
  | conversion operator =>
    cases operator <;>
      refine ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide, rfl, ?_⟩ <;>
      simp only [global_simps] <;> decide
end Itasca.Runtime.Compiler
