import Itasca.Runtime.Compiler.Local.Lowering.Emission.Lowering
import Itasca.Runtime.Compiler.Local.Lowering.Literal.LiteralSources
import Itasca.Runtime.Compiler.Local.Lowering.Literal.LiteralCursor
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerLiteralMetadata

/-!
Compiler callbacks for floating-point constants.

Main declarations: `callback_float32_eq` and `callback_float64`. A direct consumer is `Compiler.Body.Reader.Float.ConstantPrefix`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

theorem callback_float32_eq {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState) (value : U32) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_f32_const ops compiler state value =
      runtime.compiler.lower.FunctionCompiler.op ops compiler state 65#u16 0#u32 0#u32 (UScalar.cast .U128 value) := by
  simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_f32_const,lift,bind_ok]
  unfold runtime.compiler.lower.FunctionCompiler.op
  split <;> rfl

theorem callback_float64_eq {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState) (value : U64) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_f64_const ops compiler state value =
      runtime.compiler.lower.FunctionCompiler.op ops compiler state 66#u16 0#u32 0#u32 (UScalar.cast .U128 value) := by
  simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_f64_const,lift,bind_ok]
  unfold runtime.compiler.lower.FunctionCompiler.op
  split <;> rfl

@[step] theorem callback_float32 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (types : List Itasca.wasm_types.ValueType)
    (before : List valtype) (value : U32)
    (layout : CompilerLayout compiler before) (reachable : compiler.reachable = true)
    (concrete : state.vals.val = types.map Itasca.code.StackType.Val)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_f32_const ops compiler state value ⦃ out =>
      out.1 = .Ok () → Lowered compiler out.2
        (.Const32 compiler.height value) (types.map Itasca.Translate.valueType) ⦄ := by
  rw [callback_float32_eq]
  have bits : UScalar.cast .U32 (UScalar.cast .U128 value) =
      value := by
    apply UScalar.eq_of_val_eq
    simp only [UScalar.cast_val_eq]
    scalar_tac
  simpa only [bits] using lower_const32 ops law compiler state types before
    (UScalar.cast .U128 value) layout reachable concrete
    codeFits sourceFits coordinateFits

@[step] theorem callback_float64 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (types : List Itasca.wasm_types.ValueType)
    (before : List valtype) (value : U64)
    (layout : CompilerLayout compiler before) (reachable : compiler.reachable = true)
    (concrete : state.vals.val = types.map Itasca.code.StackType.Val)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_f64_const ops compiler state value ⦃ out =>
      out.1 = .Ok () → Lowered compiler out.2
        (.Const64 compiler.height value) (types.map Itasca.Translate.valueType) ⦄ := by
  rw [callback_float64_eq]
  have bits : UScalar.cast .U64 (UScalar.cast .U128 value) =
      value := by
    apply UScalar.eq_of_val_eq
    simp only [UScalar.cast_val_eq]
    scalar_tac
  simpa only [bits] using lower_const64 ops law compiler state types before
    (UScalar.cast .U128 value) layout reachable concrete
    codeFits sourceFits coordinateFits

end Itasca.Runtime.Compiler
