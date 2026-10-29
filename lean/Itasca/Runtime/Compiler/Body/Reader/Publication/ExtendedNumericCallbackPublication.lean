import Itasca.Runtime.Compiler.Body.Reader.Scalar.IntegerFacts
import Itasca.Runtime.Compiler.Body.Reader.Float.FloatFacts
import Itasca.Runtime.Compiler.Body.Reader.Source.SourceOpcodeDescriptors
import Itasca.Runtime.Compiler.Local.Coordinates.NumericSourceCoordinates
import Itasca.Runtime.Compiler.Local.Publication.LoweringMapPublication

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Sign-extension and saturating numeric events select exact descriptors. -/
theorem extended_numeric_hook_publication_dispatch {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : code.OpIterState) (hook : ExtendedNumericHook) :
    (∃ op : Abs.Numeric.Instruction,
      invoke (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) compiler (.op state (.extendedNumeric hook)) =
        runtime.compiler.lower.FunctionCompiler.op ops compiler state (integerOpcode op) 0#u32 0#u32 0#u128) ∨
    (∃ op : Abs.Float.Instruction,
      invoke (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) compiler (.op state (.extendedNumeric hook)) =
        runtime.compiler.lower.FunctionCompiler.op ops compiler state (floatOpcode op) 0#u32 0#u32 0#u128) := by
  cases hook
  · exact .inl ⟨.unary .I32 .extend8,rfl⟩
  · exact .inl ⟨.unary .I32 .extend16,rfl⟩
  · exact .inl ⟨.unary .I64 .extend8,rfl⟩
  · exact .inl ⟨.unary .I64 .extend16,rfl⟩
  · exact .inl ⟨.unary .I64 .extend32,rfl⟩
  · exact .inr ⟨.truncate .F32 .I32 .S true,rfl⟩
  · exact .inr ⟨.truncate .F32 .I32 .U true,rfl⟩
  · exact .inr ⟨.truncate .F64 .I32 .S true,rfl⟩
  · exact .inr ⟨.truncate .F64 .I32 .U true,rfl⟩
  · exact .inr ⟨.truncate .F32 .I64 .S true,rfl⟩
  · exact .inr ⟨.truncate .F32 .I64 .U true,rfl⟩
  · exact .inr ⟨.truncate .F64 .I64 .S true,rfl⟩
  · exact .inr ⟨.truncate .F64 .I64 .U true,rfl⟩

/-- Every sign-extension and saturating callback preserves both publication invariants. -/
theorem compiler_extended_numeric_hook_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : code.OpIterState) (hook : ExtendedNumericHook)
    (coordinates : SourceCoordinates before) (maps : ControlMapPublication before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (forward : before.next_source.val ≤ state.pos.val)
    (called : invoke (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before (.op state (.extendedNumeric hook)) =
      .ok (.Ok (),after)) : SourceCoordinates after ∧ ControlMapPublication after := by
  rcases extended_numeric_hook_publication_dispatch ops before state hook with ⟨op,dispatch⟩ | ⟨op,dispatch⟩
  · rw [dispatch] at called
    exact ⟨compiler_numeric_dispatch_source_coordinates ops law before after state op coordinates inside forward called,
      compiler_numeric_map_publication ops law before after state op called maps forward⟩
  · rw [dispatch] at called
    exact ⟨compiler_float_dispatch_source_coordinates ops law before after state op coordinates inside forward called,
      compiler_float_map_publication ops law before after state op called maps forward⟩

end Itasca.Runtime.Code
