import Itasca.Runtime.Compiler.Body.Reader.Scalar.IntegerFacts
import Itasca.Runtime.Compiler.Body.Reader.Float.FloatFacts
import Itasca.Runtime.Compiler.Body.Reader.Source.SourceOpcodeDescriptors
import Itasca.Runtime.Compiler.Local.Coordinates.NumericSourceCoordinates
import Itasca.Runtime.Compiler.Local.Publication.LoweringMapPublication

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Each numeric visitor event selects a canonical integer or float lowering.
This bridges the event table to publication invariants without a caller-supplied
opcode-subset premise. -/
theorem numeric_hook_publication_dispatch {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : code.OpIterState) (hook : NumericHook) :
    (∃ op : SourceMachine.Numeric.Instruction,
      invoke (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) compiler (.op state (.numeric hook)) =
        runtime.compiler.lower.FunctionCompiler.op ops compiler state (integerOpcode op) 0#u32 0#u32 0#u128) ∨
    (∃ op : SourceMachine.Float.Instruction,
      invoke (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) compiler (.op state (.numeric hook)) =
        runtime.compiler.lower.FunctionCompiler.op ops compiler state (floatOpcode op) 0#u32 0#u32 0#u128) := by
  have range : 69 ≤ hook.opcode.val ∧ hook.opcode.val < 192 := by cases hook <;> decide
  rcases source_numeric_byte_partition hook.opcode range.1 range.2 with integer | floating
  · obtain ⟨op,byte⟩ := integer_opcode_of_mem integer
    have wordBound := integer_opcode_byte op
    have same := congrArg UScalar.val byte
    have base : (integerOpcode op).val < 192 := by scalar_tac
    obtain ⟨operation,actual,_,selected,_,_,_,dispatch,_⟩ := integer_reader_facts ops compiler state op base
    rw [byte,NumericHook.ofOpcode_opcode] at selected
    have equal := Option.some.inj selected
    subst actual
    exact .inl ⟨op,dispatch⟩
  · obtain ⟨op,base,byte⟩ := float_base_opcode_of_mem floating
    obtain ⟨operation,actual,_,selected,_,_,_,dispatch,_⟩ := float_reader_facts ops compiler state op base
    rw [byte,NumericHook.ofOpcode_opcode] at selected
    have equal := Option.some.inj selected
    subst actual
    exact .inr ⟨op,dispatch⟩

/-- All actual numeric visitor callbacks preserve both coordinate and map
publication bounds, independently of the integer/float event classification. -/
theorem compiler_numeric_hook_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : code.OpIterState) (hook : NumericHook)
    (coordinates : SourceCoordinates before) (maps : ControlMapPublication before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (forward : before.next_source.val ≤ state.pos.val)
    (called : invoke (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before (.op state (.numeric hook)) =
      .ok (.Ok (),after)) : SourceCoordinates after ∧ ControlMapPublication after := by
  rcases numeric_hook_publication_dispatch ops before state hook with ⟨op,dispatch⟩ | ⟨op,dispatch⟩
  · rw [dispatch] at called
    exact ⟨compiler_numeric_dispatch_source_coordinates ops law before after state op coordinates inside forward called,
      compiler_numeric_map_publication ops law before after state op called maps forward⟩
  · rw [dispatch] at called
    exact ⟨compiler_float_dispatch_source_coordinates ops law before after state op coordinates inside forward called,
      compiler_float_map_publication ops law before after state op called maps forward⟩

end Itasca.Runtime.Compiler
