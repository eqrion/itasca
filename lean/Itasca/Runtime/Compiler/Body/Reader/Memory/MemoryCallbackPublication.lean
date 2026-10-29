import Itasca.Runtime.Compiler.Body.Reader.Memory.Instructions
import Itasca.Runtime.Compiler.Body.Reader.Source.SourceOpcodeDescriptors
import Itasca.Runtime.Compiler.Local.Coordinates.NumericSourceCoordinates
import Itasca.Runtime.Compiler.Local.Publication.LoweringMapPublication

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Every memory visitor event preserves source-coordinate and control-map
publication bounds, covering all scalar and packed load/store hooks. -/
theorem compiler_memory_hook_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : code.OpIterState) (hook : MemoryHook) (arg : code.MemArg)
    (coordinates : SourceCoordinates before) (maps : ControlMapPublication before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (forward : before.next_source.val ≤ state.pos.val)
    (called : invoke (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before (.op state (.memory hook arg)) =
      .ok (.Ok (),after)) : SourceCoordinates after ∧ ControlMapPublication after := by
  have range : 40 ≤ hook.opcode.val ∧ hook.opcode.val ≤ 62 := by cases hook <;> decide
  have visited := (MemoryHook.dispatch (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
    before state hook arg).trans called
  rcases source_memory_byte_partition hook.opcode range.1 range.2 with ⟨op,byte⟩ | ⟨op,byte⟩
  · have dispatch := (memory_load_reader_facts ops before state op arg).2.2.2.2.1
    rw [← byte,dispatch] at visited
    exact ⟨compiler_memory_load_dispatch_source_coordinates ops law before after state op arg.offset arg.align
      coordinates inside forward visited,
      compiler_core_map_publication ops law before after state (.load op arg.offset arg.align) visited maps forward⟩
  · have dispatch := (memory_store_reader_facts ops before state op arg).2.2.2.2.1
    rw [← byte,dispatch] at visited
    exact ⟨compiler_memory_store_dispatch_source_coordinates ops law before after state op arg.offset arg.align
      coordinates inside forward visited,
      compiler_core_map_publication ops law before after state (.store op arg.offset arg.align) visited maps forward⟩

end Itasca.Runtime.Code
