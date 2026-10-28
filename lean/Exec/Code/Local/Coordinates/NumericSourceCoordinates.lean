import Exec.Code.Local.Coordinates.OrdinarySourceCoordinates
import Exec.Code.Local.Coordinates.SourceCoordinateTactic

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

/-- Actual numeric lowering preserves source coordinates through
its checked descriptor dispatch, independently of source operand typing. -/
theorem compiler_numeric_dispatch_source_coordinates {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (op : Abs.Numeric.Instruction)
    (held : SourceCoordinates before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (forward : before.next_source.val ≤ state.pos.val)
    (called : runtime.compiler.lower.FunctionCompiler.op ops before state (integerOpcode op) 0#u32 0#u32 0#u128 =
      .ok (.Ok (),after)) : SourceCoordinates after := by
  by_cases live : before.reachable = true
  · rw [lower_numeric_dispatch ops before state op live] at called
    unfold numericLowering at called
    repeat' coordinates_step called using ops, law
  · exact compiler_dead_source_coordinates ops law before after state _ _ _ _
      (by cases h : before.reachable <;> simp_all) held forward called

/-- Actual float lowering preserves source coordinates through
its checked descriptor dispatch, independently of source operand typing. -/
theorem compiler_float_dispatch_source_coordinates {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (op : Abs.Float.Instruction)
    (held : SourceCoordinates before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (forward : before.next_source.val ≤ state.pos.val)
    (called : runtime.compiler.lower.FunctionCompiler.op ops before state (floatOpcode op) 0#u32 0#u32 0#u128 =
      .ok (.Ok (),after)) : SourceCoordinates after := by
  by_cases live : before.reachable = true
  · rw [lower_float_dispatch ops before state op live] at called
    unfold floatLowering at called
    repeat' coordinates_step called using ops, law
  · exact compiler_dead_source_coordinates ops law before after state _ _ _ _
      (by cases h : before.reachable <;> simp_all) held forward called

/-- Actual memory load lowering preserves source coordinates through
its checked descriptor dispatch, independently of source operand typing. -/
theorem compiler_memory_load_dispatch_source_coordinates {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (op : Abs.Memory.Load) (offset alignment : U32)
    (held : SourceCoordinates before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (forward : before.next_source.val ≤ state.pos.val)
    (called : runtime.compiler.lower.FunctionCompiler.op ops before state (memoryLoadOpcode op) offset alignment 0#u128 =
      .ok (.Ok (),after)) : SourceCoordinates after := by
  by_cases live : before.reachable = true
  · rw [lower_memory_load_dispatch ops before state op offset alignment live] at called
    unfold memoryLoadLowering at called
    repeat' coordinates_step called using ops, law
  · exact compiler_dead_source_coordinates ops law before after state _ _ _ _
      (by cases h : before.reachable <;> simp_all) held forward called

/-- Actual memory store lowering preserves source coordinates through
its checked descriptor dispatch, independently of source operand typing. -/
theorem compiler_memory_store_dispatch_source_coordinates {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (op : Abs.Memory.Store) (offset alignment : U32)
    (held : SourceCoordinates before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (forward : before.next_source.val ≤ state.pos.val)
    (called : runtime.compiler.lower.FunctionCompiler.op ops before state (memoryStoreOpcode op) offset alignment 0#u128 =
      .ok (.Ok (),after)) : SourceCoordinates after := by
  by_cases live : before.reachable = true
  · rw [lower_memory_store_dispatch ops before state op offset alignment live] at called
    unfold memoryStoreLowering at called
    repeat' coordinates_step called using ops, law
  · exact compiler_dead_source_coordinates ops law before after state _ _ _ _
      (by cases h : before.reachable <;> simp_all) held forward called

end Itasca.Runtime.Code
