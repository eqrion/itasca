import Exec.Code.Local.Coordinates.SourceCoordinateCallbacks
import Exec.Code.Local.Capacity.FinishBudgetAvailability
import Exec.Code.Local.Capacity.MemoryAvailability

namespace Exec.Code
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

/-- Dead ordinary instructions only advance the observed source cursor. -/
theorem compiler_dead_source_coordinates {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (opcode : U16) (a b : U32) (bits : U128)
    (dead : before.reachable = false) (held : SourceCoordinates before)
    (forward : before.next_source.val ≤ state.pos.val)
    (called : runtime.compiler.lower.FunctionCompiler.op ops before state opcode a b bits = .ok (.Ok (),after)) :
    SourceCoordinates after := by
  unfold runtime.compiler.lower.FunctionCompiler.op at called
  rw [if_neg (by simp [dead])] at called
  exact compiler_observe_source_coordinates ops law before after state held forward called

/-- Every integer descriptor uses the checked exact lowering equation to
preserve source coordinates, including the sign-extension instructions. -/
theorem compiler_numeric_source_coordinates {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (front : List valtype) (op : Abs.Numeric.Instruction)
    (layout : before.reachable = true → CompilerLayout before (front ++ List.replicate op.arity (integerType op.input)))
    (held : SourceCoordinates before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (forward : before.next_source.val ≤ state.pos.val)
    (called : runtime.compiler.lower.FunctionCompiler.op ops before state (integerOpcode op) 0#u32 0#u32 0#u128 =
      .ok (.Ok (),after)) : SourceCoordinates after := by
  by_cases live : before.reachable = true
  · obtain ⟨left,right,readLeft,readRight,_,_⟩ := numeric_operands ops before front op (layout live)
    rw [lower_numeric_eq ops before state op left right live readLeft readRight] at called
    exact compiler_finish_op_source_coordinates ops law before after state _ held inside forward called
  · exact compiler_dead_source_coordinates ops law before after state _ _ _ _ (by cases h : before.reachable <;> simp_all)
      held forward called

/-- Scalar floating-point and conversion lowering retain the same coordinate
invariant. No floating-point execution law is involved. -/
theorem compiler_float_source_coordinates {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (front : List valtype) (op : Abs.Float.Instruction)
    (layout : before.reachable = true → CompilerLayout before (front ++ List.replicate op.arity (valtype_numtype op.input)))
    (held : SourceCoordinates before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (forward : before.next_source.val ≤ state.pos.val)
    (called : runtime.compiler.lower.FunctionCompiler.op ops before state (floatOpcode op) 0#u32 0#u32 0#u128 =
      .ok (.Ok (),after)) : SourceCoordinates after := by
  by_cases live : before.reachable = true
  · obtain ⟨left,right,readLeft,readRight,_,_⟩ := float_operands ops before front op (layout live)
    rw [lower_float_eq ops before state op left right live readLeft readRight] at called
    exact compiler_finish_op_source_coordinates ops law before after state _ held inside forward called
  · exact compiler_dead_source_coordinates ops law before after state _ _ _ _ (by cases h : before.reachable <;> simp_all)
      held forward called

/-- All scalar and packed memory loads preserve source coordinates. -/
theorem compiler_memory_load_source_coordinates {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (front : List valtype) (op : Abs.Memory.Load) (offset alignment : U32)
    (layout : before.reachable = true → CompilerLayout before (front ++ [.I32]))
    (held : SourceCoordinates before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (forward : before.next_source.val ≤ state.pos.val)
    (called : runtime.compiler.lower.FunctionCompiler.op ops before state (memoryLoadOpcode op) offset alignment 0#u128 =
      .ok (.Ok (),after)) : SourceCoordinates after := by
  by_cases live : before.reachable = true
  · obtain ⟨address,read,_⟩ := memory_load_operand ops before front (layout live)
    rw [lower_memory_load_eq ops before state op offset alignment address live read] at called
    exact compiler_finish_op_source_coordinates ops law before after state _ held inside forward called
  · exact compiler_dead_source_coordinates ops law before after state _ _ _ _ (by cases h : before.reachable <;> simp_all)
      held forward called

/-- All scalar and packed memory stores preserve source coordinates. -/
theorem compiler_memory_store_source_coordinates {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (front : List valtype) (op : Abs.Memory.Store) (offset alignment : U32)
    (layout : before.reachable = true → CompilerLayout before (front ++ [.I32,valtype_numtype op.type]))
    (held : SourceCoordinates before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (forward : before.next_source.val ≤ state.pos.val)
    (called : runtime.compiler.lower.FunctionCompiler.op ops before state (memoryStoreOpcode op) offset alignment 0#u128 =
      .ok (.Ok (),after)) : SourceCoordinates after := by
  by_cases live : before.reachable = true
  · obtain ⟨address,value,readAddress,readValue,_,_⟩ := memory_store_operands ops before front op.type (layout live)
    rw [lower_memory_store_eq ops before state op offset alignment address value live readAddress readValue] at called
    exact compiler_finish_op_source_coordinates ops law before after state _ held inside forward called
  · exact compiler_dead_source_coordinates ops law before after state _ _ _ _ (by cases h : before.reachable <;> simp_all)
      held forward called

end Exec.Code
