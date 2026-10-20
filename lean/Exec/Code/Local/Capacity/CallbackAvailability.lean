import Exec.Code.Local.Capacity.EmitAvailability
import Exec.Code.Local.Capacity.ObserveAvailability
import Exec.Code.Local.Lowering.Common.NumericOperands
import Exec.Code.Local.Lowering.Float.FloatOperands

namespace Exec.Code
open Aeneas Aeneas.Std

/-- Numeric demand at a callback boundary. These are independent size,
coordinate, and budget bounds, not callback acceptance or code certificates. -/
structure CallbackDemand {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bound : Nat) : Prop where
  pc : compiler.function.code.length ≤ U32.max
  codeCapacity : compiler.function.code.length < Usize.max
  sourceCapacity : compiler.function.source_offsets.length < Usize.max
  codeReserve : compiler.function.code.length + 1 ≤ bound
  sourceReserve : compiler.function.source_offsets.length + 1 ≤ bound
  coordinate : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max
  instruction : compiler.budget.instructions.val < compiler.budget.limits.max_instructions.val
  operands : state.vals.length ≤ bound
  slots : compiler.function.local_slots.val + 2*state.vals.length ≤ U32.max

/-- Emission followed by rebuilding the actual observed stack accepts under
numeric demand bounds and reserve availability. -/
theorem finish_op_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (instruction : runtime.bytecode.Instr) :
    runtime.compiler.lower.FunctionCompiler.finish_op ops compiler state instruction
      ⦃ out => out.1 = .Ok () ⦄ := by
  unfold runtime.compiler.lower.FunctionCompiler.finish_op
  step with compiler_emit_available ops bound available compiler instruction demand.pc demand.codeCapacity
    demand.sourceCapacity demand.codeReserve demand.sourceReserve demand.coordinate demand.instruction
    as ⟨status,emitted,accepted,shape,used,limits⟩
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  obtain ⟨budget,code,sources,same,_,_⟩ := shape
  have localSlots : emitted.function.local_slots = compiler.function.local_slots := by rw [same]
  exact compiler_observe_available ops bound available emitted state demand.operands
    (by simpa [localSlots] using demand.slots)

/-- All integer numeric callbacks accept with the independently typed live
operand layout; dead callbacks only observe the stack and need no live layout. -/
theorem compiler_numeric_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (front : List valtype) (op : Abs.Numeric.Instruction)
    (layout : compiler.reachable = true →
      CompilerLayout compiler (front ++ List.replicate op.arity (integerType op.input))) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state (integerOpcode op) 0#u32 0#u32 0#u128
      ⦃ out => out.1 = .Ok () ⦄ := by
  by_cases live : compiler.reachable = true
  · obtain ⟨left,right,readLeft,readRight,_,_⟩ := numeric_operands ops compiler front op (layout live)
    rw [lower_numeric_eq ops compiler state op left right live readLeft readRight]
    exact finish_op_available ops bound available compiler state demand _
  · unfold runtime.compiler.lower.FunctionCompiler.op
    rw [if_neg live]
    exact compiler_observe_available ops bound available compiler state demand.operands demand.slots

/-- Scalar floating-point and conversion callbacks use the same independently
bounded emission/observation path. This is compile-time acceptance and adds no
native floating-point assumption. -/
theorem compiler_float_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (front : List valtype) (op : Abs.Float.Instruction)
    (layout : compiler.reachable = true →
      CompilerLayout compiler (front ++ List.replicate op.arity (valtype_numtype op.input))) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state (floatOpcode op) 0#u32 0#u32 0#u128
      ⦃ out => out.1 = .Ok () ⦄ := by
  by_cases live : compiler.reachable = true
  · obtain ⟨left,right,readLeft,readRight,_,_⟩ := float_operands ops compiler front op (layout live)
    rw [lower_float_eq ops compiler state op left right live readLeft readRight]
    exact finish_op_available ops bound available compiler state demand _
  · unfold runtime.compiler.lower.FunctionCompiler.op
    rw [if_neg live]
    exact compiler_observe_available ops bound available compiler state demand.operands demand.slots

end Exec.Code
