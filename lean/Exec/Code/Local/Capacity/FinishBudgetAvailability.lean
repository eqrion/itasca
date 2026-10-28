import Exec.Code.Local.Capacity.EmissionFrameAvailability
import Exec.Code.Local.Capacity.ObserveBudgetAvailability
import Exec.Code.Local.Capacity.CallbackAvailability
import Exec.Code.Local.Capacity.BudgetEffects

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- The actual emission/observation callback tail consumes exactly one
instruction and preserves every other budget counter and marker. -/
theorem finish_op_available_budget {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (instruction : runtime.bytecode.Instr) :
    runtime.compiler.lower.FunctionCompiler.finish_op ops compiler state instruction ⦃ out =>
      out.1 = .Ok () ∧ ∃ used, out.2.budget = {compiler.budget with instructions := used} ∧
        used.val = compiler.budget.instructions.val+1 ⦄ := by
  unfold runtime.compiler.lower.FunctionCompiler.finish_op
  step with compiler_emit_available_frame ops bound available compiler instruction demand.pc demand.codeCapacity
    demand.sourceCapacity demand.codeReserve demand.sourceReserve demand.coordinate demand.instruction
    as ⟨status,emitted,accepted,used,code,sources,shape,usedEq,appended,coordinates⟩
  rw [accepted]
  subst emitted
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  apply WP.spec_mono (compiler_observe_available_budget ops bound available
    {compiler with
      budget := {compiler.budget with instructions := used}
      function := {compiler.function with code,source_offsets := sources}} state demand.operands demand.slots)
  intro out post
  exact ⟨post.1,used,post.2,usedEq⟩

/-- The complete integer numeric family has a source-independent resource
allowance of one instruction; the dead path observes without charging it. -/
theorem compiler_numeric_available_effect {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (front : List valtype) (op : Abs.Numeric.Instruction)
    (layout : compiler.reachable = true →
      CompilerLayout compiler (front ++ List.replicate op.arity (integerType op.input))) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state (integerOpcode op) 0#u32 0#u32 0#u128
      ⦃ out => out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  by_cases live : compiler.reachable = true
  · obtain ⟨left,right,readLeft,readRight,_,_⟩ := numeric_operands ops compiler front op (layout live)
    rw [lower_numeric_eq ops compiler state op left right live readLeft readRight]
    apply WP.spec_mono (finish_op_available_budget ops bound available compiler state demand _)
    intro out post
    obtain ⟨used,same,usedEq⟩ := post.2
    rw [same]
    exact ⟨post.1,.of_counter .instructions compiler.budget used 1 (by simp [ChargeCounter.used]; omega)
      (by simpa [ChargeCounter.used] using (show used.val ≤ compiler.budget.instructions.val+1 by omega))⟩
  · unfold runtime.compiler.lower.FunctionCompiler.op
    rw [if_neg live]
    apply WP.spec_mono (compiler_observe_available_budget ops bound available compiler state demand.operands demand.slots)
    intro out post
    rw [post.2]
    exact ⟨post.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩

/-- Scalar FP and conversion callbacks have the same compile-time resource
effect; floating-point execution behavior is not involved. -/
theorem compiler_float_available_effect {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (front : List valtype) (op : Abs.Float.Instruction)
    (layout : compiler.reachable = true →
      CompilerLayout compiler (front ++ List.replicate op.arity (valtype_numtype op.input))) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state (floatOpcode op) 0#u32 0#u32 0#u128
      ⦃ out => out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  by_cases live : compiler.reachable = true
  · obtain ⟨left,right,readLeft,readRight,_,_⟩ := float_operands ops compiler front op (layout live)
    rw [lower_float_eq ops compiler state op left right live readLeft readRight]
    apply WP.spec_mono (finish_op_available_budget ops bound available compiler state demand _)
    intro out post
    obtain ⟨used,same,usedEq⟩ := post.2
    rw [same]
    exact ⟨post.1,.of_counter .instructions compiler.budget used 1 (by simp [ChargeCounter.used]; omega)
      (by simpa [ChargeCounter.used] using (show used.val ≤ compiler.budget.instructions.val+1 by omega))⟩
  · unfold runtime.compiler.lower.FunctionCompiler.op
    rw [if_neg live]
    apply WP.spec_mono (compiler_observe_available_budget ops bound available compiler state demand.operands demand.slots)
    intro out post
    rw [post.2]
    exact ⟨post.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩

/-- One emitted ordinary instruction has a complete compositional resource
effect; observation adds no charge to any counter. -/
theorem finish_op_available_effect {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (instruction : runtime.bytecode.Instr) :
    runtime.compiler.lower.FunctionCompiler.finish_op ops compiler state instruction ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  apply WP.spec_mono (finish_op_available_budget ops bound available compiler state demand instruction)
  intro out post
  obtain ⟨used,same,usedEq⟩ := post.2
  rw [same]
  exact ⟨post.1,.of_counter .instructions compiler.budget used 1
    (by simp [ChargeCounter.used]; omega) (by simpa [ChargeCounter.used] using
      (show used.val ≤ compiler.budget.instructions.val+1 by omega))⟩

end Itasca.Runtime.Code
