import Exec.Code.Local.Capacity.FinishBudgetAvailability
import Exec.Code.Local.Capacity.AuxiliaryAvailability
import Exec.Code.Local.Relations.Common.StatefulOperands

namespace Exec.Code
open Aeneas Aeneas.Std

/-- Every reference, table, memory-size/growth, and bulk-memory callback
accepts from its source signature and independently bounded storage. Pair
storage is charged only for table.copy and table.init. -/
theorem compiler_stateful_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (C : context)
    (front input output : List valtype) (op : Abs.Stateful.Instruction)
    (signature : Abs.Stateful.Signature C op input output) (a b : U32)
    (layout : compiler.reachable = true → CompilerLayout compiler (front ++ input))
    (pairIndex : statefulUsesPair op = true → compiler.function.indirect.length ≤ U32.max)
    (pairCapacity : statefulUsesPair op = true → compiler.function.indirect.length < Usize.max)
    (pairReserve : statefulUsesPair op = true → compiler.function.indirect.length + 1 ≤ bound) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state (statefulOpcode op) a b 0#u128
      ⦃ out => out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  by_cases live : compiler.reachable = true
  · obtain ⟨first,second,reads,_,_⟩ := stateful_operands ops compiler C front input output op signature (layout live)
    by_cases paired : statefulUsesPair op = true
    · obtain ⟨⟨status,after⟩,actual,index,pairs,accepted,_,frame,_⟩ := WP.spec_imp_exists
        (compiler_pair_available ops bound available compiler a b
          (pairIndex paired) (pairCapacity paired) (pairReserve paired))
      dsimp only at accepted frame
      subst status
      have read : runtime.compiler.FunctionCompiler.operand ops after 3#usize = .ok (.Ok first) := by
        rw [frame]
        have arity : op.arity = 3 := by cases op <;> simp_all [statefulUsesPair,Abs.Stateful.Instruction.arity]
        simpa [StatefulReads,arity,statefulDepth,runtime.compiler.FunctionCompiler.operand] using reads.1
      rw [lower_stateful_pair_eq ops compiler after state op first second a b index live paired actual read]
      have afterDemand : CallbackDemand after state bound := by
        rw [frame]
        exact ⟨demand.pc,demand.codeCapacity,demand.sourceCapacity,demand.codeReserve,
          demand.sourceReserve,demand.coordinate,demand.instruction,demand.operands,demand.slots⟩
      have budget : after.budget = compiler.budget := by rw [frame]
      simpa only [budget] using finish_op_available_effect ops bound available after state afterDemand
        (statefulInstruction op first second a index)
    · have single : statefulUsesPair op = false := Bool.eq_false_iff.mpr paired
      rw [lower_stateful_eq ops compiler state op first second a b 0#u32 live single reads]
      exact finish_op_available_effect ops bound available compiler state demand _
  · unfold runtime.compiler.lower.FunctionCompiler.op
    rw [if_neg live]
    apply WP.spec_mono (compiler_observe_available_budget ops bound available compiler state demand.operands demand.slots)
    intro out post
    rw [post.2]
    exact ⟨post.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩

end Exec.Code
