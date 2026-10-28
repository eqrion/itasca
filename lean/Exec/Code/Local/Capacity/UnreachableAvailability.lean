import Exec.Code.Local.Capacity.FinishBudgetAvailability

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- The actual unreachable callback accepts on live and dead input paths.
It consumes at most one instruction and retains every other budget counter. -/
theorem compiler_on_unreachable_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable ops compiler state ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable
  by_cases live : compiler.reachable = true
  · rw [if_pos live]
    step with compiler_emit_available_frame ops bound available compiler .Unreachable
      demand.pc demand.codeCapacity demand.sourceCapacity demand.codeReserve demand.sourceReserve
      demand.coordinate demand.instruction
      as ⟨status,emitted,accepted,used,code,sources,frame,usedEq,_,_⟩
    rw [accepted]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    have slotsFit : emitted.function.local_slots.val + 2*state.vals.length ≤ U32.max := by
      rw [frame]; exact demand.slots
    apply WP.spec_mono (compiler_observe_available_budget ops bound available {emitted with reachable := false}
      state demand.operands slotsFit)
    intro out post
    rw [post.2]
    have budgetEq : emitted.budget = {compiler.budget with instructions := used} := by rw [frame]
    change out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget emitted.budget _
    rw [budgetEq]
    exact ⟨post.1,.of_counter .instructions compiler.budget used 1
      (by simp [ChargeCounter.used]; omega) (by simp [ChargeCounter.used]; omega)⟩
  · rw [if_neg live]
    apply WP.spec_mono (compiler_observe_available_budget ops bound available compiler
      state demand.operands demand.slots)
    intro out post
    rw [post.2]
    exact ⟨post.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩

end Itasca.Runtime.Code
