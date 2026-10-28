import Itasca.Runtime.Code.Local.Capacity.FinishBudgetAvailability

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

/-- Return accepts from a retained root frame and a source-justified result
width. Dead returns need neither a live root lookup nor result operands. -/
theorem compiler_return_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (body : runtime.compiler.Frame)
    (bodyFrame : compiler.reachable = true → compiler.frames.val[0]? = some body)
    (height : compiler.reachable = true → body.results.val ≤ compiler.height.val) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return ops compiler state ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return
  by_cases live : compiler.reachable = true
  · rw [if_pos live]
    have framesBound : 0 < compiler.frames.length := (List.getElem?_eq_some_iff.mp (bodyFrame live)).1
    step as ⟨frame,hframe⟩
    have same : frame = body := hframe.trans (List.getElem?_eq_some_iff.mp (bodyFrame live)).2
    rw [same]
    have resultFits := height live
    step as ⟨value,hvalue⟩
    cases value with
    | none => simp only at hvalue; omega
    | some source =>
      simp only [core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
      step with compiler_emit_available_frame ops bound available compiler (.Return source body.results)
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
