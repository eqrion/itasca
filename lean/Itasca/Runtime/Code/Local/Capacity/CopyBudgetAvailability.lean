import Itasca.Runtime.Code.Local.Capacity.FinishBudgetAvailability

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Available raw emission retains its exact code frame and consumes one
instruction while preserving every other compiler counter. -/
theorem compiler_emit_available_effect {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (instruction : runtime.bytecode.Instr) :
    runtime.compiler.FunctionCompiler.emit ops compiler instruction ⦃ out =>
      out.1 = .Ok () ∧ Emitted compiler out.2 instruction ∧
      CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  apply WP.spec_mono (compiler_emit_available_frame ops bound available compiler instruction
    demand.pc demand.codeCapacity demand.sourceCapacity demand.codeReserve demand.sourceReserve
    demand.coordinate demand.instruction)
  intro out post
  obtain ⟨used,code,sources,frame,usedEq,appended,recorded⟩ := post.2
  refine ⟨post.1,⟨{compiler.budget with instructions := used},code,sources,frame,appended,recorded⟩,?_⟩
  rw [frame]
  exact .of_counter .instructions compiler.budget used 1
    (by simp [ChargeCounter.used]; omega) (by simp [ChargeCounter.used]; omega)

/-- Every checked transfer accepts, with exact elision or single emission and
at most one instruction charge. This resource frame also applies to branch
transfers before the subsequent jump emission. -/
theorem compiler_copy_available_effect {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (dst src count : U32) :
    runtime.compiler.FunctionCompiler.copy ops compiler dst src count ⦃ out =>
      out.1 = .Ok () ∧ (out.2 = compiler ∨ ∃ instruction, Emitted compiler out.2 instruction) ∧
      CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  unfold runtime.compiler.FunctionCompiler.copy
  split
  · exact WP.spec.ret ⟨rfl,Or.inl rfl,(CompilationBudgetEffect.refl compiler.budget).weaken
      (by intro counter; omega)⟩
  · split
    · exact WP.spec.ret ⟨rfl,Or.inl rfl,(CompilationBudgetEffect.refl compiler.budget).weaken
        (by intro counter; omega)⟩
    · have emit (instruction : runtime.bytecode.Instr) :=
        compiler_emit_available_effect ops bound available compiler state demand instruction
      split <;> simp only [bind_ok]
      all_goals
        apply WP.spec_mono (emit _)
        intro out post
        exact ⟨post.1,Or.inr ⟨_,post.2.1⟩,post.2.2⟩

end Itasca.Runtime.Code
