import Exec.Code.Module.EnvironmentReadyAvailable
import Exec.Code.Module.CompilerQueueAvailable
import Exec.Code.Local.Relations.Common.Environment
import Exec.Code.Module.EnvironmentFrame

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Fresh environment capture constructs the compiler queue, empty publication
prefix, and initial aggregate budget state from independent numerical demand. -/
theorem compiler_environment_compilation_available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (before : runtime.compiler.CompileScheduler A) (env : module.Env) (bodyBytes localCount : Nat)
    (demand : EnvironmentDemand before env bound)
    (emptyTypes : before.signatures.val = []) (emptySlots : before.func_param_slots.val = [])
    (emptyFunctions : before.functions.val = []) (emptyQueue : before.completed.val = [])
    (origin : before.code_start.val ≤ Itasca.limits.MAX_MODULE_BYTES.val) :
    runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready ops before env
      ⦃ out => out.1 = .Ok ⟨25000#usize,4#usize⟩ ∧
        CompilerQueued env before.budget bodyBytes localCount 0#u64 [] 0 out.2 ∧ out.2.tail = before.tail ⦄ := by
  obtain ⟨⟨reply,after⟩,called,status,budget⟩ := WP.spec_imp_exists
    (environment_ready_available ops bound allocation before env demand)
  dsimp only at status budget
  subst reply
  have facts := compiler_environment_ready_sequence ops law before env emptyTypes emptySlots emptyFunctions
  rw [called,WP.spec_ok] at facts
  obtain ⟨signatures,functionSlots,functions⟩ := facts _ rfl
  have frame := compiler_environment_frame ops before after env ⟨25000#usize,4#usize⟩ called
  have fields : after.completed = before.completed ∧ after.tail = before.tail ∧ after.code_start = before.code_start := by
    simpa only [schedulerFrame,Prod.mk.injEq] using frame
  rw [called,WP.spec_ok]
  refine ⟨rfl,⟨?_,?_⟩,fields.2.1⟩
  · refine ⟨signatures,functionSlots,by simpa only [fields.2.2] using origin,?_,?_⟩
    · refine ⟨by simp only [functions,List.length_replicate],Nat.zero_le _,?_,?_⟩
      · intro index impossible
        omega
      · intro index lower upper
        simp [functions,List.getElem?_replicate,upper]
    · rw [budget]
      simpa only [Nat.zero_mul] using CompilationBudgetEffect.refl before.budget
  · rw [fields.1,emptyQueue]
    exact .nil

end Itasca.Runtime.Code
