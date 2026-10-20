import Exec.Code.Local.Capacity.CopyBudgetAvailability
import Exec.Code.Local.Relations.Control.BranchSuccessEmit

namespace Exec.Code
open Aeneas Aeneas.Std

/-- Available nonelided transfer retains the exact existing transfer
certificate, with an independent one-instruction budget bound. The accepted
primitive result is derived inside the proof from allocation availability. -/
theorem compiler_transfer_available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (dst src count : U32)
    (nonempty : count ≠ 0#u32) (different : src ≠ dst) :
    runtime.compiler.FunctionCompiler.copy ops compiler dst src count ⦃ out =>
      out.1 = .Ok () ∧ Emitted compiler out.2 (transferInstruction dst src count) ∧
      CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨⟨status,after⟩,actual,accepted,_,effect⟩ := WP.spec_imp_exists
    (compiler_copy_available_effect ops bound available compiler state demand dst src count)
  dsimp only at accepted effect
  subst status
  have shape := compiler_copy_success ops law compiler after dst src count nonempty different actual
  exact WP.exists_imp_spec ⟨(.Ok (),after),actual,rfl,shape,effect⟩

end Exec.Code
