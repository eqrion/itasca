import Itasca.Runtime.Compiler.Local.Capacity.FinishBudgetAvailability

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Every ordinary opcode on a dead input path only observes the validator
stack. No opcode constructor or live operand layout is needed. -/
theorem compiler_dead_op_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (opcode : U16) (a b : U32) (bits : U128)
    (dead : compiler.reachable ≠ true)
    (request : state.vals.length ≤ bound)
    (slotsFit : compiler.function.local_slots.val+2*state.vals.length ≤ U32.max) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state opcode a b bits ⦃ out =>
      out.1 = .Ok () ∧ out.2.budget = compiler.budget ⦄ := by
  cases compiler with
  | mk signatures params budget batchStart function frames reachable nextSource before height offsets depths =>
    cases reachable with
    | true => exact False.elim (dead rfl)
    | false =>
      let current : runtime.compiler.FunctionCompiler A :=
        ⟨signatures,params,budget,batchStart,function,frames,false,nextSource,before,height,offsets,depths⟩
      change runtime.compiler.FunctionCompiler.observe ops current state ⦃ out =>
        out.1 = .Ok () ∧ out.2.budget = budget ⦄
      exact compiler_observe_available_budget ops bound available current state request slotsFit

end Itasca.Runtime.Code
