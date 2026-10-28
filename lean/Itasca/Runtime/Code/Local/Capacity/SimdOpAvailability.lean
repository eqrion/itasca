import Itasca.Runtime.Code.Local.Capacity.SimdAvailability
import Itasca.Runtime.Code.Local.Capacity.DeadOpAvailability
import Itasca.Runtime.Code.Local.Lowering.Simd.SimdDispatch

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Actual ordinary dispatch for every meaningful nonconstant SIMD opcode
accepts on live and dead paths. The immediate ledger bounds its own reserve. -/
theorem compiler_simd_nonconstant_op_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (C : context)
    (front input output : List valtype) (source : instr)
    (opcode : U16) (sub a b : U32) (bits : U128)
    (number : opcode.val = 512+sub.val) (bounded : sub.val < 256) (nonconstant : sub.val ≠ 12)
    (meaning : SimdImmediateMeaning C sub (simdImmediate sub a bits) input source output)
    (layout : compiler.reachable = true → CompilerLayout compiler (front ++ input))
    (postLength : compiler.reachable = true → state.vals.val.length = (front ++ output).length)
    (operandCapacity : compiler.before.length < Usize.max)
    (tableBound : compiler.function.simd.length ≤ compiler.function.code.length) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state opcode a b bits ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  by_cases live : compiler.reachable = true
  · obtain ⟨out,actual,post⟩ := WP.spec_imp_exists
      (compiler_simd_nonconstant_available ops bound available compiler state demand C front input output source
        opcode sub a bits number bounded nonconstant meaning (layout live) (postLength live) operandCapacity
        (tableBound.trans demand.pc) (tableBound.trans_lt demand.codeCapacity)
        ((Nat.add_le_add_right tableBound 1).trans demand.codeReserve))
    exact WP.exists_imp_spec ⟨out,
      (lower_simd_dispatch ops compiler state opcode a b bits live (by omega) (by omega)).trans actual,post⟩
  · apply WP.spec_mono (compiler_dead_op_available ops bound available compiler state opcode a b bits live
      demand.operands demand.slots)
    intro out post
    rw [post.2]
    exact ⟨post.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩

/-- The actual vector-constant dispatch accepts its bounded pool append and
instruction charge, including dead code where no pool entry is allocated. -/
theorem compiler_simd_constant_op_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (bits : U128)
    (poolBound : compiler.function.v128_pool.length ≤ compiler.function.code.length) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state 524#u16 0#u32 0#u32 bits ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  by_cases live : compiler.reachable = true
  · obtain ⟨out,actual,post⟩ := WP.spec_imp_exists
      (compiler_vector_literal_available_budget ops bound available compiler state demand poolBound bits)
    obtain ⟨used,budgetEq,usedEq⟩ := post.2
    have effect : CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) := by
      rw [budgetEq]
      exact .of_counter .instructions compiler.budget used 1
        (by simp [ChargeCounter.used]; omega) (by simp [ChargeCounter.used]; omega)
    exact WP.exists_imp_spec ⟨out,
      (lower_simd_dispatch ops compiler state 524#u16 0#u32 0#u32 bits live (by decide) (by decide)).trans actual,
      post.1,effect⟩
  · apply WP.spec_mono (compiler_dead_op_available ops bound available compiler state 524#u16 0#u32 0#u32 bits live
      demand.operands demand.slots)
    intro out post
    rw [post.2]
    exact ⟨post.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩

end Itasca.Runtime.Code
