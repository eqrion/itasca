import Exec.Code.Local.Capacity.FinishBudgetAvailability
import Exec.Code.Local.Capacity.LiteralAvailability

namespace Exec.Code
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

/-- Scalar literal callbacks charge at most one instruction and retain all
other compiler resource counters, including in dead code. -/
theorem compiler_literal_available_effect {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (kind : ScalarLiteralKind) (bits : U128) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state kind.opcode 0#u32 0#u32 bits
      ⦃ out => out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  by_cases live : compiler.reachable = true
  · have dispatch : runtime.compiler.lower.FunctionCompiler.op ops compiler state kind.opcode 0#u32 0#u32 bits =
        kind.lowering ops compiler state bits := by
      cases kind <;> unfold ScalarLiteralKind.opcode ScalarLiteralKind.lowering runtime.compiler.lower.FunctionCompiler.op <;>
        rw [if_pos live] <;> rfl
    rw [dispatch]
    cases kind <;> simp only [ScalarLiteralKind.lowering,lift,bind_ok]
    all_goals
      apply WP.spec_mono (finish_op_available_budget ops bound available compiler state demand _)
      intro out post
      obtain ⟨used,same,usedEq⟩ := post.2
      rw [same]
      exact ⟨post.1,.of_counter .instructions compiler.budget used 1
        (by simp [ChargeCounter.used]; omega) (by simpa [ChargeCounter.used] using
          (show used.val ≤ compiler.budget.instructions.val+1 by omega))⟩
  · unfold runtime.compiler.lower.FunctionCompiler.op
    rw [if_neg live]
    apply WP.spec_mono (compiler_observe_available_budget ops bound available compiler state demand.operands demand.slots)
    intro out post
    rw [post.2]
    exact ⟨post.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩

/-- The vector-literal emitter changes precisely the instruction counter;
its separate pool reserve is paid by the independent source ledger bound. -/
theorem compiler_vector_literal_available_budget {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound)
    (poolBound : compiler.function.v128_pool.length ≤ compiler.function.code.length) (bits : U128) :
    runtime.compiler.simd.FunctionCompiler.simd_op ops compiler state 524#u16 0#u32 bits
      ⦃ out => out.1 = .Ok () ∧ ∃ used, out.2.budget = {compiler.budget with instructions := used} ∧
        used.val = compiler.budget.instructions.val+1 ⦄ := by
  unfold runtime.compiler.simd.FunctionCompiler.simd_op
  split <;> try contradiction
  step with bounded_index_available (alloc.vec.Vec.len compiler.function.v128_pool) (by
    change compiler.function.v128_pool.length ≤ U32.max
    have room := demand.pc
    omega) as ⟨status,index,accepted,indexEq⟩
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  step with budget_push_available ops bound available compiler.budget compiler.function.v128_pool bits
    (by change compiler.function.v128_pool.length < Usize.max; have cap := demand.codeCapacity; omega)
    (by change compiler.function.v128_pool.length+1 ≤ bound; have room := demand.codeReserve; omega)
    as ⟨status,budget,pool,accepted,same,appended⟩
  subst status budget
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  have fresh : CallbackDemand {compiler with function := {compiler.function with v128_pool := pool}} state bound :=
    ⟨demand.pc,demand.codeCapacity,demand.sourceCapacity,demand.codeReserve,demand.sourceReserve,
      demand.coordinate,demand.instruction,demand.operands,demand.slots⟩
  change runtime.compiler.lower.FunctionCompiler.finish_op ops
    {compiler with function := {compiler.function with v128_pool := pool}} state
    (.ConstV128 compiler.height index) ⦃ out => _ ⦄
  exact finish_op_available_budget ops bound available _ state fresh _

end Exec.Code
