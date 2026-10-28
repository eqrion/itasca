import Itasca.Runtime.Code.Module.BatchLoopAvailable
import Itasca.Runtime.Code.Module.CompileSubmit

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Eager submission compiles every independently prepared source entry,
publishes its completed worker, and retains aggregate numerical resource and
source-slot invariants. Queue publication uses bounded allocation availability. -/
theorem compiler_submit_batch_available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (base : runtime.compiler.Budget A) (bodyBytes localCount peak : Nat)
    (before : runtime.compiler.CompileScheduler A) (issued : StreamBatch.Issued)
    (entries : List ModuleBinary.Code)
    (source : PreparedBatchSource issued.code issued.env issued.profile bodyBytes localCount peak
      issued.first_func.val 0#usize entries (Slice.len issued.code))
    (count : entries.length = issued.num_funcs.val) (bounded : issued.Bounded)
    (envelope : FunctionDemandEnvelope base issued.env.func_type_indices.val.length bodyBytes localCount peak bound)
    (paid : CompilationBudgetEffect base before.budget
      (fun counter => issued.first_func.val*functionDemandRate bodyBytes localCount counter))
    (slots : FunctionSlotPrefix issued.env.func_type_indices.val.length issued.first_func.val before.functions.val)
    (bounds : CodeEntry.Bounds issued.env) (environment : Profile.Environment issued.profile issued.env)
    (limits : Profile.EnvironmentWithinLimits issued.env)
    (signatures : SignatureSequence before.signatures.val issued.env.types.val)
    (functionSlots : before.func_param_slots.val.map (fun word => word.val) =
      issued.env.func_types.val.map (fun ty => signatureSlots ty.params.val))
    (origin : before.code_start.val ≤ Itasca.limits.MAX_MODULE_BYTES.val)
    (queueCapacity : before.completed.length < Usize.max) (queueReserve : before.completed.length+1 ≤ bound) :
    runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch ops before issued.seed
      ⦃ out => out.1 = .Ok () ∧
        FunctionSlotPrefix issued.env.func_type_indices.val.length (issued.first_func.val+issued.num_funcs.val) out.2.functions.val ∧
        CompilationBudgetEffect base out.2.budget
          (fun counter => (issued.first_func.val+issued.num_funcs.val)*functionDemandRate bodyBytes localCount counter) ∧
        ∃ worker, out.2.completed.val = before.completed.val++[worker] ∧
          Itasca.stream.CodeBatch.finish worker = .ok (.Ok ()) ⦄ := by
  have arithmetic : before.code_start.val+issued.code_offset.val+issued.code.length ≤ Usize.max := by
    have wordRoom : Itasca.limits.MAX_MODULE_BYTES.val+Itasca.limits.MAX_MODULE_BYTES.val ≤ Usize.max := by
      simp only [Itasca.limits.MAX_MODULE_BYTES]
      scalar_tac
    have coordinates := bounded.2.2
    omega
  obtain ⟨middle,worker,compiled,validated,ended,noError,queue,published,charged⟩ := compiler_batch_loop_available ops law bound allocation
    base bodyBytes localCount peak before issued.seed 0#usize (Slice.len issued.code) entries
    (by simpa only [StreamBatch.Issued.seed,show (0#usize).val = 0 from rfl,Nat.add_zero] using source)
    envelope (by simpa [StreamBatch.Issued.seed] using paid) (by simpa [StreamBatch.Issued.seed] using slots)
    rfl rfl rfl rfl (by simpa [StreamBatch.Issued.seed] using count) bounded.2.1 bounds environment limits signatures functionSlots bounded.2.2 arithmetic
  have run := (submit_loop_accepted ops before middle issued.seed worker 0#usize (.Ok ()) compiled).2
  have identity := (run.reachable .seed).validation.1
  obtain ⟨_,_,_,sameCode,_,_,sameCount,_⟩ := identity
  have finished : Itasca.stream.CodeBatch.finish worker = .ok (.Ok ()) := by
    apply (Itasca.stream.CodeBatch.finish.accepted_iff worker).mpr
    exact ⟨noError,validated.trans sameCount.symm,ended.trans (by rw [sameCode])⟩
  obtain ⟨⟨reply,budget,completed⟩,pushed,status,sameBudget,appended⟩ := WP.spec_imp_exists
    (budget_push_available ops bound allocation middle.budget middle.completed worker
      (by simpa only [queue] using queueCapacity) (by simpa only [queue] using queueReserve))
  dsimp only at status sameBudget appended
  subst reply budget
  unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.submit_code_batch
  rw [compiled]
  simp only [submitPack,bind_ok,uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,pushed,
    runtime.compiler.visitor_result,WP.spec_ok]
  refine ⟨True.intro,published,charged,worker,?_,finished⟩
  rw [appended,queue]

end Itasca.Runtime.Code
