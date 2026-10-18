import Exec.Code.Local.Relations.Table.SignatureTable
/-! Allocation-aware preparation of the defined-function result vector. -/
namespace Exec.Code
open Aeneas Aeneas.Std

@[step] theorem prepare_functions_loop {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (budget : runtime.compiler.Budget A)
    (functions : alloc.vec.Vec (Option runtime.bytecode.CompiledFunction))
    (env : Itasca.module.Env) (index : Usize) (status : core.result.Result Unit Itasca.error.Error)
    (bound : index.val ≤ env.func_type_indices.val.length)
    (initialized : status = .Ok () → functions.val = List.replicate index.val none) :
    runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop2
      ops functions budget env index status ⦃ out =>
      out.2.2 = .Ok () → out.1.val = List.replicate env.func_type_indices.val.length none ⦄ := by
  unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop2
  apply loop.spec_decr_nat (fun p => env.func_type_indices.val.length - p.2.2.1.val)
    (fun p => p.2.2.1.val ≤ env.func_type_indices.val.length ∧
      (p.2.2.2 = .Ok () → p.1.val = List.replicate p.2.2.1.val none))
  · rintro ⟨functions, budget, i, result⟩ ⟨hi, filled⟩
    dsimp only at hi filled
    unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop2.body
    simp only [module.Env.func_type_indices, Itasca.module.Env.impl.func_type_indices, bind_ok]
    split
    · rename_i more
      have hb : i.val < env.func_type_indices.val.length := by
        simp [alloc.vec.Vec.deref, Slice.len] at more; scalar_tac
      cases result with
      | Err error => simp [core.result.Result.is_ok]
      | Ok unit =>
        cases unit
        have initialized := filled rfl
        have capacity := env.func_type_indices.property
        have fits : functions.val.length < Usize.max := by simp [initialized]; omega
        simp only [core.result.Result.is_ok, bind_ok, ite_true]
        step with budget_push ops law budget functions none fits as ⟨status, nextBudget, nextFunctions, pushed⟩
        rcases pushed with ⟨rfl, rfl, appended⟩ | ⟨rfl, rfl, rejected⟩
        · simp only [runtime.compiler.visitor_result, bind_ok]
          step as ⟨next, hnext⟩
          refine ⟨by scalar_tac, ?_, by scalar_tac⟩
          intro _
          rw [appended, initialized, hnext, List.replicate_add]
          simp
        · simp only [runtime.compiler.visitor_result, bind_ok]
          step as ⟨next, hnext⟩
          exact ⟨by scalar_tac, by simp, by scalar_tac⟩
    · rename_i finished
      have same : i.val = env.func_type_indices.val.length := by
        simp [alloc.vec.Vec.deref, Slice.len] at finished; scalar_tac
      simp only [WP.spec_ok]
      intro accepted
      simpa [same] using filled accepted
  · exact ⟨bound, initialized⟩
end Exec.Code
