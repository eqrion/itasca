import Itasca.Runtime.Compiler.Local.Relations.Table.SignatureTable

/-!
Compiler environment preparation, including function-slot capture and the function-vector loop. The final environment-ready sequence is used by complete module assembly.
-/

/-! ## Function Slots -/

section

/-! Exact scheduler capture of argument word counts across the full source function index space. -/
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

@[step] theorem capture_function_slots {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (scheduler : runtime.compiler.CompileScheduler A)
    (env : Itasca.module.Env) (index : Usize) (ty : Itasca.types.FuncType)
    (lookup : env.func_types.val[index.val]? = some ty)
    (fits : scheduler.func_param_slots.val.length < Usize.max) :
    runtime.compiler.CompileScheduler.capture_func_slots ops scheduler env index ⦃ out =>
      out.1 = .Ok () → ∃ word budget,
        out.2 = { scheduler with func_param_slots := out.2.func_param_slots, budget } ∧
        out.2.func_param_slots.val = scheduler.func_param_slots.val ++ [word] ∧
        word.val = signatureSlots ty.params.val ⦄ := by
  unfold runtime.compiler.CompileScheduler.capture_func_slots
  simp only [Itasca.module.Env.impl.func_types, bind_ok]
  have bound := (List.getElem?_eq_some_iff.mp lookup).1
  have inBounds : index.val < env.func_types.deref.length := by simpa [alloc.vec.Vec.deref] using bound
  step as ⟨actual, hactual⟩
  have same : actual = ty := by
    simpa [List.getElem?_eq_getElem bound, alloc.vec.Vec.deref, hactual] using lookup
  rw [same]
  step with compiler_type_slots ty.params.deref as ⟨params, hparams⟩
  cases params with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok paramWords =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with budget_push ops law scheduler.budget scheduler.func_param_slots paramWords fits
      as ⟨status, budget, words, pushed⟩
    rcases pushed with ⟨rfl, rfl, appended⟩ | ⟨rfl, rfl, rejected⟩
    · simp only [runtime.compiler.visitor_result, bind_ok, WP.spec_ok]
      intro accepted
      refine ⟨paramWords, scheduler.budget, rfl, appended, ?_⟩
      simpa [alloc.vec.Vec.deref] using hparams
    · simp [runtime.compiler.visitor_result]

/-- Captured function parameter widths use the source function index space,
which includes imports, and preserve every previously captured type signature. -/
@[step] theorem capture_function_slots_loop {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (scheduler : runtime.compiler.CompileScheduler A)
    (env : Itasca.module.Env) (index : Usize) (status : core.result.Result Unit Itasca.error.Error)
    (bound : index.val ≤ env.func_types.val.length)
    (prefixMatches : status = .Ok () → scheduler.func_param_slots.val.map (fun word => word.val) =
      (env.func_types.val.take index.val).map (fun ty => signatureSlots ty.params.val)) :
    runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1
      ops scheduler env index status ⦃ out =>
      out.2.2.2.2.2.2.2 = .Ok () →
        out.1 = scheduler.signatures ∧ out.2.1.val.map (fun word => word.val) =
          env.func_types.val.map (fun ty => signatureSlots ty.params.val) ∧
        out.2.2.2.1 = scheduler.functions ⦄ := by
  unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1
  apply loop.spec_decr_nat (fun p => env.func_types.val.length - p.2.1.val)
    (fun p => p.2.1.val ≤ env.func_types.val.length ∧
      (p.2.2 = .Ok () → p.1.signatures = scheduler.signatures ∧
        p.1.func_param_slots.val.map (fun word => word.val) =
          (env.func_types.val.take p.2.1.val).map (fun ty => signatureSlots ty.params.val) ∧
        p.1.functions = scheduler.functions))
  · rintro ⟨current, i, result⟩ ⟨hi, certified⟩
    dsimp only at hi certified
    unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1.body
    simp only [Itasca.module.Env.impl.func_types, bind_ok]
    split
    · rename_i more
      have hb : i.val < env.func_types.val.length := by simp [alloc.vec.Vec.deref, Slice.len] at more; scalar_tac
      cases result with
      | Err error => simp [core.result.Result.is_ok]
      | Ok unit =>
        cases unit
        obtain ⟨signaturesEq, currentMatches, sameFunctions⟩ := certified rfl
        have length := congrArg List.length currentMatches
        have capacity := env.func_types.property
        have fits : current.func_param_slots.val.length < Usize.max := by
          simp only [List.length_map, List.length_take, Nat.min_eq_left hi] at length
          omega
        simp only [core.result.Result.is_ok, bind_ok, ite_true]
        step with capture_function_slots ops law current env i env.func_types.val[i.val]
          (List.getElem?_eq_getElem hb) fits as ⟨answer, changed, effect⟩
        step as ⟨next, hnext⟩
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        intro accepted
        obtain ⟨word, budget, changedEq, appended, exactWidth⟩ := effect accepted
        refine ⟨?_, ?_, ?_⟩
        · rw [changedEq]
          exact signaturesEq
        · rw [hnext, ← List.take_concat_get' env.func_types.val i.val hb, appended]
          simp only [List.map_append, List.map_singleton, currentMatches, exactWidth]
        · rw [changedEq]
          exact sameFunctions
    · rename_i finished
      have same : i.val = env.func_types.val.length := by simp [alloc.vec.Vec.deref, Slice.len] at finished; scalar_tac
      simp only [WP.spec_ok]
      intro accepted
      simpa [same] using certified accepted
  · exact ⟨bound, fun accepted => ⟨rfl, prefixMatches accepted, rfl⟩⟩
end Itasca.Runtime.Code

end

/-! ## Prepare Functions -/

section

/-! Allocation-aware preparation of the defined-function result vector. -/
namespace Itasca.Runtime.Code
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
    simp only [Itasca.module.Env.impl.func_type_indices, bind_ok]
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
end Itasca.Runtime.Code

end

/-! ## Environment -/

section

/-! The actual scheduler environment callback constructs source type/signature
metadata and initializes every defined-function result slot. -/
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

@[step] theorem compiler_environment_ready_sequence {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (scheduler : runtime.compiler.CompileScheduler A)
    (env : Itasca.module.Env) (emptyTypes : scheduler.signatures.val = [])
    (emptySlots : scheduler.func_param_slots.val = []) (emptyFunctions : scheduler.functions.val = []) :
    runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready ops scheduler env ⦃ out =>
      ∀ config, out.1 = .Ok config →
        SignatureSequence out.2.signatures.val env.types.val ∧
        out.2.func_param_slots.val.map (fun word => word.val) = env.func_types.val.map (fun ty => signatureSlots ty.params.val) ∧
        out.2.functions.val = List.replicate env.func_type_indices.val.length none ⦄ := by
  unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready
  simp only [Itasca.module.Env.impl.func_type_indices, bind_ok]
  split
  · simp [runtime.compiler.Budget.reject]
  · simp only [Itasca.module.Env.impl.types, bind_ok]
    split
    · simp [runtime.compiler.Budget.reject]
    · step with capture_signatures_loop_frame ops law scheduler env 0#usize (.Ok ())
        (by simp) (by intro _; simp [emptyTypes, SignatureSequence])
        as ⟨signatures, words, completed, functions, tail, codeStart, budget, status, effect⟩
      cases status with
      | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok unit =>
        cases unit
        obtain ⟨sequence, slotsSame, functionsSame⟩ := effect rfl
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, uncurry_apply_pair]
        step with capture_function_slots_loop ops law
          ⟨signatures, words, completed, functions, tail, codeStart, budget⟩ env 0#usize (.Ok ())
          (by simp) (by intro _; simp [slotsSame, emptySlots])
          as ⟨signatures1, words1, completed1, functions1, tail1, codeStart1, budget1, status1, effect1⟩
        cases status1 with
        | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok unit =>
          cases unit
          obtain ⟨sameSignatures, slotsExact, functionsSame1⟩ := effect1 rfl
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, uncurry_apply_pair]
          step with prepare_functions_loop ops law budget1 functions1 env 0#usize (.Ok ())
            (by simp) (by intro _; simp [functionsSame1, functionsSame, emptyFunctions])
            as ⟨functions2, budget2, status2, effect2⟩
          cases status2 with
          | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          | Ok unit =>
            cases unit
            simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, WP.spec_ok]
            intro config accepted
            refine ⟨?_, slotsExact, effect2 rfl⟩
            simpa only [sameSignatures] using sequence

end Itasca.Runtime.Code

end
