import Exec.Code.Module.EnvironmentFunctionVectorAvailability

namespace Exec.Code
open Aeneas Aeneas.Std

/-- Independent numerical eligibility of the compiler's environment phase. -/
structure EnvironmentDemand {A : Type} (scheduler : runtime.compiler.CompileScheduler A)
    (env : Itasca.module.Env) (bound : Nat) : Prop where
  functionLimit : env.func_type_indices.length ≤ scheduler.budget.limits.max_functions.val
  typeLimit : env.types.length ≤ scheduler.budget.limits.max_types.val
  signatureWidths : ∀ type ∈ env.types.val,
    signatureSlots type.params.val ≤ U32.max ∧ signatureSlots type.results.val ≤ U32.max
  functionWidths : ∀ type ∈ env.func_types.val, signatureSlots type.params.val ≤ U32.max
  signatureCapacity : scheduler.signatures.length + env.types.length ≤ Usize.max
  signatureReserve : scheduler.signatures.length + env.types.length ≤ bound
  slotCapacity : scheduler.func_param_slots.length + env.func_types.length ≤ Usize.max
  slotReserve : scheduler.func_param_slots.length + env.func_types.length ≤ bound
  functionCapacity : scheduler.functions.length + env.func_type_indices.length ≤ Usize.max
  functionReserve : scheduler.functions.length + env.func_type_indices.length ≤ bound

/-- The actual environment-ready callback accepts from independent source
widths, input limits, and allocation demand. No accepted callback trace is
supplied. All budget counters remain unchanged in this metadata phase. -/
theorem environment_ready_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (scheduler : runtime.compiler.CompileScheduler A) (env : Itasca.module.Env)
    (demand : EnvironmentDemand scheduler env bound) :
    runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready ops scheduler env
      ⦃ out => out.1 = .Ok ⟨25000#usize,4#usize⟩ ∧ out.2.budget = scheduler.budget ⦄ := by
  have functions : ¬ Slice.len (alloc.vec.Vec.deref env.func_type_indices) > scheduler.budget.limits.max_functions := by
    have limit := demand.functionLimit
    simp [Slice.len,alloc.vec.Vec.deref,alloc.vec.Vec.length] at *
    scalar_tac
  have types : ¬ Slice.len (alloc.vec.Vec.deref env.types) > scheduler.budget.limits.max_types := by
    have limit := demand.typeLimit
    simp [Slice.len,alloc.vec.Vec.deref,alloc.vec.Vec.length] at *
    scalar_tac
  unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready
  simp only [module.Env.func_type_indices,Itasca.module.Env.impl.func_type_indices,
    module.Env.types,Itasca.module.Env.impl.types,bind_ok,if_neg functions,if_neg types]
  obtain ⟨captured,actual,first,same,firstShape,firstLength⟩ := WP.spec_imp_exists
    (environment_signatures_available ops bound available scheduler env 0#usize (by simp)
      demand.signatureWidths (by simpa using demand.signatureCapacity) (by simpa using demand.signatureReserve))
  rw [same] at actual
  rw [actual]
  simp only [captureState,bind_ok,uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch]
  have slots : first.func_param_slots = scheduler.func_param_slots :=
    congrArg (fun value => value.func_param_slots) firstShape
  have firstFunctions : first.functions = scheduler.functions := congrArg (fun value => value.functions) firstShape
  have firstBudget : first.budget = scheduler.budget := congrArg (fun value => value.budget) firstShape
  obtain ⟨captured,actual,second,same,secondShape,secondLength⟩ := WP.spec_imp_exists
    (environment_function_slots_available ops bound available first env 0#usize (by simp)
      demand.functionWidths (by simpa [slots] using demand.slotCapacity) (by simpa [slots] using demand.slotReserve))
  rw [same] at actual
  rw [actual]
  simp only [captureState,bind_ok,uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch]
  have secondFunctions : second.functions = scheduler.functions :=
    (congrArg (fun value => value.functions) secondShape).trans firstFunctions
  have secondBudget : second.budget = scheduler.budget :=
    (congrArg (fun value => value.budget) secondShape).trans firstBudget
  step with environment_function_vector_available ops bound available second.functions second.budget env 0#usize
    (by simp) (by simpa [secondFunctions] using demand.functionCapacity)
    (by simpa [secondFunctions] using demand.functionReserve)
    as ⟨functions,budget,status,accepted,sameBudget,length⟩
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,WP.spec_ok]
  exact ⟨trivial,by rw [sameBudget,secondBudget]⟩

end Exec.Code
