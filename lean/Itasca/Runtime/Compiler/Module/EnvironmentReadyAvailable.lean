import Itasca.Runtime.Compiler.Local.Capacity.BudgetAvailability
import Itasca.Runtime.Compiler.Local.Relations.Function.Signatures

/-!
Successful compiler environment capture, from signature and function slots through the completed function vector. EnvironmentDemand bounds the requests needed to reach the ready compiler environment.
-/

/-! ## Signature Availability -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Independent source signature width excludes the actual accumulator error. -/
theorem type_slots_available (types : Slice Itasca.types.ValueType)
    (bounded : signatureSlots types.val ≤ U32.max) :
    runtime.compiler.type_slots types ⦃ out =>
      ∃ amount, out = .Ok amount ∧ amount.val = signatureSlots types.val ⦄ := by
  apply WP.spec_mono (compiler_type_slots types)
  intro out counted
  cases out with
  | Ok amount => exact ⟨amount,rfl,counted⟩
  | Err error => omega

/-- Signature capture accepts from independently bounded parameter/result
widths and its actual append demand. -/
theorem capture_signature_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (scheduler : runtime.compiler.CompileScheduler A) (env : Itasca.module.Env) (index : Usize)
    (type : Itasca.types.FuncType) (lookup : env.types.val[index.val]? = some type)
    (parameters : signatureSlots type.params.val ≤ U32.max)
    (results : signatureSlots type.results.val ≤ U32.max)
    (capacity : scheduler.signatures.length < Usize.max)
    (request : scheduler.signatures.length + 1 ≤ bound) :
    runtime.compiler.CompileScheduler.capture_signature ops scheduler env index ⦃ out =>
      out.1 = .Ok () ∧ ∃ signatures signature,
        out.2 = {scheduler with signatures} ∧
        signatures.val = scheduler.signatures.val ++ [signature] ∧
        SignatureMatches signature (type.params.val.map Itasca.Translate.valueType)
          (type.results.val.map Itasca.Translate.valueType) ⦄ := by
  unfold runtime.compiler.CompileScheduler.capture_signature
  simp only [Itasca.module.Env.impl.types,bind_ok]
  have inside := (List.getElem?_eq_some_iff.mp lookup).1
  step as ⟨actual,found⟩
  · simpa [alloc.vec.Vec.deref] using inside
  have same : actual = type := by
    simpa [List.getElem?_eq_getElem inside,alloc.vec.Vec.deref,found] using lookup
  rw [same]
  step with type_slots_available type.params.deref (by simpa [alloc.vec.Vec.deref] using parameters) as ⟨status,params,accepted,paramWords⟩
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  step with type_slots_available type.results.deref (by simpa [alloc.vec.Vec.deref] using results) as ⟨status,returned,accepted,resultWords⟩
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  step with budget_push_available ops bound available scheduler.budget scheduler.signatures
    ⟨alloc.vec.Vec.len type.params,alloc.vec.Vec.len type.results,params,returned⟩ capacity request
    as ⟨status,budget,signatures,accepted,sameBudget,appended⟩
  rw [accepted]
  simp only [runtime.compiler.visitor_result,bind_ok,WP.spec_ok]
  refine ⟨trivial,signatures,_,?_,appended,?_⟩
  · rw [sameBudget]
  · constructor
    · simp [alloc.vec.Vec.len]
    · simp [alloc.vec.Vec.len]
    · simpa [signatureSlots,alloc.vec.Vec.deref] using paramWords
    · simpa [signatureSlots,alloc.vec.Vec.deref] using resultWords

/-- Function-import/definition parameter capture accepts the same independently
bounded source width and append request. -/
theorem capture_func_slots_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (scheduler : runtime.compiler.CompileScheduler A) (env : Itasca.module.Env) (index : Usize)
    (type : Itasca.types.FuncType) (lookup : env.func_types.val[index.val]? = some type)
    (parameters : signatureSlots type.params.val ≤ U32.max)
    (capacity : scheduler.func_param_slots.length < Usize.max)
    (request : scheduler.func_param_slots.length + 1 ≤ bound) :
    runtime.compiler.CompileScheduler.capture_func_slots ops scheduler env index ⦃ out =>
      out.1 = .Ok () ∧ ∃ slots amount,
        out.2 = {scheduler with func_param_slots := slots} ∧
        slots.val = scheduler.func_param_slots.val ++ [amount] ∧
        amount.val = signatureSlots type.params.val ⦄ := by
  unfold runtime.compiler.CompileScheduler.capture_func_slots
  simp only [Itasca.module.Env.impl.func_types,bind_ok]
  have inside := (List.getElem?_eq_some_iff.mp lookup).1
  step as ⟨actual,found⟩
  · simpa [alloc.vec.Vec.deref] using inside
  have same : actual = type := by
    simpa [List.getElem?_eq_getElem inside,alloc.vec.Vec.deref,found] using lookup
  rw [same]
  step with type_slots_available type.params.deref (by simpa [alloc.vec.Vec.deref] using parameters) as ⟨status,amount,accepted,counted⟩
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  step with budget_push_available ops bound available scheduler.budget scheduler.func_param_slots amount capacity request
    as ⟨status,budget,slots,accepted,sameBudget,appended⟩
  rw [accepted]
  simp only [runtime.compiler.visitor_result,bind_ok,WP.spec_ok]
  exact ⟨trivial,slots,amount,by rw [sameBudget],appended,by simpa [alloc.vec.Vec.deref] using counted⟩

end Itasca.Runtime.Code

end

/-! ## Environment Availability -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

abbrev EnvironmentCapture (A : Type) :=
  alloc.vec.Vec runtime.compiler.Signature × alloc.vec.Vec U32 × alloc.vec.Vec Itasca.stream.CodeBatch ×
  alloc.vec.Vec (Option runtime.bytecode.CompiledFunction) × Option Itasca.module.Tail × Usize ×
  runtime.compiler.Budget A × core.result.Result Unit Itasca.error.Error

def captureState {A : Type} (scheduler : runtime.compiler.CompileScheduler A)
    (status : core.result.Result Unit Itasca.error.Error) : EnvironmentCapture A :=
  (scheduler.signatures,scheduler.func_param_slots,scheduler.completed,scheduler.functions,
    scheduler.tail,scheduler.code_start,scheduler.budget,status)

/-- The actual type-capture loop accepts independently bounded source signature
widths and reserve demand for its remaining entries. -/
theorem environment_signatures_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (scheduler : runtime.compiler.CompileScheduler A) (env : Itasca.module.Env) (index : Usize)
    (inside : index.val ≤ env.types.val.length)
    (widths : ∀ type ∈ env.types.val,
      signatureSlots type.params.val ≤ U32.max ∧ signatureSlots type.results.val ≤ U32.max)
    (capacity : scheduler.signatures.length + (env.types.val.length-index.val) ≤ Usize.max)
    (request : scheduler.signatures.length + (env.types.val.length-index.val) ≤ bound) :
    runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop0
      ops scheduler env index (.Ok ()) ⦃ out => ∃ after,
        out = captureState after (.Ok ()) ∧
        after = {scheduler with signatures := after.signatures} ∧
        after.signatures.length = scheduler.signatures.length + (env.types.val.length-index.val) ⦄ := by
  unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop0
  apply loop.spec_decr_nat (fun state => env.types.val.length-state.2.1.val)
    (fun state => state.1 = {scheduler with signatures := state.1.signatures} ∧ state.2.2 = .Ok () ∧
      state.2.1.val ≤ env.types.val.length ∧
      state.1.signatures.length + (env.types.val.length-state.2.1.val) =
        scheduler.signatures.length + (env.types.val.length-index.val))
  · rintro ⟨current,next,status⟩ ⟨same,accepted,position,count⟩
    dsimp only at same accepted position count
    subst status
    unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop0.body
    simp only [Itasca.module.Env.impl.types,bind_ok]
    split
    · rename_i more
      have insideType : next.val < env.types.val.length := by
        simpa [UScalar.lt_equiv,alloc.vec.Vec.deref,Slice.len] using more
      let type := env.types.val[next.val]
      have lookup : env.types.val[next.val]? = some type := List.getElem?_eq_getElem insideType
      obtain ⟨params,results⟩ := widths type (List.getElem_mem insideType)
      simp only [core.result.Result.is_ok,bind_ok,↓reduceIte]
      step with capture_signature_available ops bound available current env next type lookup params results
        (by omega) (by omega) as ⟨status,middle,accepted,signatures,signature,shape,appended,matched⟩
      subst status middle
      step as ⟨following,followingEq⟩
      refine ⟨?_,?_,?_,?_⟩
      · rw [same]
      · clear same; scalar_tac
      · simp only [alloc.vec.Vec.length,appended,List.length_append,List.length_singleton]
        simp only [alloc.vec.Vec.length] at count
        omega
      · clear same; scalar_tac
    · rename_i stopped
      have last : next.val = env.types.val.length := by
        have ended : env.types.val.length ≤ next.val := by
          simpa [UScalar.lt_equiv,alloc.vec.Vec.deref,Slice.len] using stopped
        omega
      exact WP.spec.ret ⟨current,rfl,same,by simpa [last] using count⟩
  · exact ⟨rfl,rfl,inside,rfl⟩

end Itasca.Runtime.Code

end

/-! ## Environment Function Slots Availability -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- The actual function-parameter capture loop accepts independently bounded source parameter
widths and reserve demand for its remaining entries. -/
theorem environment_function_slots_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (scheduler : runtime.compiler.CompileScheduler A) (env : Itasca.module.Env) (index : Usize)
    (inside : index.val ≤ env.func_types.val.length)
    (widths : ∀ type ∈ env.func_types.val,
      signatureSlots type.params.val ≤ U32.max)
    (capacity : scheduler.func_param_slots.length + (env.func_types.val.length-index.val) ≤ Usize.max)
    (request : scheduler.func_param_slots.length + (env.func_types.val.length-index.val) ≤ bound) :
    runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1
      ops scheduler env index (.Ok ()) ⦃ out => ∃ after,
        out = captureState after (.Ok ()) ∧
        after = {scheduler with func_param_slots := after.func_param_slots} ∧
        after.func_param_slots.length = scheduler.func_param_slots.length + (env.func_types.val.length-index.val) ⦄ := by
  unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1
  apply loop.spec_decr_nat (fun state => env.func_types.val.length-state.2.1.val)
    (fun state => state.1 = {scheduler with func_param_slots := state.1.func_param_slots} ∧ state.2.2 = .Ok () ∧
      state.2.1.val ≤ env.func_types.val.length ∧
      state.1.func_param_slots.length + (env.func_types.val.length-state.2.1.val) =
        scheduler.func_param_slots.length + (env.func_types.val.length-index.val))
  · rintro ⟨current,next,status⟩ ⟨same,accepted,position,count⟩
    dsimp only at same accepted position count
    subst status
    unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1.body
    simp only [Itasca.module.Env.impl.func_types,bind_ok]
    split
    · rename_i more
      have insideType : next.val < env.func_types.val.length := by
        simpa [UScalar.lt_equiv,alloc.vec.Vec.deref,Slice.len] using more
      let type := env.func_types.val[next.val]
      have lookup : env.func_types.val[next.val]? = some type := List.getElem?_eq_getElem insideType
      have params := widths type (List.getElem_mem insideType)
      simp only [core.result.Result.is_ok,bind_ok,↓reduceIte]
      step with capture_func_slots_available ops bound available current env next type lookup params
        (by omega) (by omega) as ⟨status,middle,accepted,slots,amount,shape,appended,counted⟩
      subst status middle
      step as ⟨following,followingEq⟩
      refine ⟨?_,?_,?_,?_⟩
      · rw [same]
      · clear same; scalar_tac
      · simp only [alloc.vec.Vec.length,appended,List.length_append,List.length_singleton]
        simp only [alloc.vec.Vec.length] at count
        omega
      · clear same; scalar_tac
    · rename_i stopped
      have last : next.val = env.func_types.val.length := by
        have ended : env.func_types.val.length ≤ next.val := by
          simpa [UScalar.lt_equiv,alloc.vec.Vec.deref,Slice.len] using stopped
        omega
      exact WP.spec.ret ⟨current,rfl,same,by simpa [last] using count⟩
  · exact ⟨rfl,rfl,inside,rfl⟩

end Itasca.Runtime.Code

end

/-! ## Environment Function Vector Availability -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Allocating the defined-function slots accepts under a reserve bound computed
from the remaining source function declarations. The budget is unchanged. -/
theorem environment_function_vector_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (functions : alloc.vec.Vec (Option runtime.bytecode.CompiledFunction))
    (budget : runtime.compiler.Budget A) (env : Itasca.module.Env) (index : Usize)
    (inside : index.val ≤ env.func_type_indices.val.length)
    (capacity : functions.length + (env.func_type_indices.val.length-index.val) ≤ Usize.max)
    (request : functions.length + (env.func_type_indices.val.length-index.val) ≤ bound) :
    runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop2
      ops functions budget env index (.Ok ()) ⦃ out =>
        out.2.2 = .Ok () ∧ out.2.1 = budget ∧
        out.1.length = functions.length + (env.func_type_indices.val.length-index.val) ⦄ := by
  unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop2
  apply loop.spec_decr_nat (fun state => env.func_type_indices.val.length-state.2.2.1.val)
    (fun state => state.2.1 = budget ∧ state.2.2.2 = .Ok () ∧
      state.2.2.1.val ≤ env.func_type_indices.val.length ∧
      state.1.length + (env.func_type_indices.val.length-state.2.2.1.val) =
        functions.length + (env.func_type_indices.val.length-index.val))
  · rintro ⟨current,charged,next,status⟩ ⟨same,accepted,position,count⟩
    dsimp only at same accepted position count
    subst charged status
    unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop2.body
    simp only [Itasca.module.Env.impl.func_type_indices,bind_ok]
    split
    · rename_i more
      have inbounds : next.val < env.func_type_indices.val.length := by
        simpa [UScalar.lt_equiv,alloc.vec.Vec.deref,Slice.len] using more
      simp only [core.result.Result.is_ok,bind_ok,↓reduceIte]
      step with budget_push_available ops bound available budget current none (by change current.length < Usize.max; omega)
        (by change current.length + 1 ≤ bound; omega)
        as ⟨status,charged,after,accepted,same,appended⟩
      subst status charged
      simp only [runtime.compiler.visitor_result,bind_ok]
      step as ⟨following,followingEq⟩
      refine ⟨?_,?_,?_⟩
      · scalar_tac
      · simp only [alloc.vec.Vec.length,appended,List.length_append,List.length_singleton]
        simp only [alloc.vec.Vec.length] at count
        omega
      · scalar_tac
    · rename_i stopped
      have last : next.val = env.func_type_indices.val.length := by
        have ended : env.func_type_indices.val.length ≤ next.val := by
          simpa [UScalar.lt_equiv,alloc.vec.Vec.deref,Slice.len] using stopped
        omega
      exact WP.spec.ret ⟨rfl,rfl,by simpa [last] using count⟩
  · exact ⟨rfl,rfl,inside,rfl⟩

end Itasca.Runtime.Code

end

/-! ## Environment Ready Available -/

section

namespace Itasca.Runtime.Code
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
  simp only [Itasca.module.Env.impl.func_type_indices,Itasca.module.Env.impl.types,bind_ok,if_neg functions,if_neg types]
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

end Itasca.Runtime.Code

end
