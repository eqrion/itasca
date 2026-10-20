import Exec.Code.Module.SignatureAvailability

namespace Exec.Code
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
    simp only [module.Env.types,Itasca.module.Env.impl.types,bind_ok]
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

end Exec.Code
