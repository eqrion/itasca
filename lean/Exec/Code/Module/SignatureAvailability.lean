import Exec.Code.Local.Capacity.BudgetAvailability
import Exec.Code.Local.Relations.Common.Signatures

namespace Exec.Code
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
  simp only [module.Env.types,Itasca.module.Env.impl.types,bind_ok]
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
  simp only [module.Env.func_types,Itasca.module.Env.impl.func_types,bind_ok]
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

end Exec.Code
