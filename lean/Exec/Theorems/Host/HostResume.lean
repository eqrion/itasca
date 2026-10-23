import Exec.Theorems.Host.HostResultCheck
import Exec.Interp.Host.HostResume

namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- Successful host checks produce exactly the encoded results; rejected
results and explicit host errors retain the callback's store in an atomic host
source transition. Stack exhaustion records that completed callback as a trap. -/
theorem host_resume_source {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (before after : runtime.store.Store M) (ambient : frame)
    (exec : runtime.interp.Execution) (address : runtime.FuncAddr) (base : Usize)
    (function : runtime.store.FuncInst) (signature : Itasca.types.FuncType)
    (identity : Nat) (params : List valtype) (args : List val)
    (results : alloc.vec.Vec runtime.Value)
    (status : core.result.Result Unit runtime.platform.HostError)
    (host : HostFunction (Store.decodeStore view code before) address.index.val identity
      params (signature.results.val.map sourceType))
    (arguments : ResultsTyped (Store.decodeStore view code before) params args)
    (extension : Extend_store (Store.decodeStore view code before) (Store.decodeStore view code after))
    (sourceTyped : Store_ok (Store.decodeStore view code after))
    (wfAmbient : wf_frame ambient)
    (functionAt : after.funcs.val[address.index.val]? = some function)
    (signatureAt : after.types.val[function.signature.val]? = some signature)
    (issued : ∀ value ∈ results.val, Store.IssuedValue after value)
    (capacity : base.val + Code.slots (signature.results.val.map sourceType) ≤ exec.slots.length) :
    hostResume memory exec after address base results status ⦃ out =>
      out.2.host_args = exec.host_args ∧ out.2.host_results = results ∧
      out.2.frames = exec.frames ∧ out.2.store = exec.store ∧
      ((out.1 = .Ok () ∧
        StepH ⟨⟨Store.decodeStore view code before,ambient⟩,vals args ++ [.CALL_ADDR address.index.val]⟩
          [.call address.index.val args (some (results.val.map sourceValue))]
          ⟨⟨Store.decodeStore view code after,ambient⟩,vals (results.val.map sourceValue)⟩ ∧
        ResultsTyped (Store.decodeStore view code after) (signature.results.val.map sourceType)
          (results.val.map sourceValue) ∧
        ValuesAt out.2.slots.val base.val (results.val.map sourceValue) ∧
        out.2.slots.length = exec.slots.length ∧
        (∀ j, j < base.val ∨ base.val + Code.slots (signature.results.val.map sourceType) ≤ j →
          out.2.slots.val[j]? = exec.slots.val[j]?)) ∨
       ((out.1 = .Err (.Trap .Host) ∨ out.1 = .Err (.Exhausted .CallStack) ∧ status = .Err .StackOverflow) ∧
        out.2.slots = exec.slots ∧
        StepH ⟨⟨Store.decodeStore view code before,ambient⟩,vals args ++ [.CALL_ADDR address.index.val]⟩
          [.call address.index.val args none] ⟨⟨Store.decodeStore view code after,ambient⟩,[.TRAP]⟩)) ⦄ := by
  cases status with
  | Err error =>
    cases error <;> simp only [hostResume,WP.spec_ok]
    · exact ⟨by trivial,by trivial,by trivial,by trivial,Or.inr ⟨Or.inl (by trivial),by trivial,Spec.host_trap_step host arguments extension sourceTyped wfAmbient⟩⟩
    · exact ⟨by trivial,by trivial,by trivial,by trivial,Or.inr ⟨Or.inr ⟨by trivial,by trivial⟩,by trivial,Spec.host_trap_step host arguments extension sourceTyped wfAmbient⟩⟩
  | Ok unitValue =>
    cases unitValue
    unfold hostResume
    step with vec_index_given after.funcs address.index function functionAt as ⟨found,same⟩
    subst found
    step with vec_index_given after.types function.signature signature signatureAt as ⟨found,same⟩
    subst found
    step with Store.check_values_source_typed memory view code after (Spec.extend_store_wf extension).2
      results.slice signature.results.slice issued as ⟨checked,accepted⟩
    cases checked with
    | Err error =>
      simp only [runtime.interp.check_failed,bind_ok,ite_true,WP.spec_ok]
      exact ⟨by trivial,by trivial,by trivial,by trivial,Or.inr ⟨Or.inl (by trivial),by trivial,Spec.host_trap_step host arguments extension sourceTyped wfAmbient⟩⟩
    | Ok unitValue =>
      cases unitValue
      obtain ⟨typed,owned,tags⟩ := accepted rfl
      simp only [runtime.interp.check_failed,bind_ok,Bool.false_eq_true,ite_false]
      have widths : (Code.encodeValues (results.val.map sourceValue)).length =
          Code.slots (signature.results.val.map sourceType) := by
        rw [Code.encodeValues_length]
        simp only [List.map_map,Function.comp_def,sourceValue_type]
        change signature.results.val = results.val.map rawType at tags
        rw [tags,List.map_map]
        rfl
      step with host_results_encode exec.slots results signature.results after.id base tags
        (fun value member => (owned value member).1) (by rw [widths]; exact capacity)
        as ⟨words,length,represented,preserved⟩
      exact Or.inl ⟨Spec.host_return_step host arguments extension sourceTyped typed wfAmbient,
        typed,represented,length,by simpa only [widths] using preserved⟩
end Exec.Theorems
