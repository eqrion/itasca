import Exec.Store.Invariant.CheckedValues
import Exec.Spec.HostCall
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt

/-- The actual host result checker supplies either typed return values or a
source host trap. The hook's result types are not assumed. -/
theorem host_result_check_source {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (before after : runtime.store.Store M) (frame : _root_.frame)
    (address identity : Nat) (params : List valtype) (types : Slice Itasca.types.ValueType)
    (args : List val) (results : Slice runtime.Value)
    (host : HostFunction (Store.decodeStore view code before) address identity
      params (types.val.map Interp.sourceType))
    (arguments : ResultsTyped (Store.decodeStore view code before) params args)
    (extension : Extend_store (Store.decodeStore view code before) (Store.decodeStore view code after))
    (sourceTyped : Store_ok (Store.decodeStore view code after))
    (ambient : wf_frame frame)
    (issued : ∀ value ∈ results.val, Store.IssuedValue after value) :
    (do
      let checked ← runtime.interp.check_values memory after results types
      let failed ← runtime.interp.check_failed checked
      pure (if failed then core.result.Result.Err (runtime.ExecError.Trap runtime.Trap.Host) else .Ok ())) ⦃ status =>
      (status = .Ok () ∧
        StepH ⟨⟨Store.decodeStore view code before, frame⟩, vals args ++ [.CALL_ADDR address]⟩
          [.call address args (some (results.val.map Interp.sourceValue))]
          ⟨⟨Store.decodeStore view code after, frame⟩, vals (results.val.map Interp.sourceValue)⟩ ∧
        (∀ value ∈ results.val, Store.ValueInStore after value) ∧
        types.val = results.val.map Interp.rawType) ∨
      (status = .Err (.Trap .Host) ∧
        StepH ⟨⟨Store.decodeStore view code before, frame⟩, vals args ++ [.CALL_ADDR address]⟩
          [.call address args none] ⟨⟨Store.decodeStore view code after, frame⟩, [.TRAP]⟩) ⦄ := by
  step with Store.check_values_source_typed memory view code after (Spec.extend_store_wf extension).2
    results types issued as ⟨checked, accepted⟩
  cases checked with
  | Ok token =>
    cases token
    obtain ⟨typed, owned, tags⟩ := accepted rfl
    simp only [runtime.interp.check_failed, bind_ok, Bool.false_eq_true, ite_false, WP.spec_ok]
    exact Or.inl ⟨trivial, Spec.host_return_step host arguments extension sourceTyped typed ambient, owned, tags⟩
  | Err error =>
    simp only [runtime.interp.check_failed, bind_ok, ite_true, WP.spec_ok]
    exact Or.inr ⟨trivial, Spec.host_trap_step host arguments extension sourceTyped ambient⟩
end Exec.Theorems
