import Exec.Interp.Host.HostPreparationCauses
namespace Exec.Interp
open Aeneas Aeneas.Std

/-- Execute the complete extracted host-call preparation, passing the exact
source arguments and zero-initialized result buffer to the callback proof. -/
theorem call_host_composition {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (address : runtime.FuncAddr) (base : Usize)
    (function : runtime.store.Function) (identity : U64) (signature : Itasca.types.FuncType)
    (functionAt : store.funcs.val[address.index.val]? = some function)
    (host : function.code = .Host identity)
    (signatureAt : store.types.val[function.signature.val]? = some signature)
    (values : List val)
    (typed : signature.params.val.map sourceType = values.map Code.valueType)
    (wellFormed : ∀ value ∈ values, wf_val value)
    (fits : ∀ value ∈ values, ResultIndexFits value)
    (represented : ValuesAt exec.slots.val base.val values)
    (post : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P → Prop)
    (resume : ∀ (ready : runtime.interp.Execution) (nextPlatform : P)
        (args results : alloc.vec.Vec runtime.Value),
      (∃ padding, SlotsEffect exec ready (exec.slots.val ++ padding)) →
      ready.frames = exec.frames →
      base.val + Code.slots (signature.results.val.map sourceType) ≤ ready.slots.length →
      args.val.map sourceValue = values → results.val = signature.results.val.map zeroValue →
      (do
        let (status,p,s,returned) ← hooks.call_host nextPlatform store identity args.slice results.slice
        let (status,finished) ← hostResume memory {ready with host_args := args} s address base
          ⟨returned⟩ status
        Result.ok (status,finished,s,p)) ⦃ post ⦄) :
    runtime.interp.call memory hooks floats allocator exec store platform address base ⦃ out =>
      (∃ error, out.1 = .Err error ∧ HostPreparationError error ∧ out.2.2.1 = store) ∨ post out ⦄ := by

  apply WP.spec_mono (call_host_composition_causes memory hooks floats allocator allocation interrupts
    exec store platform address base function identity signature functionAt host signatureAt values
    typed wellFormed fits represented post resume)
  intro out outcome
  rcases outcome with ⟨error,status,cause,unchanged⟩ | result
  · exact Or.inl ⟨error,status,cause.error,unchanged⟩
  · exact Or.inr result
end Exec.Interp
