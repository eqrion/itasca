import Exec.Theorems.Host.Open.Driver.RootInvoke
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall

/-- Issued public inputs need not already pass dynamic argument checking.
Rejection is an ordinary unchanged-store result; accepted inputs establish the
typed resumable root guard without assuming a successful checker result. -/
theorem prepare_root_input {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform Unit M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀p,hooks.interrupt p ⦃ _=>True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (token : Unit)
    (held : ExecutableInv view code store) (ambient : frame) (ambientWf : wf_frame ambient)
    (address : runtime.FuncAddr) (function : runtime.store.FuncInst) (signature : Itasca.types.FuncType)
    (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value) (owner : address.store=store.id)
    (issued : ∀value∈args.val,Store.IssuedValue store value)
    (functionAt : store.funcs.val[address.index.val]?=some function)
    (signatureAt : store.types.val[function.signature.val]?=some signature) :
    prepareInvoke memory hooks floats allocator exec store token address args results
      ⦃phase=>RootInvokeReady view code store ambient address signature (args.val.map sourceValue) phase⦄ := by
  obtain ⟨checked,actual,post⟩ := WP.spec_imp_exists (Store.check_values_source_typed memory view code store held.well_formed
    args signature.params.deref issued)
  cases checked with
  | Ok unit =>
    cases unit
    obtain ⟨typed,owned,tags⟩ := post rfl
    have typedArgs : ResultsTyped (Store.decodeStore view code store) (signature.params.val.map sourceType) (args.val.map sourceValue) := by
      simpa only [alloc.vec.Vec.deref,Slice.from_val] using typed
    exact prepare_root_invoke memory hooks floats allocator allocation interrupts view code exec store token held ambient ambientWf
      address function signature args results owner actual owned functionAt signatureAt typedArgs
  | Err error =>
    unfold prepareInvoke
    step with func_type_lookup memory store address function signature owner functionAt signatureAt as ⟨found,same⟩
    subst found
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    rw [actual,bind_ok]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    simpa [core.convert.FromSame.from,bind_ok] using
      (WP.spec.ret (RootInvokeReady.rejected (view:=view) (code:=code) (ambient:=ambient) (address:=address)
        (signature:=signature) (arguments:=args.val.map sourceValue) (.Err error,exec,store,token,results) error rfl rfl))
end Exec.Theorems.OpenReentrantControl
