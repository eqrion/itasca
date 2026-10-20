import Exec.Theorems.Host.Open.Source.State.RootCall
import Exec.Theorems.Host.Open.Driver.RootInvoke
import Exec.Interp.Relations.ArgumentRejectionKind
import Exec.Store.Invariant.CheckedValuesComplete
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall

/-- Checked root setup retains whether it rejected arguments or encountered
an actual resource refusal. Accepted arguments retain the stronger call guard. -/
inductive SourceRootInvokeReady {M A : Type} (allocator : runtime.platform.Alloc A)
    (hooks : runtime.platform.Platform Unit M) (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (token : Unit)
    (ambient : frame) (address : runtime.FuncAddr) (signature : Itasca.types.FuncType)
    (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value) : InvokePhase M Unit → Prop
  | rejected (error : runtime.ExecError)
      (kind : error=.BadArguments ∨ error=.WrongStore)
      (notTyped : ¬ResultsTyped (Store.decodeStore view code store) (signature.params.val.map sourceType) (args.val.map sourceValue)) :
      SourceRootInvokeReady allocator hooks view code exec store token ambient address signature args results
        (.done (.Err error,exec,store,token,results))
  | resource (error : runtime.ExecError) (afterExec : runtime.interp.Execution)
      (typed : ResultsTyped (Store.decodeStore view code store) (signature.params.val.map sourceType) (args.val.map sourceValue))
      (cause : InvocationResourceCause allocator exec store signature results error) :
      SourceRootInvokeReady allocator hooks view code exec store token ambient address signature args results
        (.done (.Err error,afterExec,store,token,results))
  | waiting (prepared : runtime.interp.Execution) (nextToken : Unit) (phase : CallPhase M Unit)
      (empty : prepared.frames.val=[])
      (typed : ResultsTyped (Store.decodeStore view code store) (signature.params.val.map sourceType) (args.val.map sourceValue))
      (ready : SourceRootCallReady allocator hooks prepared store nextToken view code ambient address signature (args.val.map sourceValue) phase) :
      SourceRootInvokeReady allocator hooks view code exec store token ambient address signature args results (.waiting phase address results)

/-- Owned root inputs are checked against independent source typing before
any invocation preparation. No successful checker or invocation is assumed. -/
theorem prepare_source_root_input {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform Unit M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀p,hooks.interrupt p ⦃ _=>True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (token : Unit)
    (held : ExecutableInv view code store) (ambient : frame) (ambientWf : wf_frame ambient)
    (address : runtime.FuncAddr) (function : runtime.store.Function) (signature : Itasca.types.FuncType)
    (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value) (owner : address.store=store.id)
    (owned : ∀value∈args.val,Store.ValueInStore store value)
    (functionAt : store.funcs.val[address.index.val]?=some function)
    (signatureAt : store.types.val[function.signature.val]?=some signature) :
    prepareInvoke memory hooks floats allocator exec store token address args results
      ⦃phase=>SourceRootInvokeReady allocator hooks view code exec store token ambient address signature args results phase⦄ := by
  obtain ⟨checked,actual,accepts⟩ := WP.spec_imp_exists
    (Store.check_values_source_iff memory view code store held.well_formed args signature.params owned)
  cases checked with
  | Ok unit=>
    cases unit
    have typed:=accepts.mp rfl
    apply prepare_invoke_checked memory hooks floats allocator allocation exec store token address function signature args results
      owner functionAt signatureAt actual (fun value member=>(owned value member).1)
    · intro error cause afterExec
      exact .resource error afterExec typed cause
    · intro prepared nextToken preparedOwner empty words
      exact WP.spec_mono (prepare_source_root_call memory hooks floats allocator allocation interrupts view code prepared store nextToken
        held ambient ambientWf address function signature args empty preparedOwner words actual owned functionAt signatureAt typed)
        (fun phase ready=>.waiting prepared nextToken phase empty typed ready)
  | Err error=>
    have notTyped : ¬ResultsTyped (Store.decodeStore view code store) (signature.params.val.map sourceType) (args.val.map sourceValue) := by
      intro typed
      have impossible := accepts.mpr typed
      cases impossible
    have kind:=check_values_error_kind memory store args signature.params.deref error actual
    unfold prepareInvoke
    step with func_type_lookup memory store address function signature owner functionAt signatureAt as ⟨found,same⟩
    subst found
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    rw [actual,bind_ok]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    simpa [core.convert.FromSame.from,bind_ok] using
      (WP.spec.ret (SourceRootInvokeReady.rejected (allocator:=allocator) (hooks:=hooks) (view:=view) (code:=code)
        (exec:=exec) (store:=store) (token:=token) (ambient:=ambient) (address:=address) (signature:=signature)
        (args:=args) (results:=results) error kind notTyped))
/-- Source setup supplies the established native root guard as a consequence. -/
theorem SourceRootInvokeReady.forget {M A : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform Unit M} {view : M → Slice U8} {code : Store.CodeInterpretation}
    {exec : runtime.interp.Execution} {store : runtime.store.Store M} {token : Unit}
    {ambient : frame} {address : runtime.FuncAddr} {signature : Itasca.types.FuncType}
    {args : Slice runtime.Value} {results : alloc.vec.Vec runtime.Value} {phase : InvokePhase M Unit}
    (ready : SourceRootInvokeReady allocator hooks view code exec store token ambient address signature args results phase) :
    RootInvokeReady view code store ambient address signature (args.val.map sourceValue) phase := by
  cases ready with
  | rejected error kind notTyped=>exact .rejected _ error rfl rfl
  | resource error afterExec typed cause=>exact .rejected _ error rfl rfl
  | waiting prepared nextToken phase empty typed ready=>exact .waiting phase results ready.forget
end Exec.Theorems.OpenReentrantControl
