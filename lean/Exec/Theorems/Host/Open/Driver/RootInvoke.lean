import Exec.Theorems.Host.Open.Driver.RootPreparation
import Exec.Interp.Invocation.OpenInvokeSetup
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall

inductive RootInvokeReady {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (ambient : frame) (address : runtime.FuncAddr)
    (signature : Itasca.types.FuncType) (arguments : List val) : InvokePhase M Unit → Prop
  | rejected (answer : InvokeAnswer M Unit) (error : runtime.ExecError)
      (status : answer.1=.Err error) (sameStore : answer.2.2.1=store) :
      RootInvokeReady view code store ambient address signature arguments (.done answer)
  | waiting (phase : CallPhase M Unit) (results : alloc.vec.Vec runtime.Value)
      (ready : RootCallReady view code store ambient address signature arguments phase) :
      RootInvokeReady view code store ambient address signature arguments (.waiting phase address results)

/-- Valid checked public inputs prepare a root task or return an ordinary
resource error. The proof constructs the Wasm/host guard from raw metadata. -/
theorem prepare_root_invoke {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform Unit M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀p,hooks.interrupt p ⦃ _=>True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (token : Unit)
    (held : ExecutableInv view code store) (ambient : frame) (ambientWf : wf_frame ambient)
    (address : runtime.FuncAddr) (function : runtime.store.FuncInst) (signature : Itasca.types.FuncType)
    (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value) (owner : address.store=store.id)
    (accepted : runtime.interp.check_values memory store args signature.params.deref=.ok (.Ok ()))
    (owned : ∀value∈args.val,Store.ValueInStore store value)
    (functionAt : store.funcs.val[address.index.val]?=some function)
    (signatureAt : store.types.val[function.signature.val]?=some signature)
    (typed : ResultsTyped (Store.decodeStore view code store) (signature.params.val.map sourceType) (args.val.map sourceValue)) :
    prepareInvoke memory hooks floats allocator exec store token address args results
      ⦃phase=>RootInvokeReady view code store ambient address signature (args.val.map sourceValue) phase⦄ := by
  apply prepare_invoke_checked memory hooks floats allocator allocation exec store token address function signature args results
    owner functionAt signatureAt accepted (fun value member=>(owned value member).1)
  · intro error cause afterExec
    exact .rejected _ error rfl rfl
  · intro prepared nextToken preparedOwner empty words
    exact WP.spec_mono (prepare_root_call memory hooks floats allocator allocation interrupts view code prepared store nextToken
      held ambient ambientWf address function signature args empty preparedOwner words accepted owned functionAt signatureAt typed)
      (fun phase ready=>.waiting phase results ready)
end Exec.Theorems.OpenReentrantControl
