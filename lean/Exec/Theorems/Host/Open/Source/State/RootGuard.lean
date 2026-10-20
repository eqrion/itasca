import Exec.Theorems.Host.Open.Source.State.StateGuard
import Exec.Theorems.Host.Open.Driver.DriverStackSafety
import Exec.Theorems.Host.Open.Driver.StackTraces
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std Exec.Interp Exec.Interp.OpenCall

/-- Actual public preparation constructs the initial coupled source/native
guard from issued function metadata and owned inputs, including argument and
resource rejection. No invocation outcome or host normality is assumed. -/
theorem prepare_source_root_guard {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (address : runtime.FuncAddr) (function : runtime.store.Function) (signature : Itasca.types.FuncType)
    (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value) (owner : address.store=store.id)
    (owned : ∀value∈args.val,Store.ValueInStore store value)
    (functionAt : store.funcs.val[address.index.val]?=some function)
    (signatureAt : store.types.val[function.signature.val]?=some signature) :
    prepareInvoke memory (inert memory) floats allocator exec store () address args results ⦃phase=>
      let native : State M:=⟨store,.preparing phase,[],[.invokeEnter address args]⟩
      let source : Spec.OpenExecution.State SourceControl:=⟨Store.decodeStore view code store,
        .invokeRequest address.index.val (args.val.map sourceValue) (signature.params.val.map sourceType) (signature.results.val.map sourceType),[]⟩
      SourceStateGuard memory allocator view code native source 0 ∧ native.Shape .invocation ∧ NoOverflowMode native.mode⦄ := by
  apply WP.spec_mono (prepare_source_root_input memory (inert memory) floats allocator allocation (fun _=>WP.spec.ret trivial)
    view code exec store () held Spec.invocationFrame Spec.empty_frame_wf address function signature args results owner owned functionAt signatureAt)
  intro phase ready
  exact ⟨⟨held,.preparing exec address signature args results phase ⟨owner,function,functionAt,signatureAt⟩ ready,.nil,rfl⟩,.nil _,trivial⟩
end Exec.Theorems.OpenReentrantControl
