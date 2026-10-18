import Exec.Theorems.Invocation.InvokeSupported
import Exec.Theorems.Composition.Supported.SupportedCumulativeCertificate
import Exec.Interp.StructuredMachine.SupportedCumulativeHeads
import Exec.Theorems.Composition.Cumulative.CumulativeEntryOutcomes
import Exec.Theorems.Composition.Cumulative.CumulativeLoopReadback
import Exec.Theorems.Composition.Cumulative.CumulativeErrors
import Exec.Interp.Invocation.InvokeMutable
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt

/-- Source meaning of the error classes reachable after accepting owned Core
arguments. Stronger local theorems retain exact resource and hook witnesses. -/
def CumulativeInvocationError (initial : config) (s : _root_.store) (ambient : frame) : runtime.ExecError → Prop
  | .Trap trap => CumulativeTrap trap ∧ StepsH initial [] ⟨⟨s,ambient⟩,[.TRAP]⟩
  | .Exhausted _ | .Terminated => True
  | _ => False

/-- Actual public invocation preserves the certified mutable store and agrees
with source execution on results and traps. Defined-only Core code includes
integer/control operations, scalar constants, globals, and scalar memory. -/
theorem invoke_defined_cumulative_outcomes {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (certified : CertifiedCumulativeStore view code store) (hostFree : CoreHostFree store)
    (ambient : frame) (ambientWf : wf_frame ambient)
    (address : runtime.FuncAddr) (function : runtime.store.Function)
    (signature : Itasca.types.FuncType) (instanceIndex functionIndex : Usize)
    (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (owner : address.store = store.id)
    (owned : ∀ value ∈ args.val, Store.ValueInStore store value)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (hw : function.code = .Wasm instanceIndex functionIndex)
    (accepted : runtime.interp.check_values memory store args (alloc.vec.Vec.deref signature.params) = .ok (.Ok ())) :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results
      ⦃ out =>
        (CertifiedCumulativeStore view code out.2.2.1 ∧ Interp.FrameStoreMetadata store out.2.2.1 ∧
          Extend_store (Store.decodeStore view code store) (Store.decodeStore view code out.2.2.1)) ∧
        (out.1 = .Ok () →
          signature.results.val.map Interp.sourceType = (out.2.2.2.2.val.map Interp.sourceValue).map Code.valueType ∧
          StepsH ⟨⟨Store.decodeStore view code store,ambient⟩,
            vals (args.val.map Interp.sourceValue) ++ [admininstr.CALL_ADDR address.index.val]⟩ []
            ⟨⟨Store.decodeStore view code out.2.2.1,ambient⟩,vals (out.2.2.2.2.val.map Interp.sourceValue)⟩) ∧
        (∀ error, out.1 = .Err error → CumulativeInvocationError
          ⟨⟨Store.decodeStore view code store,ambient⟩,
            vals (args.val.map Interp.sourceValue) ++ [admininstr.CALL_ADDR address.index.val]⟩
          (Store.decodeStore view code out.2.2.1) ambient error) ⦄div := by
  apply WP.dspec_mono (invoke_defined_supported_outcomes (emission := Interp.Cumulative.emission)
    Abs.cumulative_language memory hooks floats allocator correct allocation interrupts view laws code
    exec store platform certified.supported hostFree ambient ambientWf address function signature
    instanceIndex functionIndex args results owner owned hf hs hw accepted)
  rintro out ⟨⟨fresh,metadata,extension,segments⟩,success,failure⟩
  exact ⟨⟨fresh.cumulative,metadata,extension⟩,success,failure⟩
end Exec.Theorems
