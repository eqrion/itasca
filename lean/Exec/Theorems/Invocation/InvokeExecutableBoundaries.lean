import Exec.Theorems.Invocation.InvokeSupportedBoundaries
import Exec.Interp.StructuredMachine.ExecutableFunctionHeads
import Exec.Interp.Relations.TypedArguments
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- Complete-language host-free invocation retains its initial limits and
explains frame exhaustion and interruption from actual execution. -/
theorem invoke_defined_executable_boundaries
 {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (certified : CertifiedSupportedStore Executable.emission Abs.ExecutableInstr view code store) (hostFree : CoreHostFree store)
    (ambient : frame) (ambientWf : wf_frame ambient)
    (address : runtime.FuncAddr) (function : runtime.store.FuncInst)
    (signature : Itasca.types.FuncType) (instanceIndex functionIndex : Usize)
    (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (owner : address.store = store.id)
    (owned : ∀ value ∈ args.val, Store.ValueInStore store value)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (hw : function.code = .Wasm instanceIndex functionIndex)
    (typedArguments : ResultsTyped (Store.decodeStore view code store)
      (signature.params.val.map sourceType) (args.val.map sourceValue)) :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results
      ⦃ out =>
        (CertifiedSupportedStore Executable.emission Abs.ExecutableInstr view code out.2.2.1 ∧ Interp.FrameStoreMetadata store out.2.2.1 ∧
          Extend_store (Store.decodeStore view code store) (Store.decodeStore view code out.2.2.1) ∧
          Store.SegmentCounts store out.2.2.1 ∧ out.2.2.1.limits = store.limits) ∧
        (out.1 = .Ok () →
          signature.results.val.map Interp.sourceType = (out.2.2.2.2.val.map Interp.sourceValue).map Code.valueType ∧
          StepsH ⟨⟨Store.decodeStore view code store,ambient⟩,
            vals (args.val.map Interp.sourceValue) ++ [admininstr.CALL_ADDR address.index.val]⟩ []
            ⟨⟨Store.decodeStore view code out.2.2.1,ambient⟩,vals (out.2.2.2.2.val.map Interp.sourceValue)⟩) ∧
        (∀ error, out.1 = .Err error → InvocationBoundaryCause hooks
          ⟨⟨Store.decodeStore view code store,ambient⟩,
            vals (args.val.map Interp.sourceValue) ++ [admininstr.CALL_ADDR address.index.val]⟩
          store.limits.max_frames.val error) ⦄div := by
  exact invoke_defined_supported_boundaries Abs.executable_language memory hooks floats allocator correct allocation interrupts
    view laws code exec store platform certified hostFree ambient ambientWf address function signature
    instanceIndex functionIndex args results owner owned hf hs hw
    (typed_arguments_accepted memory store (Store.decodeStore view code store) args signature.params
      typedArguments (fun value member => (owned value member).1))
end Exec.Theorems
