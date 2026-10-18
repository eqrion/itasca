import Exec.Theorems.Invocation.InvokeSupportedTyped
import Exec.Interp.StructuredMachine.ExecutableFunctionHeads
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- The common invocation proof instantiated with the complete executable
source language and its checked compiler-emission projections. -/
theorem invoke_defined_executable_typed
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
    (address : runtime.FuncAddr) (function : runtime.store.Function)
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
          Store.SegmentCounts store out.2.2.1) ∧
        (out.1 = .Ok () →
          signature.results.val.map Interp.sourceType = (out.2.2.2.2.val.map Interp.sourceValue).map Code.valueType ∧
          StepsH ⟨⟨Store.decodeStore view code store,ambient⟩,
            vals (args.val.map Interp.sourceValue) ++ [admininstr.CALL_ADDR address.index.val]⟩ []
            ⟨⟨Store.decodeStore view code out.2.2.1,ambient⟩,vals (out.2.2.2.2.val.map Interp.sourceValue)⟩) ∧
        (∀ error, out.1 = .Err error → SupportedInvocationError
          ⟨⟨Store.decodeStore view code store,ambient⟩,
            vals (args.val.map Interp.sourceValue) ++ [admininstr.CALL_ADDR address.index.val]⟩
          (Store.decodeStore view code out.2.2.1) ambient error) ⦄div := by
  exact invoke_defined_supported_typed Abs.executable_language memory hooks floats allocator correct allocation interrupts
    view laws code exec store platform certified hostFree ambient ambientWf address function signature
    instanceIndex functionIndex args results owner owned hf hs hw typedArguments
end Exec.Theorems
