import Exec.Theorems.Invocation.InvokeSupported
import Exec.Interp.Invocation.InvokeCheckedMutable
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}

/-- The actual checker either rejects before changing caller state or enters
the proved mutable Core invocation. No accepted-arguments premise is required. -/
theorem invoke_defined_supported_checked
    [∀ compiled, StructuredMachine.FloatHeads (emission compiled)]
    [∀ compiled, StructuredMachine.OrdinaryHeads (emission compiled)]
    [∀ compiled, StructuredMachine.StatefulProjection (emission compiled) compiled.indirect.val]
    [∀ compiled, StructuredMachine.IndirectProjection (emission compiled) compiled.indirect.val]
    [∀ compiled, StructuredMachine.SimdProjection (emission compiled) compiled.simd.val compiled.v128_pool.val]
    [∀ compiled, StructuredMachine.TypedSelectHeads (emission compiled)]
    [∀ compiled, StructuredMachine.SupportedHeads (emission compiled)]
    [∀ compiled, StructuredMachine.ErasedHeads (emission compiled)]
    (language : Abs.Supported.Language allowed) {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (certified : CertifiedSupportedStore emission allowed view code store) (hostFree : CoreHostFree store)
    (ambient : frame) (ambientWf : wf_frame ambient)
    (address : runtime.FuncAddr) (function : runtime.store.Function)
    (signature : Itasca.types.FuncType) (instanceIndex functionIndex : Usize)
    (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (owner : address.store = store.id)
    (owned : ∀ value ∈ args.val, Store.ValueInStore store value)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (hw : function.code = .Wasm instanceIndex functionIndex) :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results
      ⦃ out =>
        (∃ error, runtime.interp.check_values memory store args (alloc.vec.Vec.deref signature.params) = .ok (.Err error) ∧
          out = (.Err error,exec,store,platform,results)) ∨
        ((CertifiedSupportedStore emission allowed view code out.2.2.1 ∧ Interp.FrameStoreMetadata store out.2.2.1 ∧
          Extend_store (Store.decodeStore view code store) (Store.decodeStore view code out.2.2.1) ∧ Store.SegmentCounts store out.2.2.1) ∧
        (out.1 = .Ok () →
          signature.results.val.map Interp.sourceType = (out.2.2.2.2.val.map Interp.sourceValue).map Code.valueType ∧
          StepsH ⟨⟨Store.decodeStore view code store,ambient⟩,
            vals (args.val.map Interp.sourceValue) ++ [admininstr.CALL_ADDR address.index.val]⟩ []
            ⟨⟨Store.decodeStore view code out.2.2.1,ambient⟩,vals (out.2.2.2.2.val.map Interp.sourceValue)⟩) ∧
        (∀ error, out.1 = .Err error → SupportedInvocationError
          ⟨⟨Store.decodeStore view code store,ambient⟩,
            vals (args.val.map Interp.sourceValue) ++ [admininstr.CALL_ADDR address.index.val]⟩
          (Store.decodeStore view code out.2.2.1) ambient error)) ⦄div := by
  apply WP.dspec_mono (Interp.invoke_with_checked_outcome memory hooks floats allocator exec store platform
    address function signature args results owner hf hs
    (fun out => (CertifiedSupportedStore emission allowed view code out.2.2.1 ∧ Interp.FrameStoreMetadata store out.2.2.1 ∧
          Extend_store (Store.decodeStore view code store) (Store.decodeStore view code out.2.2.1) ∧ Store.SegmentCounts store out.2.2.1) ∧
        (out.1 = .Ok () →
          signature.results.val.map Interp.sourceType = (out.2.2.2.2.val.map Interp.sourceValue).map Code.valueType ∧
          StepsH ⟨⟨Store.decodeStore view code store,ambient⟩,
            vals (args.val.map Interp.sourceValue) ++ [admininstr.CALL_ADDR address.index.val]⟩ []
            ⟨⟨Store.decodeStore view code out.2.2.1,ambient⟩,vals (out.2.2.2.2.val.map Interp.sourceValue)⟩) ∧
        (∀ error, out.1 = .Err error → SupportedInvocationError
          ⟨⟨Store.decodeStore view code store,ambient⟩,
            vals (args.val.map Interp.sourceValue) ++ [admininstr.CALL_ADDR address.index.val]⟩
          (Store.decodeStore view code out.2.2.1) ambient error))
    (fun accepted => invoke_defined_supported_outcomes language memory hooks floats allocator correct allocation interrupts
      view laws code exec store platform certified hostFree ambient ambientWf address function signature
      instanceIndex functionIndex args results owner owned hf hs hw accepted))
  intro out outcome
  exact outcome.elim Or.inl (fun accepted => Or.inr accepted.2)
end Exec.Theorems
