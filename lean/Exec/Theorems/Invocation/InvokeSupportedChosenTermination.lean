import Exec.Theorems.Invocation.InvokeSupportedChosenDivergence
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}
/-- One terminating selected source run yields an ordinary host-free public
invocation result with the full invariant and classified outcome retained. -/
theorem invoke_defined_supported_chosen_terminates {choices : Spec.SourceChoices} (admissible : choices.Admissible)
    (numericChoice : choices.numeric=Spec.firstNumericChoice) (vector : choices.vector=Spec.firstVectorChoice) (occurrence : Nat)
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
    (compatible : GrowthChoicesCompatible memory allocator view choices)
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
    (hw : function.code = .Wasm instanceIndex functionIndex)
    (accepted : runtime.interp.check_values memory store args (alloc.vec.Vec.deref signature.params)=.ok (.Ok ()))
    {events : List HostEvent} {target : config}
    (run : Spec.ChoiceSteps choices occurrence
      ⟨⟨Store.decodeStore view code store,ambient⟩,vals (args.val.map Interp.sourceValue) ++ [.CALL_ADDR address.index.val]⟩ events target)
    (terminal : Spec.SourceTerminal target) :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results
      ⦃ out =>
        (CertifiedSupportedStore emission allowed view code out.2.2.1 ∧ Interp.FrameStoreMetadata store out.2.2.1 ∧
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
          (Store.decodeStore view code out.2.2.1) ambient error) ⦄ := by
  have notdiv : runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results≠.div := by
    intro divergent
    exact Spec.chosen_terminating_no_infinite admissible run terminal
      (invoke_defined_supported_infinite_chosen admissible numericChoice vector occurrence language memory hooks floats allocator
        correct allocation interrupts view laws code compatible exec store platform certified hostFree ambient ambientWf
        address function signature instanceIndex functionIndex args results owner owned hf hs hw divergent)
  have safe := invoke_defined_supported_outcomes language memory hooks floats allocator correct allocation interrupts view laws code
    exec store platform certified hostFree ambient ambientWf address function signature instanceIndex functionIndex args results
    owner owned hf hs hw accepted
  generalize answerEq : runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results=answer at safe notdiv ⊢
  cases safe with
  | ret post => exact .ret post
  | div => exact False.elim (notdiv rfl)
end Exec.Theorems
