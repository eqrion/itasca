import Exec.Theorems.Invocation.InvokeSupportedChosenTermination
import Exec.Theorems.Invocation.InvokeSupportedChosenOutcomes
import Exec.Theorems.Invocation.InvokeSupportedResources
import Exec.Theorems.Api.InvocationResourcesAdequate
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}
/-- The full host-free public invocation matches one terminating run under the
selected policy. Source capacities and primitive availability exclude setup,
call and result-buffer exhaustion; native trap diagnostics remain abstract. -/
theorem invoke_defined_supported_chosen_matches {choices : Spec.SourceChoices} (admissible : choices.Admissible)
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
    (address : runtime.FuncAddr) (function : runtime.store.FuncInst)
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
    (terminal : Spec.SourceTerminal target)
    (capacities : Store.FunctionCapacities code store)
    (resources : SourceInvocationResources
      ⟨⟨Store.decodeStore view code store,ambient⟩,vals (args.val.map sourceValue) ++ [.CALL_ADDR address.index.val]⟩
      (Store.decodeStore view code store) (Store.decodeFuncType signature) address.index.val
      store.limits.max_values.val store.limits.max_frames.val)
    (available : Platform.AllocationAvailable allocator (2*Usize.max))
    (continuing : ∀ before after,hooks.interrupt before≠.ok (.Terminate,after)) :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results
      ⦃ out =>
        (CertifiedSupportedStore emission allowed view code out.2.2.1 ∧ FrameStoreMetadata store out.2.2.1 ∧
          Extend_store (Store.decodeStore view code store) (Store.decodeStore view code out.2.2.1) ∧
          Store.SegmentCounts store out.2.2.1) ∧ events=[] ∧
        match out.1 with
        | .Ok _ => target=⟨⟨Store.decodeStore view code out.2.2.1,ambient⟩,vals (out.2.2.2.2.val.map sourceValue)⟩
        | .Err (.Trap trap) => CumulativeTrap trap ∧ target=⟨⟨Store.decodeStore view code out.2.2.1,ambient⟩,[.TRAP]⟩
        | .Err _ => False ⦄ := by
  obtain ⟨out,actual,held⟩ := WP.spec_imp_exists
    (invoke_defined_supported_chosen_terminates admissible numericChoice vector occurrence language memory hooks floats allocator
      correct allocation interrupts view laws code compatible exec store platform certified hostFree ambient ambientWf address function signature
      instanceIndex functionIndex args results owner owned hf hs hw accepted run terminal)
  have selected := invoke_defined_supported_chosen_outcomes admissible numericChoice vector occurrence language memory hooks floats allocator
    correct allocation interrupts view laws code compatible exec store platform certified hostFree ambient ambientWf address function signature
    instanceIndex functionIndex args results owner owned hf hs hw accepted
  have bounded := invoke_defined_supported_resources language memory hooks floats allocator correct allocation interrupts view laws code
    exec store platform certified hostFree ambient ambientWf address function signature instanceIndex functionIndex args results owner capacities
    owned hf hs hw accepted
  rw [actual,WP.dspec_ok] at selected bounded
  rw [actual,WP.spec_ok]
  refine ⟨selected.1,?_⟩
  cases status : out.1 with
  | Ok unit =>
    obtain ⟨tags,source⟩ := selected.2.1 status
    exact Spec.chosen_terminal_unique admissible run terminal _ _ source (.values _ _)
  | Err error =>
    have cause := (bounded.2.2 error status).2
    have meaning := selected.2.2 error status
    cases error with
    | Trap trap =>
      obtain ⟨kind,source⟩ := meaning
      obtain ⟨empty,same⟩ := Spec.chosen_terminal_unique admissible run terminal _ _ source (.trap _)
      exact ⟨empty,kind,same⟩
    | Terminated =>
      exact False.elim (cause.excludes_boundary resources (Spec.stepsH_wf (run.erases admissible)).1 available continuing (Or.inl rfl))
    | Exhausted resource =>
      cases resource with
      | CallStack => exact False.elim (cause.excludes_boundary resources (Spec.stepsH_wf (run.erases admissible)).1 available continuing (Or.inr (Or.inl rfl)))
      | Values => exact False.elim (cause.excludes_boundary resources (Spec.stepsH_wf (run.erases admissible)).1 available continuing (Or.inr (Or.inr (Or.inl rfl))))
      | Allocation => exact False.elim (cause.excludes_boundary resources (Spec.stepsH_wf (run.erases admissible)).1 available continuing (Or.inr (Or.inr (Or.inr rfl))))
      | Objects => exact False.elim cause
    | _ => exact False.elim meaning
end Exec.Theorems
