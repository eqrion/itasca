import Exec.Theorems.Composition.Supported.SupportedEntryOutcomes
import Exec.Theorems.Composition.Supported.SupportedLoopReadback
import Exec.Theorems.Composition.Supported.SupportedErrors
import Exec.Theorems.Composition.Supported.ChosenNativeOutcomes
import Exec.Theorems.Composition.Supported.ChosenLoopSource
import Exec.Spec.Choices.NeutralStep
import Exec.Interp.Invocation.InvokeMutable
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}

/-- Source meaning of the error classes reachable after accepting owned Core
arguments. Stronger local theorems retain exact resource and hook witnesses. -/
def ChosenSupportedInvocationError (choices : Spec.SourceChoices) (occurrence : Nat) (initial : config) (s : _root_.store) (ambient : frame) : runtime.ExecError → Prop
  | .Trap trap => CumulativeTrap trap ∧ Spec.ChoiceSteps choices occurrence initial [] ⟨⟨s,ambient⟩,[.TRAP]⟩
  | .Exhausted _ | .Terminated => True
  | _ => False

/-- Actual invocation uses the common supported machine. Results and traps
retain source execution, the updated store, and segment counts. -/
theorem invoke_defined_supported_chosen_outcomes {choices : Spec.SourceChoices} (admissible : choices.Admissible)
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
    (accepted : runtime.interp.check_values memory store args (alloc.vec.Vec.deref signature.params) = .ok (.Ok ())) :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results
      ⦃ out =>
        (CertifiedSupportedStore emission allowed view code out.2.2.1 ∧ Interp.FrameStoreMetadata store out.2.2.1 ∧
          Extend_store (Store.decodeStore view code store) (Store.decodeStore view code out.2.2.1) ∧
          Store.SegmentCounts store out.2.2.1) ∧
        (out.1 = .Ok () →
          signature.results.val.map Interp.sourceType = (out.2.2.2.2.val.map Interp.sourceValue).map Code.valueType ∧
          Spec.ChoiceSteps choices occurrence ⟨⟨Store.decodeStore view code store,ambient⟩,
            vals (args.val.map Interp.sourceValue) ++ [admininstr.CALL_ADDR address.index.val]⟩ []
            ⟨⟨Store.decodeStore view code out.2.2.1,ambient⟩,vals (out.2.2.2.2.val.map Interp.sourceValue)⟩) ∧
        (∀ error, out.1 = .Err error → ChosenSupportedInvocationError choices occurrence
          ⟨⟨Store.decodeStore view code store,ambient⟩,
            vals (args.val.map Interp.sourceValue) ++ [admininstr.CALL_ADDR address.index.val]⟩
          (Store.decodeStore view code out.2.2.1) ambient error) ⦄div := by
  let entry (prepared : runtime.interp.Execution) : Prop := ∃ source,
    Interp.StructuredMachine.Execution emission (Abs.SupportedState allowed) view code store prepared source (signature.results.val.map Interp.sourceType) 0 false ∧
    Abs.Ownership.StatefulOwned (Store.ownershipBounds store) source ∧ source.ambient = ambient ∧
    StepH ⟨⟨Store.decodeStore view code store,ambient⟩,
      vals (args.val.map Interp.sourceValue) ++ [admininstr.CALL_ADDR address.index.val]⟩ [] (Abs.decode source)
  apply Interp.invoke_with_mutable_error_composition memory hooks floats allocator allocation exec store platform
    address function signature args results owner hf hs accepted (fun value member => (owned value member).1) entry
    (fun after => CertifiedSupportedStore emission allowed view code after ∧ Interp.FrameStoreMetadata store after ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view code after) ∧ Store.SegmentCounts store after)
    ⟨certified,.refl _,Spec.extend_store_refl _ (Store.decodeStore_wf view code store certified.shape certified.storeSyntax),.refl store⟩
    (fun after values => signature.results.val.map Interp.sourceType = values.map Code.valueType ∧
      Spec.ChoiceSteps choices occurrence ⟨⟨Store.decodeStore view code store,ambient⟩,
        vals (args.val.map Interp.sourceValue) ++ [admininstr.CALL_ADDR address.index.val]⟩ []
        ⟨⟨Store.decodeStore view code after,ambient⟩,vals values⟩)
    (fun after => ChosenSupportedInvocationError choices occurrence ⟨⟨Store.decodeStore view code store,ambient⟩,
      vals (args.val.map Interp.sourceValue) ++ [admininstr.CALL_ADDR address.index.val]⟩
      (Store.decodeStore view code after) ambient) (by intro after reason; trivial)
  · intro prepared p identity empty arguments
    apply WP.spec_mono (call_defined_supported_entry_outcomes memory hooks floats allocator allocation interrupts view code
      prepared store p certified.shape certified.storeSyntax certified.segmentBounds certified.typed certified.supported certified.compiled ambient ambientWf address function signature instanceIndex functionIndex
      args empty identity arguments accepted owned hf hs hw)
    intro out post
    refine ⟨post.1,post.2.1,?_⟩
    intro error rejected
    obtain ⟨inst,compiled,hi,hc,cause⟩ := post.2.2 error rejected
    rcases cause.kind with rfl | rfl | rfl | rfl <;> trivial
  · intro prepared p entered
    obtain ⟨source,invariant,ownedSource,ambientEq,sourceStep⟩ := entered
    let machine : ChosenSupportedMachine emission allowed M P view code (signature.results.val.map Interp.sourceType) :=
      ⟨⟨store,prepared,p,source,0,false,invariant,certified,ownedSource,hostFree⟩,occurrence+1⟩
    apply WP.dspec_mono (chosen_supported_loop_stops memory hooks floats allocator
      (chosen_supported_step_outcomes admissible numericChoice vector language memory hooks floats allocator correct allocation interrupts view laws code compatible _) machine)
    rintro out ⟨state,held,stopped,rfl⟩
    have outcome := chosen_supported_loop_finished memory hooks floats allocator machine state held stopped
    have chosenEntry := Spec.stepH_neutral_chosen admissible vector occurrence sourceStep (by
      simp only [Spec.trapCode,Spec.neutralActive_vals,Spec.neutralActive])
    obtain ⟨fresh,metadata,extension,segments,readback⟩ := outcome.chosen_readback admissible
    refine ⟨metadata.identity,metadata.functions,metadata.types,⟨fresh,metadata,extension,segments⟩,?_,?_⟩
    · intro success
      obtain ⟨values,tags,wellFormed,fits,represented,reductions⟩ := readback success
      refine ⟨values,tags,wellFormed,fits,represented,tags,?_⟩
      simpa only [machine,ambientEq,List.nil_append] using Spec.ChoiceSteps.cons chosenEntry reductions
    · intro error rejected
      rcases (outcome.erases admissible).error_kind rejected with ⟨trap,rfl,allowed⟩ | rfl | rfl | rfl | rfl
      · obtain ⟨_,trapped⟩ := outcome.chosen_trap rejected
        refine ⟨allowed,?_⟩
        simpa only [machine,ambientEq,List.nil_append,finishExecution] using Spec.ChoiceSteps.cons chosenEntry trapped
      all_goals trivial
end Exec.Theorems
