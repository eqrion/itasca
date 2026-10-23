import Exec.Interp.Invocation.InvokeRecordingErasure
import Exec.Theorems.Invocation.InvokeWorldChosenRecorded
import Exec.Theorems.Invocation.InvokeWorldChosenDivergence
import Exec.Theorems.Invocation.InvokeWorldNoBoundary
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}

private theorem returning_of_not_div {T : Type} {computation : Result T} {post : T → Prop}
    (safe : computation ⦃ post ⦄div) (notdiv : computation≠.div) : ∃out,computation=.ok out ∧ post out := by
  generalize answerEq : computation=answer at safe notdiv ⊢
  cases safe with
  | ret held => exact ⟨_,rfl,held⟩
  | div => exact False.elim (notdiv rfl)

/-- Actual public Wasm invocation matches one terminating selected run, including
its exact recorder events and final interpreted store. Resource assumptions
concern source capacities, independent reserves and callback behavior. -/
theorem invoke_defined_world_chosen_matches {choices : Spec.SourceChoices} (admissible : choices.Admissible)
    (numericChoice : choices.numeric=Spec.firstNumericChoice) (vector : choices.vector=Spec.firstVectorChoice) (occurrence : Nat)
    [∀ compiled, StructuredMachine.FloatHeads (emission compiled)]
    [∀ compiled, StructuredMachine.OrdinaryHeads (emission compiled)]
    [∀ compiled, StructuredMachine.StatefulProjection (emission compiled) compiled.indirect.val]
    [∀ compiled, StructuredMachine.IndirectProjection (emission compiled) compiled.indirect.val]
    [∀ compiled, StructuredMachine.SimdProjection (emission compiled) compiled.simd.val compiled.v128_pool.val]
    [∀ compiled, StructuredMachine.TypedSelectHeads (emission compiled)]
    [∀ compiled, StructuredMachine.SupportedHeads (emission compiled)]
    [∀ compiled, StructuredMachine.ErasedHeads (emission compiled)]
    [∀ compiled, StructuredMachine.RecordingHeads (emission compiled)]
    (language : Abs.Supported.Language allowed) {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (compatible : GrowthChoicesCompatible memory allocator view choices)
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (certify : ∀ c s,Inv c s → CertifiedSupportedStore emission allowed view c s)
    (update : ∀ c before after,Inv c before → CumulativeStoreMutation view c before after → Inv c after)
    (typedStore : ∀ code store,Inv code store → Store_ok (Store.decodeStore view code store))
    (sound : HostWorldChosenSound memory hooks view Inv choices)
    (preserve : ∀ c store, Inv c store →
      ∀ host p args results answer, hooks.call_host p store host args results=.ok answer → FrameStorePrefix store answer.2.2.1)
    (externs : ∀ c store, Inv c store →
      ∀ host p args results answer, hooks.call_host p store host args results=.ok answer → store.externs.length≤answer.2.2.1.externs.length)
    (issued : ∀ c store, Inv c store →
      ∀ host p args results answer, hooks.call_host p store host args results=.ok answer →
      ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : Inv code store)
    (ambient : frame) (ambientWf : wf_frame ambient)
    (address : runtime.FuncAddr) (function : runtime.store.FuncInst)
    (signature : Itasca.types.FuncType) (instanceIndex functionIndex : Usize)
    (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (owner : address.store = store.id)
    (owned : ∀ value ∈ args.val, Store.ValueInStore store value)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (hw : function.code = .Wasm instanceIndex functionIndex)
    (accepted : runtime.interp.check_values memory store args (alloc.vec.Vec.deref signature.params) = .ok (.Ok ()))
    (capacities : ∀c store,Inv c store → Store.FunctionCapacities c store) {valueLimit frameLimit : Nat}
    (floors : ∀c store,Inv c store → valueLimit≤store.limits.max_values.val ∧ frameLimit≤store.limits.max_frames.val)
    (signatureFits : signatureWords (Store.decodeFuncType signature)≤valueLimit)
    (entryCapacity : ∀words,SourceCanonicalFunctionCapacity (Store.decodeStore view code store) address.index.val words → words≤valueLimit)
    (positiveFrames : 0<frameLimit)
    (resources : ChosenWorldResources choices occurrence
      ⟨⟨Store.decodeStore view code store,ambient⟩,vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val]⟩ valueLimit frameLimit)
    (available : Platform.AllocationAvailable allocator (2*Usize.max))
    (continuing : ∀ before after,hooks.interrupt before≠.ok (.Terminate,after)) (noOverflow : NoHostStackOverflow hooks Inv)
    {events : List HostEvent} {target : config}
    (run : Spec.ChoiceSteps choices occurrence
      ⟨⟨Store.decodeStore view code store,ambient⟩,vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val]⟩ events target)
    (terminal : Spec.SourceTerminal target) :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results
      ⦃ out => ∃afterCode,Inv afterCode out.2.2.1 ∧ Store_ok (Store.decodeStore view afterCode out.2.2.1) ∧
        FrameStorePrefix store out.2.2.1 ∧ Store.CodeAgreesOn store code afterCode ∧
        Extend_store (Store.decodeStore view code store) (Store.decodeStore view afterCode out.2.2.1) ∧
        recordedInvokeWith memory hooks floats allocator exec store platform address args results []=.ok (out,events) ∧
        match out.1 with
        | .Ok _ => target=⟨⟨Store.decodeStore view afterCode out.2.2.1,ambient⟩,vals (out.2.2.2.2.val.map sourceValue)⟩ ∧
            (∀value∈out.2.2.2.2.val,Store.ValueInStore out.2.2.1 value)
        | .Err (.Trap _) => target=⟨⟨Store.decodeStore view afterCode out.2.2.1,ambient⟩,[.TRAP]⟩
        | .Err _ => False ⦄ := by
  have notdiv : runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results≠.div := by
    intro divergent
    exact Spec.chosen_terminating_no_infinite admissible run terminal
      (invoke_defined_world_infinite_chosen admissible numericChoice vector occurrence language memory hooks floats allocator correct allocation
        interrupts view laws code compatible Inv certify update typedStore sound preserve externs issued exec store platform valid ambient ambientWf
        address function signature instanceIndex functionIndex args results owner owned hf hs hw divergent)
  have selected := invoke_defined_world_chosen_recorded_outcomes admissible numericChoice vector occurrence language memory hooks floats allocator
    correct allocation interrupts view laws code compatible Inv certify update typedStore sound preserve externs issued exec store platform valid
    ambient ambientWf address function signature instanceIndex functionIndex args results owner owned hf hs hw accepted
  have safe := Platform.Recording.erase_dspec _ _ _ (recordedInvokeWith_erase memory hooks floats allocator exec store platform address args results []) selected
  obtain ⟨out,actual,nativeEvents,graph,afterCode,fresh,kept,agrees,extension,success,failure⟩ := returning_of_not_div safe notdiv
  have noBoundary := invoke_defined_world_no_boundary admissible vector occurrence memory hooks floats allocator allocation interrupts view code Inv
    certify capacities exec store platform valid ambient ambientWf address function signature instanceIndex functionIndex args results owner owned hf hs hw accepted
    (chosen_world_step_outcomes admissible numericChoice vector language memory hooks floats allocator correct allocation interrupts view laws compatible
      Inv certify update typedStore sound preserve externs issued _) floors signatureFits entryCapacity positiveFrames resources available continuing noOverflow
  rw [actual,WP.dspec_ok] at noBoundary
  rw [actual,WP.spec_ok]
  refine ⟨afterCode,fresh,typedStore _ _ fresh,kept,agrees,extension,?_⟩
  cases status : out.1 with
  | Ok unit =>
    obtain ⟨typed,sourceOwned,source,rawOwned⟩ := success status
    obtain ⟨sameEvents,sameTarget⟩ := Spec.chosen_terminal_unique admissible run terminal _ _ source (.values _ _)
    exact ⟨by simpa only [sameEvents] using graph,by simpa only [status] using And.intro sameTarget rawOwned⟩
  | Err error =>
    obtain ⟨trap,rfl⟩ := noBoundary error status
    obtain ⟨count,source⟩ := failure (.Trap trap) status
    obtain ⟨sameEvents,sameTarget⟩ := Spec.chosen_terminal_unique admissible run terminal _ _ source.erase_count (.trap _)
    exact ⟨by simpa only [sameEvents] using graph,by simpa only [status] using sameTarget⟩
end Exec.Theorems
