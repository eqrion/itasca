import Exec.Theorems.Invocation.InvokeWorldChosenOutcomes
import Exec.Theorems.Composition.World.ChosenWorldResourceLoop
import Exec.Theorems.Api.InvocationPrimitiveResources
import Exec.Interp.Calls.ResourcesAdequate
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Spec Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}

/-- Internal public-call composition: independent source and primitive resource
conditions exclude exhaustion and interruption, including result readback. The
native dispatcher discharges `steps` in the exported matching theorem. -/
theorem invoke_defined_world_no_boundary {choices : SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=firstVectorChoice) (occurrence : Nat) {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (interrupts : ∀p,hooks.interrupt p ⦃ _=>True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (certify : ∀c store,Inv c store → CertifiedSupportedStore emission allowed view c store)
    (capacities : ∀c store,Inv c store → Store.FunctionCapacities c store)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P) (valid : Inv code store)
    (ambient : frame) (ambientWf : wf_frame ambient) (address : runtime.FuncAddr) (function : runtime.store.FuncInst)
    (signature : Itasca.types.FuncType) (instanceIndex functionIndex : Usize)
    (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value) (owner : address.store=store.id)
    (owned : ∀value∈args.val,Store.ValueInStore store value)
    (hf : store.funcs.val[address.index.val]?=some function) (hs : store.types.val[function.signature.val]?=some signature)
    (hw : function.code=.Wasm instanceIndex functionIndex)
    (accepted : runtime.interp.check_values memory store args signature.params.deref=.ok (.Ok ()))
    (steps : ChosenWorldStepOutcomes (emission:=emission) (allowed:=allowed) choices memory hooks floats allocator view
      (signature.results.val.map sourceType) Inv)
    {valueLimit frameLimit : Nat}
    (floors : ∀c store,Inv c store → valueLimit≤store.limits.max_values.val ∧ frameLimit≤store.limits.max_frames.val)
    (signatureFits : signatureWords (Store.decodeFuncType signature)≤valueLimit)
    (entryCapacity : ∀words,SourceCanonicalFunctionCapacity (Store.decodeStore view code store) address.index.val words → words≤valueLimit)
    (positiveFrames : 0<frameLimit)
    (resources : ChosenWorldResources choices occurrence
      ⟨⟨Store.decodeStore view code store,ambient⟩,vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val]⟩ valueLimit frameLimit)
    (available : Platform.AllocationAvailable allocator (2*Usize.max))
    (continuing : ∀ before after,hooks.interrupt before≠.ok (.Terminate,after)) (noOverflow : NoHostStackOverflow hooks Inv) :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results
      ⦃ out => ∀error,out.1=.Err error → ∃trap,error=.Trap trap ⦄div := by
  have certified := certify code store valid
  have initialFloors := floors code store valid
  let entry := fun (after : runtime.store.Store M) (prepared : runtime.interp.Execution) => after=store ∧ ∃source,
    StructuredMachine.Execution emission (Abs.SupportedState allowed) view code store prepared source
      (signature.results.val.map sourceType) 0 false ∧
    Abs.Ownership.StatefulOwned (Store.ownershipBounds store) source ∧ source.ambient=ambient ∧
    StepH ⟨⟨Store.decodeStore view code store,ambient⟩,vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val]⟩ [] (Abs.decode source)
  apply WP.dspec_mono (invoke_with_prefix_owned_causes_composition_mode memory hooks floats allocator true allocation exec store platform
    address function signature args results owner hf hs accepted (fun value member=>(owned value member).1)
    entry (FrameStorePrefix store) (.refl _) (fun _ _=>True) (fun _ error=>∃trap,error=.Trap trap) ?_ ?_ ?_ ?_)
  · intro out post
    exact post.2.2
  · intro error cause
    exact False.elim (invocation_resource_cause_impossible available (signatureFits.trans initialFloors.1) cause)
  · intro after values kept satisfied refused
    obtain ⟨n,amount,refused⟩ := refused
    exact False.elim (reserve_ne_refusal_of_universal_bound available results n refused)
  · intro prepared p identity empty represented
    apply WP.spec_mono (call_defined_supported_entry_outcomes memory hooks floats allocator allocation interrupts view code
      prepared store p certified.shape certified.storeSyntax certified.segmentBounds certified.typed certified.supported certified.compiled
      ambient ambientWf address function signature instanceIndex functionIndex args empty identity represented accepted owned hf hs hw)
    intro out outcome
    refine ⟨?_,?_,?_⟩
    · simpa only [outcome.1] using (FrameStorePrefix.refl store)
    · intro success
      exact ⟨outcome.1,outcome.2.1 success⟩
    · intro error failed
      obtain ⟨inst,compiled,hi,hc,cause⟩ := outcome.2.2 error failed
      obtain ⟨words,capacity,bounded⟩ := function_canonical_capacity_decoded view code store (capacities code store valid) certified.typed
        address function instanceIndex functionIndex inst compiled hf hw hi hc
      have sourceBound := entryCapacity words capacity
      have frames : prepared.frames.length=0 := by simp only [alloc.vec.Vec.length,empty,List.length_nil]
      exact False.elim (cause.impossible_of_resources available continuing (by omega) (by scalar_tac) (by scalar_tac) (by scalar_tac))
  · intro after prepared p entered
    obtain ⟨same,source,invariant,ownedSource,ambientEq,sourceStep⟩ := entered
    subst after
    have chosenEntry := stepH_neutral_chosen admissible vector occurrence sourceStep (by
      simp only [trapCode,neutralActive_vals,neutralActive])
    have sourcePrefix : ChosenStepsN choices occurrence 1
        ⟨⟨Store.decodeStore view code store,ambient⟩,vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val]⟩ [] (Abs.decode source) := by
      simpa only [List.nil_append] using ChosenStepsN.cons chosenEntry (ChosenStepsN.refl (occurrence+1) invariant.typed.typed.decode_wf)
    let initial : ChosenWorld emission allowed M P view (signature.results.val.map sourceType) :=
      ⟨⟨code,⟨store,prepared,p,source,0,false,invariant,certified,ownedSource⟩⟩,occurrence+1⟩
    have bodyResources : ChosenWorldResources choices initial.occurrence (Abs.decode source) valueLimit frameLimit := by
      intro count events next suffix
      apply resources (1+count) events next
      simpa only [List.nil_append] using sourcePrefix.trans suffix
    apply WP.dspec_mono (chosen_world_loop_no_boundary memory hooks floats allocator Inv steps initial valid capacities floors
      bodyResources available continuing noOverflow)
    rintro out ⟨result,onlyTraps⟩
    obtain ⟨afterCode,fresh,certified,kept,agrees,extension,success,failed⟩ := result
    refine ⟨kept,kept,?_,onlyTraps⟩
    intro status
    obtain ⟨values,events,typed,ownedValues,represented,count,source⟩ := success status
    refine ⟨values,?_,resultsTyped_wf typed,?_,represented,True.intro⟩
    · simpa only [show Code.valueType=Abs.valueType from funext valueType_eq_abs] using (Abs.results_type_of_typed typed).symm
    · intro value member
      exact Store.owned_result_fits _ value (ownedValues value member)
end Exec.Theorems
