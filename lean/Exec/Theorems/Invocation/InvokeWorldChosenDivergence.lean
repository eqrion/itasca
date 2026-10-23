import Exec.Theorems.Composition.Eventful.EventfulWorldTotal
import Exec.Theorems.Composition.World.ChosenWorldTotal
import Exec.Theorems.Composition.World.ChosenWorldDivergence
import Exec.Spec.Choices.NeutralStep
import Exec.Theorems.Progress.EventfulWorldInfinite
import Exec.Theorems.Composition.Supported.SupportedEntry
import Exec.Interp.Invocation.InvokeDivergence
import Exec.Interp.Invocation.InvokePrefixDivergence
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

theorem invoke_defined_world_infinite_chosen {choices : Spec.SourceChoices} (admissible : choices.Admissible)
    (numericChoice : choices.numeric=Spec.firstNumericChoice) (vector : choices.vector=Spec.firstVectorChoice) (occurrence : Nat)
 {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (compatible : GrowthChoicesCompatible memory allocator view choices)
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (certify : ∀code s,Inv code s → CertifiedSupportedStore view code s)
    (update : ∀code before after,Inv code before → CumulativeStoreMutation view code before after → Inv code after)
    (typedStore : ∀ code store,Inv code store → Store_ok (Store.decodeStore view code store))
    (sound : HostWorldChosenSound memory hooks view Inv choices)
    (preserve : ∀ code store, Inv code store →
      ∀ host p args results answer, hooks.call_host p store host args results=.ok answer → FrameStorePrefix store answer.2.2.1)
    (externs : ∀ code store, Inv code store →
      ∀ host p args results answer, hooks.call_host p store host args results=.ok answer → store.externs.length≤answer.2.2.1.externs.length)
    (issued : ∀ code store, Inv code store →
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
    (divergent : runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results=.div) :
    Spec.InfiniteChosenSource choices occurrence
      ⟨⟨Store.decodeStore view code store,ambient⟩,vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val]⟩ := by
  have certified := certify code store valid
  let entry := fun (after : runtime.store.Store M) (prepared : runtime.interp.Execution) => after=store ∧ ∃source,
    StructuredMachine.Execution view code store prepared source
      (signature.results.val.map sourceType) 0 false ∧
    Abs.Ownership.StatefulOwned (Store.ownershipBounds store) source ∧ source.ambient=ambient ∧
    StepH ⟨⟨Store.decodeStore view code store,ambient⟩,vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val]⟩ [] (Abs.decode source)
  have accepted := invoke_divergent_arguments memory hooks floats allocator exec store platform address
    function signature args results owner hf hs divergent
  have reached : ∃after prepared p,entry after prepared ∧
      runtime.interp.invoke_with_loop1 memory hooks floats allocator prepared after p (.Ok ())=.div := by
    apply invoke_prefix_divergent_entry memory hooks floats allocator allocation exec store platform address
      function signature args results owner hf hs accepted (fun value member=>(owned value member).1) entry ?_ ?_ divergent
    · intro prepared p identity empty represented
      apply WP.spec_mono (call_defined_supported_entry memory hooks floats allocator allocation interrupts view code
        prepared store p certified.shape certified.storeSyntax certified.segmentBounds certified.typed certified.supported certified.compiled
        ambient ambientWf address function signature instanceIndex functionIndex args empty identity represented accepted owned hf hs hw)
      intro out effect success
      exact ⟨effect.1,effect.2 success⟩
    · intro after prepared p entered
      obtain ⟨same,source,invariant,ownedSource,ambientEq,sourceStep⟩ := entered
      subst after
      let machine : EventfulMachine M P view code (signature.results.val.map sourceType) :=
        ⟨store,prepared,p,source,0,false,invariant,certified,ownedSource⟩
      apply WP.dspec_mono (world_loop_results memory hooks floats allocator Inv
        (world_step_outcomes memory hooks floats allocator correct allocation interrupts view laws Inv certify update sound.erases preserve externs issued _) ⟨code,machine⟩ valid)
      intro out result
      obtain ⟨finalCode,newValid,fresh,retained,agrees,extension,returned,failed⟩ := result.1
      refine ⟨retained,?_⟩
      intro success
      obtain ⟨values,events,typed,ownedValues,represented,reductions⟩ := returned success
      refine ⟨values,?_,Spec.resultsTyped_wf typed,?_,represented⟩
      · simpa only [show Code.valueType=Abs.valueType from funext valueType_eq_abs] using (Abs.results_type_of_typed typed).symm
      · intro value member
        exact Store.owned_result_fits _ value (ownedValues value member)
  obtain ⟨after,prepared,p,⟨same,source,invariant,ownedSource,ambientEq,sourceStep⟩,bodyDivergent⟩ := reached
  subst after
  let machine : EventfulMachine M P view code (signature.results.val.map sourceType) :=
    ⟨store,prepared,p,source,0,false,invariant,certified,ownedSource⟩
  let selected : ChosenWorld M P view (signature.results.val.map sourceType) := ⟨⟨code,machine⟩,occurrence+1⟩
  have infinite := chosen_world_loop_infinite memory hooks floats allocator Inv
    (chosen_world_step_outcomes admissible numericChoice vector memory hooks floats allocator correct allocation interrupts
      view laws compatible Inv certify update typedStore sound preserve externs issued _) selected valid bodyDivergent
  have chosenEntry := Spec.stepH_neutral_chosen admissible vector occurrence sourceStep (by
    simp only [Spec.trapCode,Spec.neutralActive_vals,Spec.neutralActive])
  exact Spec.InfiniteChosenSource.prepend_step chosenEntry infinite
end Exec.Theorems
