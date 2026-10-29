import Itasca.Runtime.Integration.Execution.World.StepOutcomes
import Itasca.Runtime.Integration.Execution.World.Infinite
import Itasca.Runtime.Integration.Execution.Dispatch.Entry
import Itasca.Runtime.Interp.Invocation.Divergence
import Itasca.Runtime.Interp.Invocation.PrefixDivergence

/-!
A source run from `initial` reaches a configuration whose store decodes a runtime store on which some callback diverges.

Main declarations: `HostCallDiverged` and `invoke_defined_world_infinite_source`. A direct consumer is `Integration.Invocation.Behaves`.
-/

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Interp

/-- A source run from `initial` reaches a configuration whose store decodes a runtime store on
which some callback diverges. -/
def HostCallDiverged {M P : Type} (hooks : runtime.platform.Platform P M) (view : M → Slice U8)
    (initial : config) : Prop :=
  ∃ events code store ambient instrs,
    StepsH initial events ⟨⟨Store.decodeStore view code store,ambient⟩,instrs⟩ ∧ HostDiverges hooks store

theorem invoke_defined_world_infinite_source
 {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.Laws memory hooks floats allocator view) (code : Store.CodeInterpretation)
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (certify : ∀code s,Inv code s → CertifiedSupportedStore view code s)
    (update : ∀code before after,Inv code before → CumulativeStoreMutation view code before after → Inv code after)
    (callbacks : HostLaws hooks view Inv)
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
    Spec.InfiniteSourceWithEvents
      ⟨⟨Store.decodeStore view code store,ambient⟩,vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val]⟩ ∨
    HostCallDiverged hooks view
      ⟨⟨Store.decodeStore view code store,ambient⟩,vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val]⟩ := by
  have certified := certify code store valid
  let entry := fun (after : runtime.store.Store M) (prepared : runtime.interp.Execution) => after=store ∧ ∃source,
    Machine.Execution view code store prepared source
      (signature.results.val.map sourceType) 0 false ∧
    SourceMachine.Ownership.StatefulOwned (Store.ownershipBounds store) source ∧ source.ambient=ambient ∧
    StepH ⟨⟨Store.decodeStore view code store,ambient⟩,vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val]⟩ [] (SourceMachine.decode source)
  have accepted := invoke_divergent_arguments memory hooks floats allocator exec store platform address
    function signature args results owner hf hs divergent
  have reached : ∃after prepared p,entry after prepared ∧
      runtime.interp.invoke_with_loop1 memory hooks floats allocator prepared after p (.Ok ())=.div := by
    apply invoke_prefix_divergent_entry memory hooks floats allocator laws.allocCorrect exec store platform address
      function signature args results owner hf hs accepted (fun value member=>(owned value member).1) entry ?_ ?_ divergent
    · intro prepared p identity empty represented
      apply WP.spec_mono (call_defined_supported_entry memory hooks floats allocator laws.allocCorrect laws.interruptsReturn view code
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
        (world_step_outcomes memory hooks floats allocator view laws Inv certify update callbacks _) ⟨code,machine⟩ valid)
      intro out result
      obtain ⟨finalCode,newValid,fresh,retained,agrees,extension,returned,failed⟩ := result.1
      refine ⟨retained,?_⟩
      intro success
      obtain ⟨values,events,typed,ownedValues,represented,reductions⟩ := returned success
      refine ⟨values,?_,Spec.results_typed_wf typed,?_,represented⟩
      · simpa only [show Compiler.valueType=SourceMachine.valueType from funext value_type_eq_abs] using (SourceMachine.results_type_of_typed typed).symm
      · intro value member
        exact Store.owned_result_fits _ value (ownedValues value member)
  obtain ⟨after,prepared,p,⟨same,source,invariant,ownedSource,ambientEq,sourceStep⟩,bodyDivergent⟩ := reached
  subst after
  let machine : EventfulMachine M P view code (signature.results.val.map sourceType) :=
    ⟨store,prepared,p,source,0,false,invariant,certified,ownedSource⟩
  have first : StepsH _ [] (SourceMachine.decode source) := StepsH.cons sourceStep (StepsH.refl invariant.typed.typed.decode_wf)
  rcases world_loop_infinite memory hooks floats allocator Inv
      (world_step_outcomes memory hooks floats allocator view laws Inv certify update callbacks _) ⟨code,machine⟩ valid bodyDivergent with
    infinite | ⟨count,events,reached,history,diverged⟩
  · exact Or.inl (infinite.prepend first)
  · obtain ⟨n,reductions⟩ := EventfulWorld.history_source (world_recorded_history history)
    refine Or.inr ⟨events,reached.code,reached.machine.store,reached.machine.source.ambient,
      SourceMachine.decodeFrames reached.machine.source.frames (vals reached.machine.source.results),?_,diverged⟩
    have trace := Spec.steps_h_trans first reductions.erase
    simpa only [List.nil_append,SourceMachine.decode,reached.machine.invariant.storeEq] using trace
end Itasca.Runtime.Integration
