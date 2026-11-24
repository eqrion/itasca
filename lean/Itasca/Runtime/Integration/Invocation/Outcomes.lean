import Itasca.Runtime.Interp.Recording
import Itasca.Runtime.Integration.Execution.Certificates
import Itasca.Runtime.Integration.Api.CreationAndGrowth
import Itasca.Runtime.Integration.Execution.Resources.SourceDemand
import Itasca.Runtime.Integration.Execution.History.State
import Itasca.Runtime.Integration.Execution.Dispatch.Host
import Itasca.Runtime.Integration.Execution.Resources.InvocationErrors
import Itasca.Runtime.Integration.Execution.Dispatch.EntryOutcomes
import Itasca.Runtime.Integration.Host.HostRecordingBoundary
import Itasca.Runtime.Integration.Host.HostCallContext
import Itasca.Runtime.Interp.Relations.StackPreservation
import Itasca.Runtime.Integration.Host.HostIndirectSelected
import Itasca.Runtime.Integration.Execution.Ownership.ReferenceShape
import Itasca.Runtime.Integration.Execution.Ownership.Publication
import Itasca.Runtime.Interp.Machine.Calls.IndirectOperands
import Itasca.Runtime.Integration.Execution.Dispatch.Normalization
import Itasca.Runtime.Interp.Relations.StepActive
import Itasca.Runtime.Integration.Host.HostDispatchCauses
import Itasca.Runtime.Interp.Invocation.Recording
import Itasca.Runtime.Integration.Api.GrowthAndValueSupport
import Itasca.Runtime.Spec.PrimitiveOperations
import Itasca.Runtime.Integration.Api.GrowthAndHostResourceCauses
import Itasca.Runtime.Store.Invariant.HostSignature
import Itasca.Runtime.Integration.Execution.Dispatch.IndirectBoundary
import Itasca.Runtime.Integration.Execution.Resources.SourceCauses
import Itasca.Runtime.Integration.Host.HostIndirectStructuredWorld
import Itasca.Runtime.Interp.Relations.ResourceCausesAndArgumentErrors
import Itasca.Runtime.Integration.Execution.World.NonhostStep
import Itasca.Runtime.Integration.Execution.Resources.WorldLoop

/-!
Proofs for Runtime / Integration / Invocation.

This module collects Outcomes, DivergenceAndHostOutcomes, DefinedResources.
Each section documents its contracts and consumers.
-/

/-! ## Outcomes -/

section

open Itasca.Representation

/-! ## HostResources -/

section

/-!
Recorded host invocation outcomes and their source resource evidence.

Main declarations: `InitialHostInvocationCause.source_resources` and `invoke_host_world_recorded_resources`.
-/

namespace Itasca.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Interp

theorem InitialHostInvocationCause.source_resources {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Representation.CodeInterpretation}
    {exec : runtime.interp.Execution} {store after : runtime.store.Store M}
    {ambient : frame} {address : runtime.FuncAddr} {identity : U64}
    {error : runtime.ExecError} {signature : Itasca.wasm_types.FuncType} {args : Slice runtime.Value} {results : alloc.vec.Vec runtime.Value}
    (cause : InitialHostInvocationCause memory hooks floats allocator view code exec store ambient address identity signature args results after error) :
    InitialHostSourceResourceCause hooks allocator store after identity signature error := by
  cases error with
  | Terminated => exact cause.interrupted
  | Exhausted reason =>
    cases reason with
    | Values => exact cause.source_values
    | Allocation => exact cause.source_allocation
    | CallStack => exact cause.host_overflow
    | Objects => exact cause.no_objects
  | _ => trivial

theorem invoke_host_world_recorded_resources {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Representation.CodeInterpretation)
    (invariant : Representation.CodeInterpretation → runtime.store.Store M → Prop)
    (shape : ∀ c s, invariant c s → Representation.Shape view s)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : invariant code store) (sourceWf : wf_store (Representation.decodeStore view code store))
    (ambient : frame) (ambientWf : wf_frame ambient)
    (address : runtime.FuncAddr) (function : runtime.store.FuncInst) (identity : U64)
    (signature : Itasca.wasm_types.FuncType) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (owner : address.store = store.id)
    (functionAt : store.funcs.val[address.index.val]? = some function)
    (host : function.code = .Host identity)
    (signatureAt : store.types.val[function.signature.val]? = some signature)
    (owned : ∀ value ∈ args.val, Store.ValueInStore store value)
    (accepted : runtime.interp.check_values memory store args (alloc.vec.Vec.deref signature.params) = .ok (.Ok ()))
    (callback : ∀ p arguments defaults,
      hooks.call_host p store identity arguments defaults ⦃ answer => ∃ afterCode,
        Store.CodeAgreesOn store code afterCode ∧ invariant afterCode answer.2.2.1 ∧
        Extend_store (Representation.decodeStore view code store) (Representation.decodeStore view afterCode answer.2.2.1) ∧
        Store_ok (Representation.decodeStore view afterCode answer.2.2.1) ⦄div)
    (retains : HostRetention hooks store identity) :
    Computation.DivSpec (HostDiverges hooks store) (recordedInvokeWith memory hooks floats allocator exec store platform address args results [])
      fun (out,trace) => ∃ afterCode,
      (invariant afterCode out.2.2.1 ∧ Store.CodeAgreesOn store code afterCode ∧ Store.MetadataExtended store out.2.2.1 ∧
        Extend_store (Representation.decodeStore view code store) (Representation.decodeStore view afterCode out.2.2.1) ∧
        store.externs.length ≤ out.2.2.1.externs.length) ∧
      (out.1 = .Ok () →
        ResultsTyped (Representation.decodeStore view afterCode out.2.2.1) (signature.results.val.map Itasca.Translation.valueType)
          (out.2.2.2.2.val.map sourceValue) ∧
        SourceMachine.Ownership.ValuesOwned (Store.ownershipBounds out.2.2.1) (out.2.2.2.2.val.map sourceValue) ∧
        StepsH ⟨⟨Representation.decodeStore view code store,ambient⟩, vals (args.val.map sourceValue) ++ [.CALL_ADDR address.index.val]⟩
          trace
          ⟨⟨Representation.decodeStore view afterCode out.2.2.1,ambient⟩, vals (out.2.2.2.2.val.map sourceValue)⟩ ∧
        (∀ value ∈ out.2.2.2.2.val, Store.ValueInStore out.2.2.1 value)) ∧
      (∀ error, out.1 = .Err error → EventfulInvocationError
        ⟨⟨Representation.decodeStore view code store,ambient⟩, vals (args.val.map sourceValue) ++ [.CALL_ADDR address.index.val]⟩
        trace (Representation.decodeStore view afterCode out.2.2.1) ambient error ∧
        InitialHostSourceResourceCause hooks allocator store out.2.2.1 identity signature error) := by
  have arguments := checked_arguments_typed memory view code store sourceWf args signature.params accepted owned
  have initialWf := Spec.host_call_wf (fa:=address.index.val) sourceWf ambientWf arguments
  have argsOwned := Store.source_values_owned store args.val owned
  let retained := fun after => Store.MetadataExtended store after ∧ store.externs.length ≤ after.externs.length
  let property := fun after values trace => ∃ afterCode,
    invariant afterCode after ∧ Store.CodeAgreesOn store code afterCode ∧
    Extend_store (Representation.decodeStore view code store) (Representation.decodeStore view afterCode after) ∧
    ResultsTyped (Representation.decodeStore view afterCode after) (signature.results.val.map Itasca.Translation.valueType) values ∧
    SourceMachine.Ownership.ValuesOwned (Store.ownershipBounds after) values ∧
    StepsH ⟨⟨Representation.decodeStore view code store,ambient⟩,vals (args.val.map sourceValue) ++ [.CALL_ADDR address.index.val]⟩
      trace
      ⟨⟨Representation.decodeStore view afterCode after,ambient⟩,vals values⟩
  let errors := fun (after : runtime.store.Store M) (error : runtime.ExecError) (trace : List HostEvent) => ∃ afterCode,
    invariant afterCode after ∧ Store.CodeAgreesOn store code afterCode ∧
    Extend_store (Representation.decodeStore view code store) (Representation.decodeStore view afterCode after) ∧
    EventfulInvocationError
      ⟨⟨Representation.decodeStore view code store,ambient⟩, vals (args.val.map sourceValue) ++ [.CALL_ADDR address.index.val]⟩
      trace (Representation.decodeStore view afterCode after) ambient error ∧
      InitialHostSourceResourceCause hooks allocator store after identity signature error
  let entry := fun (after : runtime.store.Store M) (entered : runtime.interp.Execution) (trace : List HostEvent) => retained after ∧ entered.frames.val = [] ∧
    ∃ values, ValuesAt entered.slots.val 0 values ∧ property after values trace
  refine Computation.DivSpec.mono (recorded_invoke_with_prefix_owned_causes_composition_mode memory hooks floats allocator (HostDiverges hooks store) allocation exec store platform
    address function signature args results [] owner functionAt signatureAt accepted
    (fun value member => (owned value member).1) entry retained
    ⟨.refl _,Nat.le_refl _⟩ property errors ?_ ?_ ?_ ?_) ?_
  · intro error cause
    have causal : InitialHostInvocationCause memory hooks floats allocator view code exec store ambient address identity signature args results store error := Or.inl ⟨rfl,cause⟩
    refine ⟨code,valid,(by intro index inst found fn; rfl),Spec.extend_store_refl _ sourceWf,?_,causal.source_resources⟩
    cases error <;> try simp only [InvocationResourceCause] at cause
    rename_i limit
    exact ⟨_,StepsH.refl initialWf⟩
  · intro after values trace kept satisfied refused
    obtain ⟨afterCode,fresh,agrees,extension,typed,ownership,source⟩ := satisfied
    refine ⟨afterCode,fresh,agrees,extension,⟨vals values,source⟩,Or.inr (Or.inr ?_)⟩
    obtain ⟨n,amount,refusal⟩ := refused
    refine ⟨results,n,?_,refusal⟩
    simp only [List.length_map]
    simp only [alloc.vec.Vec.length] at amount
    omega
  · intro prepared p executionId empty represented
    rcases (call_host_source_retained_world memory hooks floats allocator allocation interrupts view code invariant shape
        prepared store p valid address 0#usize ambient ambientWf function identity signature functionAt host signatureAt
        (args.val.map sourceValue) (by simpa only [show Representation.valueType=SourceMachine.valueType from funext value_type_eq_abs] using (SourceMachine.results_type_of_typed arguments).symm) arguments
        (Spec.results_typed_wf arguments) (fun value member => Store.owned_result_fits store value (argsOwned value member))
        represented sourceWf callback retains).imp_exists with
      ⟨called,actual,afterCode,agrees,fresh,kept,extension,count,effect,causes,_boundary⟩ | ⟨actual,diverged⟩
    swap
    · simp only [recordedCall,Platform.Recording.run,actual,bind_div]
      exact .div _ diverged
    have sameDecode := Store.decode_store_code_agrees view agrees
    have recorded := (recorded_call_returned memory hooks floats allocator prepared store p address 0#usize [] called (hostCallEvents address called)).mpr
      ⟨actual,by simp only [List.nil_append,call_host_events_host functionAt host]⟩
    rw [recorded,Computation.DivSpec.ok_iff]
    refine ⟨⟨kept,count⟩,?_,?_⟩
    · intro success
      rcases effect with ⟨error,status,_,_⟩ | ⟨effect,typed⟩
      · rw [success] at status; cases status
      · obtain ⟨typed,ownedResults⟩ := typed success
        refine ⟨⟨kept,count⟩,?_,called.2.1.host_results.val.map sourceValue,?_,afterCode,fresh,agrees,extension,typed,ownedResults,?_⟩
        · exact congrArg alloc.vec.Vec.val effect.2.1 |>.trans empty
        · rcases effect.2.2.2.2 with good | bad
          · exact good.2.1
          · rcases bad.1 with bad | bad <;> rw [success] at bad <;> cases bad
        · simpa only [hostCallResultConfig,success,sameDecode] using
            effect.events view afterCode store ambient address (args.val.map sourceValue) 0#usize prepared called
    · intro error rejected
      have causal : InitialHostInvocationCause memory hooks floats allocator view code exec store ambient address identity signature args results called.2.2.1 error :=
        Or.inr (Or.inr ⟨prepared,p,called,executionId,empty,represented,actual,rejected,rfl,causes⟩)
      refine ⟨afterCode,fresh,agrees,extension,?_,causal.source_resources⟩
      rcases effect with ⟨early,status,cause,same⟩ | ⟨effect,typed⟩
      · have eq : early=error := by simpa only [rejected,core.result.Result.Err.injEq] using status.symm
        subst early
        have kind := cause.error
        cases error <;> simp only [HostPreparationError] at kind
        case Exhausted limit =>
          cases limit <;> simp only at kind
          all_goals simpa only [EventfulInvocationError,hostCallEvents,rejected,same,sameDecode] using
            (show ∃ body, StepsH ⟨⟨Representation.decodeStore view code store,ambient⟩,vals (args.val.map sourceValue) ++ [.CALL_ADDR address.index.val]⟩ [] ⟨⟨Representation.decodeStore view code store,ambient⟩,body⟩ from
              ⟨_,StepsH.refl initialWf⟩)
        case Terminated =>
          simpa only [EventfulInvocationError,hostCallEvents,rejected,same,sameDecode] using
            (show ∃ body, StepsH ⟨⟨Representation.decodeStore view code store,ambient⟩,vals (args.val.map sourceValue) ++ [.CALL_ADDR address.index.val]⟩ [] ⟨⟨Representation.decodeStore view code store,ambient⟩,body⟩ from
              ⟨_,StepsH.refl initialWf⟩)
      · have source := effect.events view afterCode store ambient address (args.val.map sourceValue) 0#usize prepared called
        rcases effect.2.2.2.2 with good | bad
        · rw [rejected] at good
          cases good.1
        · obtain ⟨failure,_,footprint⟩ := bad
          rcases failure with trapped | exhausted
          · have eq : error=.Trap .Host := by simpa only [rejected,core.result.Result.Err.injEq] using trapped
            subst error
            simpa only [EventfulInvocationError,hostCallResultConfig,rejected,sameDecode] using source
          · have eq : error=.Exhausted .CallStack := by simpa only [rejected,core.result.Result.Err.injEq] using exhausted
            subst error
            refine ⟨[.TRAP],?_⟩
            simpa only [hostCallResultConfig,rejected,sameDecode] using source
  · intro after entered p trace enteredProof
    obtain ⟨kept,empty,values,represented,afterCode,fresh,agrees,extension,typed,ownedResults,source⟩ := enteredProof
    have stopped : ¬ActiveExecution (entered,after,p,.Ok ()) := by
      simp [ActiveExecution,empty,alloc.vec.Vec.length]
    rw [recorded_invoke_loop_stopped memory hooks floats allocator (entered,after,p,.Ok ()) stopped trace]
    simp only [Computation.DivSpec.ok_iff,finishExecution]
    exact ⟨kept.1,kept,fun _ => ⟨values,(by simpa only [show Representation.valueType=SourceMachine.valueType from funext value_type_eq_abs] using (SourceMachine.results_type_of_typed typed).symm),Spec.results_typed_wf typed,
      fun value member => Store.owned_result_fits after value (ownedResults value member),represented,afterCode,fresh,agrees,extension,typed,ownedResults,source⟩,
      fun error impossible => by cases impossible⟩
  · rintro ⟨out,trace⟩ ⟨kept,success,errors⟩
    cases status : out.1 with
    | Ok unit =>
      cases unit
      obtain ⟨⟨afterCode,fresh,agrees,extension,typed,ownedValues,source⟩,owners⟩ := success status
      refine ⟨afterCode,⟨fresh,agrees,kept.1,extension,kept.2⟩,?_,?_⟩
      · intro _
        exact ⟨typed,ownedValues,source,fun value member =>
          owned_source_value_in_store out.2.2.1 value (owners value member)
            (ownedValues (sourceValue value) (List.mem_map.mpr ⟨value,member,rfl⟩))⟩
      · intro error impossible
        rw [status] at impossible
        cases impossible
    | Err error =>
      obtain ⟨afterCode,fresh,agrees,extension,source⟩ := errors error status
      refine ⟨afterCode,⟨fresh,agrees,kept.1,extension,kept.2⟩,?_,?_⟩
      · intro impossible
        rw [status] at impossible
        cases impossible
      · intro reported failed
        have equal : error=reported := by simpa only [status,core.result.Result.Err.injEq] using failed
        subst reported
        exact source
end Itasca.Integration

end

/-! ## Outcomes -/

section

/-! Shared public invocation outcomes and erasure. These predicates retain a
single final code interpretation and sit below the public API constructions. -/
namespace Itasca.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Interp

theorem InvocationRejected.kind {M : Type} {memory : runtime.platform.MemoryBuffer M}
    {store : runtime.store.Store M} {address : runtime.FuncAddr} {args : Slice runtime.Value}
    {error : runtime.ExecError} (rejected : InvocationRejected memory store address args error) :
    error=.BadArguments ∨ error=.WrongStore := by
  rcases rejected with ⟨_,rfl⟩ | ⟨function,signature,_,_,checked⟩
  · exact Or.inr rfl
  · exact check_values_error_kind memory store args _ error checked

theorem ExecutableWorldRecordedOutcome.of_executed {M P : Type}
    {memory : runtime.platform.MemoryBuffer M} {address : runtime.FuncAddr} {args : Slice runtime.Value}
    {view : M → Slice U8} {code afterCode : Representation.CodeInterpretation} {before : runtime.store.Store M}
    {exec : runtime.interp.Execution} {platform : P} {results : alloc.vec.Vec runtime.Value}
    {initial : config} {result : core.result.Result Unit runtime.ExecError}
    {execution : runtime.interp.Execution} {after : runtime.store.Store M}
    {nextPlatform : P} {returned : alloc.vec.Vec runtime.Value} {events : List HostEvent}
    (agrees : Store.CodeAgreesOn before code afterCode)
    (retained : ExecutableInv view afterCode after ∧ Store.MetadataExtended before after ∧
      Extend_store (Representation.decodeStore view code before) (Representation.decodeStore view afterCode after))
    (success : result=.Ok () → (StepsH initial events
      ⟨⟨Representation.decodeStore view afterCode after,Spec.invocationFrame⟩,vals (returned.val.map sourceValue)⟩) ∧
      (∀value∈returned.val,Store.ValueInStore after value))
    (failure : ∀error,result=.Err error →
      EventfulInvocationError initial events (Representation.decodeStore view afterCode after) Spec.invocationFrame error) :
    ExecutableWorldRecordedOutcome memory view code before exec platform address args results initial result execution after nextPlatform returned events := by
  refine ⟨afterCode,agrees,retained.1,retained.2.1,retained.2.2,?_,success,fun error failed=>Or.inr (failure error failed)⟩
  cases status : result with
  | Ok value =>
    cases value
    exact ⟨_,(success status).1⟩
  | Err error =>
    have outcome := failure error status
    obtain ⟨body,steps⟩ := outcome.reachable
    exact ⟨body,steps⟩

end Itasca.Integration

end

end

/-! ## DivergenceAndHostOutcomes -/

section

open Itasca.Representation

/-!
# Divergence And Host Outcomes

Defined divergence and host outcomes construct invocation behavior with the corresponding retained world interpretation.
-/

/-! ## DefinedDivergence -/

section

/-!
A source run from `initial` reaches a configuration whose store decodes a runtime store on which some callback diverges.

Main declarations: `HostCallDiverged` and `invoke_defined_world_infinite_source`.
-/

namespace Itasca.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Interp

theorem invoke_defined_world_infinite_source
 {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.Laws memory hooks floats allocator view) (code : Representation.CodeInterpretation)
    (Inv : Representation.CodeInterpretation → runtime.store.Store M → Prop)
    (certify : ∀code s,Inv code s → CertifiedSupportedStore view code s)
    (update : ∀code before after,Inv code before → CumulativeStoreMutation view code before after → Inv code after)
    (callbacks : HostLaws hooks view Inv)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : Inv code store)
    (ambient : frame) (ambientWf : wf_frame ambient)
    (address : runtime.FuncAddr) (function : runtime.store.FuncInst)
    (signature : Itasca.wasm_types.FuncType) (instanceIndex functionIndex : Usize)
    (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (owner : address.store = store.id)
    (owned : ∀ value ∈ args.val, Store.ValueInStore store value)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (hw : function.code = .Wasm instanceIndex functionIndex)
    (divergent : runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results=.div) :
    Spec.InfiniteSourceWithEvents
      ⟨⟨Representation.decodeStore view code store,ambient⟩,vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val]⟩ ∨
    HostCallDiverged hooks view
      ⟨⟨Representation.decodeStore view code store,ambient⟩,vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val]⟩ := by
  have certified := certify code store valid
  let entry := fun (after : runtime.store.Store M) (prepared : runtime.interp.Execution) => after=store ∧ ∃source,
    Machine.Execution view code store prepared source
      (signature.results.val.map Itasca.Translation.valueType) 0 false ∧
    SourceMachine.Ownership.StatefulOwned (Store.ownershipBounds store) source ∧ source.ambient=ambient ∧
    StepH ⟨⟨Representation.decodeStore view code store,ambient⟩,vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val]⟩ [] (SourceMachine.decode source)
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
      let machine : EventfulMachine M P view code (signature.results.val.map Itasca.Translation.valueType) :=
        ⟨store,prepared,p,source,0,false,invariant,certified,ownedSource⟩
      apply WP.dspec_mono (world_loop_results memory hooks floats allocator Inv
        (world_step_outcomes memory hooks floats allocator view laws Inv certify update callbacks _) ⟨code,machine⟩ valid)
      intro out result
      obtain ⟨finalCode,newValid,fresh,retained,agrees,extension,returned,failed⟩ := result.1
      refine ⟨retained,?_⟩
      intro success
      obtain ⟨values,events,typed,ownedValues,represented,reductions⟩ := returned success
      refine ⟨values,?_,Spec.results_typed_wf typed,?_,represented⟩
      · simpa only [show Representation.valueType=SourceMachine.valueType from funext value_type_eq_abs] using (SourceMachine.results_type_of_typed typed).symm
      · intro value member
        exact Store.owned_result_fits _ value (ownedValues value member)
  obtain ⟨after,prepared,p,⟨same,source,invariant,ownedSource,ambientEq,sourceStep⟩,bodyDivergent⟩ := reached
  subst after
  let machine : EventfulMachine M P view code (signature.results.val.map Itasca.Translation.valueType) :=
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
end Itasca.Integration

end

/-! ## HostOutcomes -/

section

/-!
Public host invocation outcomes while retaining the evolving source-code interpretation.

Main declarations: `invoke_host_world_outcomes`.
-/

namespace Itasca.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Interp

theorem invoke_host_world_outcomes {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Representation.CodeInterpretation)
    (invariant : Representation.CodeInterpretation → runtime.store.Store M → Prop)
    (shape : ∀ c s, invariant c s → Representation.Shape view s)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : invariant code store) (sourceWf : wf_store (Representation.decodeStore view code store))
    (ambient : frame) (ambientWf : wf_frame ambient)
    (address : runtime.FuncAddr) (function : runtime.store.FuncInst) (identity : U64)
    (signature : Itasca.wasm_types.FuncType) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (owner : address.store = store.id)
    (functionAt : store.funcs.val[address.index.val]? = some function)
    (host : function.code = .Host identity)
    (signatureAt : store.types.val[function.signature.val]? = some signature)
    (owned : ∀ value ∈ args.val, Store.ValueInStore store value)
    (accepted : runtime.interp.check_values memory store args (alloc.vec.Vec.deref signature.params) = .ok (.Ok ()))
    (callback : ∀ p arguments defaults,
      hooks.call_host p store identity arguments defaults ⦃ (result, nextPlatform, after, returned) => ∃ afterCode,
        Store.CodeAgreesOn store code afterCode ∧ invariant afterCode after ∧
        Extend_store (Representation.decodeStore view code store) (Representation.decodeStore view afterCode after) ∧
        Store_ok (Representation.decodeStore view afterCode after) ⦄div)
    (retains : HostRetention hooks store identity) :
    Computation.DivSpec (HostDiverges hooks store) (runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results) fun out => ∃ afterCode,
      (invariant afterCode out.2.2.1 ∧ Store.CodeAgreesOn store code afterCode ∧ Store.MetadataExtended store out.2.2.1 ∧
        Extend_store (Representation.decodeStore view code store) (Representation.decodeStore view afterCode out.2.2.1) ∧
        store.externs.length ≤ out.2.2.1.externs.length) ∧
      (out.1 = .Ok () →
        ResultsTyped (Representation.decodeStore view afterCode out.2.2.1) (signature.results.val.map Itasca.Translation.valueType)
          (out.2.2.2.2.val.map sourceValue) ∧
        SourceMachine.Ownership.ValuesOwned (Store.ownershipBounds out.2.2.1) (out.2.2.2.2.val.map sourceValue) ∧
        StepH ⟨⟨Representation.decodeStore view code store,ambient⟩, vals (args.val.map sourceValue) ++ [.CALL_ADDR address.index.val]⟩
          [.call address.index.val (args.val.map sourceValue) (some (out.2.2.2.2.val.map sourceValue))]
          ⟨⟨Representation.decodeStore view afterCode out.2.2.1,ambient⟩, vals (out.2.2.2.2.val.map sourceValue)⟩ ∧
        (∀ value ∈ out.2.2.2.2.val, Store.ValueInStore out.2.2.1 value)) ∧
      (∀ error, out.1 = .Err error → ∃ events, EventfulInvocationError
        ⟨⟨Representation.decodeStore view code store,ambient⟩, vals (args.val.map sourceValue) ++ [.CALL_ADDR address.index.val]⟩
        events (Representation.decodeStore view afterCode out.2.2.1) ambient error) := by
  have arguments := checked_arguments_typed memory view code store sourceWf args signature.params accepted owned
  have initialWf := Spec.host_call_wf (fa:=address.index.val) sourceWf ambientWf arguments
  have argsOwned := Store.source_values_owned store args.val owned
  let retained := fun after => Store.MetadataExtended store after ∧ store.externs.length ≤ after.externs.length
  let property := fun after values => ∃ afterCode,
    invariant afterCode after ∧ Store.CodeAgreesOn store code afterCode ∧
    Extend_store (Representation.decodeStore view code store) (Representation.decodeStore view afterCode after) ∧
    ResultsTyped (Representation.decodeStore view afterCode after) (signature.results.val.map Itasca.Translation.valueType) values ∧
    SourceMachine.Ownership.ValuesOwned (Store.ownershipBounds after) values ∧
    StepH ⟨⟨Representation.decodeStore view code store,ambient⟩,vals (args.val.map sourceValue) ++ [.CALL_ADDR address.index.val]⟩
      [.call address.index.val (args.val.map sourceValue) (some values)]
      ⟨⟨Representation.decodeStore view afterCode after,ambient⟩,vals values⟩
  let errors := fun (after : runtime.store.Store M) (error : runtime.ExecError) => ∃ afterCode,
    invariant afterCode after ∧ Store.CodeAgreesOn store code afterCode ∧
    Extend_store (Representation.decodeStore view code store) (Representation.decodeStore view afterCode after) ∧
    ∃ events, EventfulInvocationError
      ⟨⟨Representation.decodeStore view code store,ambient⟩, vals (args.val.map sourceValue) ++ [.CALL_ADDR address.index.val]⟩
      events (Representation.decodeStore view afterCode after) ambient error
  let entry := fun (after : runtime.store.Store M) (entered : runtime.interp.Execution) => retained after ∧ entered.frames.val = [] ∧
    ∃ values, ValuesAt entered.slots.val 0 values ∧ property after values
  refine Computation.DivSpec.mono (invoke_with_prefix_owned_causes_composition_mode memory hooks floats allocator (HostDiverges hooks store) allocation exec store platform
    address function signature args results owner functionAt signatureAt accepted
    (fun value member => (owned value member).1) entry retained
    ⟨.refl _,Nat.le_refl _⟩ property errors ?_ ?_ ?_ ?_) ?_
  · intro error cause
    refine ⟨code,valid,(by intro index inst found fn; rfl),Spec.extend_store_refl _ sourceWf,?_⟩
    cases error <;> try simp only [InvocationResourceCause] at cause
    rename_i limit
    exact ⟨[],_,StepsH.refl initialWf⟩
  · intro after values kept satisfied refused
    obtain ⟨afterCode,fresh,agrees,extension,typed,ownership,source⟩ := satisfied
    exact ⟨afterCode,fresh,agrees,extension,[.call address.index.val (args.val.map sourceValue) (some values)], vals values,
      Spec.steps_h_single source⟩
  · intro prepared p executionId empty represented
    rcases (call_host_source_retained_world memory hooks floats allocator allocation interrupts view code invariant shape
        prepared store p valid address 0#usize ambient ambientWf function identity signature functionAt host signatureAt
        (args.val.map sourceValue) (by simpa only [show Representation.valueType=SourceMachine.valueType from funext value_type_eq_abs] using (SourceMachine.results_type_of_typed arguments).symm) arguments
        (Spec.results_typed_wf arguments) (fun value member => Store.owned_result_fits store value (argsOwned value member))
        represented sourceWf callback retains).imp_exists with
      ⟨called,actual,afterCode,agrees,fresh,kept,extension,count,effect,causes,_boundary⟩ | ⟨actual,diverged⟩
    swap
    · rw [actual]
      exact .div _ diverged
    have sameDecode := Store.decode_store_code_agrees view agrees
    rw [actual,Computation.DivSpec.ok_iff]
    refine ⟨⟨kept,count⟩,?_,?_⟩
    · intro success
      rcases effect with ⟨error,status,_,_⟩ | ⟨effect,typed⟩
      · rw [success] at status; cases status
      · obtain ⟨typed,ownedResults⟩ := typed success
        refine ⟨⟨kept,count⟩,?_,called.2.1.host_results.val.map sourceValue,?_,afterCode,fresh,agrees,extension,typed,ownedResults,?_⟩
        · exact congrArg alloc.vec.Vec.val effect.2.1 |>.trans empty
        · rcases effect.2.2.2.2 with good | bad
          · exact good.2.1
          · rcases bad.1 with bad | bad <;> rw [success] at bad <;> cases bad
        · rcases effect.2.2.2.2 with good | bad
          · simpa only [sameDecode] using good.2.2.1
          · rcases bad.1 with bad | bad <;> rw [success] at bad <;> cases bad
    · intro error rejected
      refine ⟨afterCode,fresh,agrees,extension,?_⟩
      rcases effect with ⟨early,status,cause,same⟩ | ⟨effect,typed⟩
      · have eq : early=error := by simpa only [rejected,core.result.Result.Err.injEq] using status.symm
        subst early
        rw [same,sameDecode]
        have kind := cause.error
        cases error <;> first
          | exact ⟨[],_,StepsH.refl initialWf⟩
          | simp [HostPreparationError] at kind
      · rcases effect.2.2.2.2 with good | bad
        · rw [rejected] at good
          cases good.1
        · obtain ⟨failure,source,footprint⟩ := bad
          have trace := Spec.steps_h_single source
          rw [sameDecode] at trace
          rcases failure with trapped | exhausted
          · have eq : error=.Trap .Host := by simpa only [rejected,core.result.Result.Err.injEq] using trapped
            subst error
            exact ⟨[.call address.index.val (args.val.map sourceValue) none],trace⟩
          · have eq : error=.Exhausted .CallStack := by simpa only [rejected,core.result.Result.Err.injEq] using exhausted
            subst error
            exact ⟨[.call address.index.val (args.val.map sourceValue) none],[.TRAP],trace⟩
  · intro after entered p enteredProof
    obtain ⟨kept,empty,values,represented,afterCode,fresh,agrees,extension,typed,ownedResults,source⟩ := enteredProof
    have stopped : ¬0#usize < entered.frames.len := by simp [alloc.vec.Vec.len,empty,alloc.vec.Vec.length]
    apply Computation.DivSpec.of_spec
    simp only [runtime.interp.invoke_with_loop1]
    apply loop.spec_decr_nat (fun _ => 0) (fun state => state = (entered,after,p,.Ok ()))
    · rintro state rfl
      simp only [runtime.interp.invoke_with_loop1.body,stopped,ite_false,WP.spec_ok]
      exact ⟨kept.1,kept,fun _ => ⟨values,(by simpa only [show Representation.valueType=SourceMachine.valueType from funext value_type_eq_abs] using (SourceMachine.results_type_of_typed typed).symm),Spec.results_typed_wf typed,
        fun value member => Store.owned_result_fits after value (ownedResults value member),represented,afterCode,fresh,agrees,extension,typed,ownedResults,source⟩,
        fun error impossible => by cases impossible⟩
    · rfl
  · rintro out ⟨kept,success,errors⟩
    cases status : out.1 with
    | Ok unit =>
      cases unit
      obtain ⟨⟨afterCode,fresh,agrees,extension,typed,ownedValues,source⟩,owners⟩ := success status
      refine ⟨afterCode,⟨fresh,agrees,kept.1,extension,kept.2⟩,?_,?_⟩
      · intro _
        exact ⟨typed,ownedValues,source,fun value member =>
          owned_source_value_in_store out.2.2.1 value (owners value member)
            (ownedValues (sourceValue value) (List.mem_map.mpr ⟨value,member,rfl⟩))⟩
      · intro error impossible
        cases impossible
    | Err error =>
      obtain ⟨afterCode,fresh,agrees,extension,events,source⟩ := errors error status
      refine ⟨afterCode,⟨fresh,agrees,kept.1,extension,kept.2⟩,?_,?_⟩
      · intro impossible
        cases impossible
      · intro reported failed
        have equal : error=reported := by simpa only [core.result.Result.Err.injEq] using failed
        subst reported
        exact ⟨events,source⟩
end Itasca.Integration

end

end

/-! ## DefinedResources -/

section

open Itasca.Representation

/-!
A public failure is explained at its original signature/entry boundary or at an actual source-reachable dispatch in the then-current code world.

Main declarations: `WorldDefinedSourceResourceCause` and `invoke_defined_world_recorded_resources`.
-/

namespace Itasca.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Interp

/-- Actual public defined-function invocation keeps one selected final code
world with its invariant, source outcomes and issued readback values. -/
theorem invoke_defined_world_recorded_resources
 {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.Laws memory hooks floats allocator view) (code : Representation.CodeInterpretation)
    (Inv : Representation.CodeInterpretation → runtime.store.Store M → Prop)
    (certify : ∀ c s,Inv c s → CertifiedSupportedStore view c s)
    (update : ∀ c before after,Inv c before → CumulativeStoreMutation view c before after → Inv c after)
    (capacities : ∀ c s,Inv c s → Representation.FunctionCapacities c s)
    (callbacks : HostLaws hooks view Inv)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : Inv code store)
    (ambient : frame) (ambientWf : wf_frame ambient)
    (address : runtime.FuncAddr) (function : runtime.store.FuncInst)
    (signature : Itasca.wasm_types.FuncType) (instanceIndex functionIndex : Usize)
    (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (owner : address.store = store.id)
    (owned : ∀ value ∈ args.val, Store.ValueInStore store value)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (hw : function.code = .Wasm instanceIndex functionIndex)
    (accepted : runtime.interp.check_values memory store args (alloc.vec.Vec.deref signature.params) = .ok (.Ok ())) :
    recordedInvokeWith memory hooks floats allocator exec store platform address args results []
      ⦃ (out,events) => ∃ afterCode,
        Inv afterCode out.2.2.1 ∧ Store.MetadataExtended store out.2.2.1 ∧ Store.CodeAgreesOn store code afterCode ∧
        Extend_store (Representation.decodeStore view code store) (Representation.decodeStore view afterCode out.2.2.1) ∧
        (out.1=.Ok () →
          ResultsTyped (Representation.decodeStore view afterCode out.2.2.1) (signature.results.val.map Itasca.Translation.valueType)
            (out.2.2.2.2.val.map sourceValue) ∧
          SourceMachine.Ownership.ValuesOwned (Store.ownershipBounds out.2.2.1) (out.2.2.2.2.val.map sourceValue) ∧
          (StepsH ⟨⟨Representation.decodeStore view code store,ambient⟩,
            vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val]⟩ events
            ⟨⟨Representation.decodeStore view afterCode out.2.2.1,ambient⟩,vals (out.2.2.2.2.val.map sourceValue)⟩) ∧
          (∀value∈out.2.2.2.2.val,Store.ValueInStore out.2.2.1 value)) ∧
        (∀error,out.1=.Err error → EventfulInvocationError
          ⟨⟨Representation.decodeStore view code store,ambient⟩,vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val]⟩
          events (Representation.decodeStore view afterCode out.2.2.1) ambient error ∧
          WorldDefinedSourceResourceCause hooks allocator view code Inv
            store ambient address signature args out.2.2.1 error) ⦄div := by
  have certified := certify code store valid
  have storeWf := Store.decode_store_wf view code store certified.shape certified.storeSyntax
  have arguments := checked_arguments_typed memory view code store storeWf args signature.params accepted owned
  have initialWf := Spec.host_call_wf (fa:=address.index.val) storeWf ambientWf arguments
  let retained := fun after => Store.MetadataExtended store after
  let property := fun after values events => ∃ afterCode,
    Inv afterCode after ∧ Store.CodeAgreesOn store code afterCode ∧
    Extend_store (Representation.decodeStore view code store) (Representation.decodeStore view afterCode after) ∧
    ResultsTyped (Representation.decodeStore view afterCode after) (signature.results.val.map Itasca.Translation.valueType) values ∧
    SourceMachine.Ownership.ValuesOwned (Store.ownershipBounds after) values ∧
    StepsH ⟨⟨Representation.decodeStore view code store,ambient⟩,vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val]⟩ events
      ⟨⟨Representation.decodeStore view afterCode after,ambient⟩,vals values⟩
  let errors := fun after error events => ∃ afterCode,
    Inv afterCode after ∧ Store.CodeAgreesOn store code afterCode ∧
    Extend_store (Representation.decodeStore view code store) (Representation.decodeStore view afterCode after) ∧
    EventfulInvocationError
      ⟨⟨Representation.decodeStore view code store,ambient⟩,vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val]⟩
      events (Representation.decodeStore view afterCode after) ambient error ∧
      WorldDefinedSourceResourceCause hooks allocator view code Inv
        store ambient address signature args after error
  let entry := fun (after : runtime.store.Store M) (prepared : runtime.interp.Execution) (events : List HostEvent) => events=[] ∧ after=store ∧ ∃source,
    Machine.Execution view code store prepared source
      (signature.results.val.map Itasca.Translation.valueType) 0 false ∧
    SourceMachine.Ownership.StatefulOwned (Store.ownershipBounds store) source ∧ source.ambient=ambient ∧
    StepH ⟨⟨Representation.decodeStore view code store,ambient⟩,vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val]⟩ [] (SourceMachine.decode source)
  refine (Computation.DivSpec.mono (recorded_invoke_with_prefix_owned_causes_composition_mode memory hooks floats allocator True laws.allocCorrect exec store platform
    address function signature args results [] owner hf hs accepted (fun value member=>(owned value member).1)
    entry retained (.refl _) property errors ?_ ?_ ?_ ?_) ?_).dspec
  · intro error cause
    refine ⟨code,valid,(by intro index inst found fn; rfl),Spec.extend_store_refl _ storeWf,?_,Or.inl (InvocationResourceCause.canonical _ _ _ cause)⟩
    cases error <;> try simp only [InvocationResourceCause] at cause
    rename_i limit
    exact ⟨_,StepsH.refl initialWf⟩
  · intro after values events kept satisfied refused
    obtain ⟨afterCode,fresh,agrees,extension,typed,ownership,reductions⟩ := satisfied
    refine ⟨afterCode,fresh,agrees,extension,⟨vals values,reductions⟩,Or.inl ?_⟩
    apply Or.inl; apply Or.inr
    obtain ⟨n,amount,refusal⟩ := refused
    exact ⟨results,n,by simpa only [Itasca.Translation.Environment.funcType,List.length_map] using Nat.le_trans (Nat.le_of_eq amount) (Nat.sub_le _ _),refusal⟩
  · intro prepared p identity empty represented
    unfold recordedCall Platform.Recording.run
    apply Computation.DivSpec.of_spec
    apply WP.spec_bind (call_defined_supported_entry_outcomes memory hooks floats allocator laws.allocCorrect laws.interruptsReturn view code
      prepared store p certified.shape certified.storeSyntax certified.segmentBounds certified.typed certified.supported certified.compiled
      ambient ambientWf address function signature instanceIndex functionIndex args empty identity represented accepted owned hf hs hw)
    intro out outcome
    rw [call_host_events_wasm hf hw]
    simp only [List.nil_append,WP.spec_ok]
    refine ⟨?_,?_,?_⟩
    · simpa only [outcome.1] using (show retained store from .refl _)
    · intro success
      exact ⟨rfl,outcome.1,outcome.2.1 success⟩
    · intro error failed
      obtain ⟨inst,compiled,hi,hc,cause⟩ := outcome.2.2 error failed
      change errors out.2.2.1 error []
      rw [outcome.1]
      refine ⟨code,valid,(by intro index inst found fn; rfl),Spec.extend_store_refl _ storeWf,?_,Or.inl ?_⟩
      · rcases cause.kind with rfl | rfl | rfl | rfl <;> exact ⟨_,StepsH.refl initialWf⟩
      · exact CallCause.invocation_canonical view code _ (capacities code store valid) certified.typed address function
          instanceIndex functionIndex inst compiled hf hw hi hc empty cause
  · intro after prepared p entryTrace entered
    obtain ⟨rfl,same,source,invariant,ownedSource,ambientEq,sourceStep⟩ := entered
    subst after
    let machine : EventfulWorld M P view (signature.results.val.map Itasca.Translation.valueType) :=
      ⟨code,⟨store,prepared,p,source,0,false,invariant,certified,ownedSource⟩⟩
    refine Computation.DivSpec.of_dspec ?_ fun _ => trivial
    apply WP.dspec_mono (world_recorded_loop_resource_results memory hooks floats allocator Inv capacities
      (world_step_outcomes memory hooks floats allocator view laws Inv certify update callbacks _) machine valid)
    rintro ⟨out,events⟩ outcome
    obtain ⟨⟨afterCode,newValid,fresh,kept,agrees,extension,success,failed⟩,causes⟩ := outcome
    refine ⟨kept,kept,?_,?_⟩
    · intro status
      obtain ⟨values,typed,ownedValues,represented,reductions⟩ := success status
      have tags : signature.results.val.map Itasca.Translation.valueType=values.map Representation.valueType := by
        simpa only [show Representation.valueType=SourceMachine.valueType from funext value_type_eq_abs] using (SourceMachine.results_type_of_typed typed).symm
      refine ⟨values,tags,Spec.results_typed_wf typed,?_,represented,afterCode,newValid,agrees,extension,typed,ownedValues,?_⟩
      · intro value member
        exact Store.owned_result_fits _ value (ownedValues value member)
      · simpa only [machine,ambientEq,List.nil_append] using StepsH.cons sourceStep reductions
    · intro error status
      have errorSource := failed error status
      refine ⟨afterCode,newValid,agrees,extension,?_,Or.inr ((causes error status).source sourceStep)⟩
      have first : StepsH _ [] (SourceMachine.decode source) := StepsH.cons sourceStep (StepsH.refl invariant.typed.typed.decode_wf)
      simpa only [machine,ambientEq,List.nil_append] using errorSource.prepend first
  · rintro ⟨out,events⟩ outcome
    cases status : out.1 with
    | Ok unit =>
      cases unit
      obtain ⟨⟨afterCode,fresh,agrees,extension,typed,sourceOwned,reductions⟩,rawOwned⟩ := outcome.2.1 status
      refine ⟨afterCode,fresh,outcome.1,agrees,extension,?_,?_⟩
      · intro _
        refine ⟨typed,sourceOwned,reductions,?_⟩
        intro value member
        apply owned_source_value_in_store out.2.2.1 value (rawOwned value member)
        exact sourceOwned _ (List.mem_map.mpr ⟨value,member,rfl⟩)
      · intro error failed
        simp only [status] at failed
        cases failed
    | Err error =>
      obtain ⟨afterCode,fresh,agrees,extension,reductions⟩ := outcome.2.2 error status
      refine ⟨afterCode,fresh,outcome.1,agrees,extension,?_,?_⟩
      · intro success
        simp only [status] at success
        cases success
      · intro reported failed
        have equal : error=reported := by simpa only [status,core.result.Result.Err.injEq] using failed
        subst reported
        exact reductions
end Itasca.Integration

end
