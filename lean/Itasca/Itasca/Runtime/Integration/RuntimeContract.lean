import Itasca.Runtime.Interp.Recording
import Itasca.Runtime.Integration.Host.Observation
import Itasca.Runtime.Integration.Definitions
import Itasca.Results.Definitions.Runtime
import Itasca.Runtime.Integration.Api.CreationAndGrowth
import Itasca.Runtime.Integration.Api.DefinitionAndWrite
import Itasca.Runtime.Integration.Api.StoreRead
import Itasca.Runtime.Integration.Instantiation.InstantiateSource
import Itasca.Runtime.Integration.Invocation.Behaves
import Itasca.Runtime.Integration.Api.SourceResourceBounds

open WebAssembly

/-! Constructs the public runtime protocol from the internal invariant.
Only this proof knows which store predicate implements the protocol. -/
namespace Itasca.Integration
open Aeneas Aeneas.Std Itasca.Representation Itasca.Interp Itasca.Store

/-- Export the observable part of an internal mutation certificate. -/
private theorem CumulativeStoreMutation.public {M : Type} {view : M → Slice U8}
    {code : CodeInterpretation} {before after : runtime.store.Store M}
    (mutation : CumulativeStoreMutation view code before after) : StoreMutation view code before after :=
  ⟨mutation.metadata, mutation.externs, mutation.extension, mutation.segmentCounts, mutation.limits⟩

/-- Typed, owned calls cannot take either API-rejection branch. This fact is
proved from the checker contract, never included in the candidate vocabulary. -/
private theorem not_rejected {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : CodeInterpretation) (store : runtime.store.Store M)
    (address : runtime.FuncAddr) (args : Slice runtime.Value)
    (owner : address.store = store.id)
    (owned : ∀ value ∈ args.val, Store.ValueInStore store value)
    (typed : InvocationArgumentsTyped (decodeStore view code store) address.index.val (args.val.map sourceValue))
    {error : runtime.ExecError} (rejected : InvocationRejected memory store address args error) : False := by
  rcases rejected with ⟨foreign, _⟩ | ⟨function, signature, hf, hs, checked⟩
  · exact foreign owner
  · have lookup : (decodeStore view code store).FUNCS[address.index.val]? =
        some (decodeFunction code store function) := by
      simp only [decodeStore, List.getElem?_map, hf, Option.map_some]
    have typeEq : (decodeFunction code store function).TYPE = Itasca.Translation.Environment.funcType signature := by
      rw [Store.decode_function_type code store function (List.getElem?_eq_some_iff.mp hs).1]
      simp only [(List.getElem?_eq_some_iff.mp hs).2]
    have arguments := typed _ (signature.params.val.map Itasca.Translation.valueType) (signature.results.val.map Itasca.Translation.valueType)
      lookup (by rw [typeEq]; rfl)
    have accepted := typed_arguments_accepted memory store (decodeStore view code store) args signature.params
      arguments (fun value member => (owned value member).1)
    simp only [accepted, Result.ok.injEq, reduceCtorEq] at checked

/-- The implementation's checker rejection implies the semantic input error. -/
private theorem InvocationRejected.public {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : CodeInterpretation) (store : runtime.store.Store M)
    (address : runtime.FuncAddr) (args : Slice runtime.Value) {error : runtime.ExecError}
    (rejected : InvocationRejected memory store address args error) :
    InvocationInputError view code store address args error := by
  refine ⟨?_, ?_⟩
  · rcases rejected with ⟨_, reported⟩ | ⟨function, signature, _, _, checked⟩
    · exact Or.inl reported
    · exact (Interp.check_values_error_kind memory store args (alloc.vec.Vec.deref signature.params) error checked).symm
  · rintro ⟨owner, owned, typed⟩
    exact not_rejected memory view code store address args owner owned typed rejected

theorem executable_contract {M : Type} (view : M → Slice U8) :
    RuntimeContract view (ExecutableInv view) where
  well_formed := fun _ _ valid => valid.well_formed
  source_typed := fun _ _ valid => valid.source_typed
  with_identity := by
    intro memory code id limits positive
    exact _root_.Itasca.runtime.store.Store.with_identity.spec memory view code id limits positive
  define_extern_with := by
    intro A memory allocator allocator_correct code store store_invariant identity
    apply Aeneas.Std.WP.spec_mono (_root_.Itasca.runtime.store.Store.define_extern_with.spec memory allocator allocator_correct view code store store_invariant identity)
    rintro ⟨result, after⟩ held
    cases result <;> simpa only [uncurry_apply_pair, RustResult.Post] using held
  define_host_with := by
    intro A memory allocator allocator_correct code store store_invariant ty host
    apply Aeneas.Std.WP.spec_mono (_root_.Itasca.runtime.store.Store.define_host_with.spec memory allocator allocator_correct view code store store_invariant ty host)
    rintro ⟨result, after⟩ held
    cases result <;> simp only [uncurry_apply_pair, RustResult.Post] at * <;>
      exact ⟨held.1, ⟨held.2.1.identity, held.2.1.funcs, held.2.1.types,
        held.2.1.instances⟩, held.2.1.externs, held.2.1.limits,
        decode_store_prefix view code store after store_invariant.shape held.2.1, held.2.2⟩
  define_memory_with := by
    intro A memory allocator allocator_correct memory_laws code store store_invariant ty buffer
    apply WP.spec_mono (_root_.Itasca.runtime.store.Store.define_memory_with.spec memory allocator allocator_correct view memory_laws code store store_invariant ty buffer)
    rintro ⟨result, after⟩ held
    cases result with
    | Err error => exact ⟨held.1,held.2.1.public,held.2.2⟩
    | Ok address =>
      obtain ⟨owner,index,issued,appended,length⟩ := held.2.2
      refine ⟨held.1,held.2.1.public,owner,index,issued,?_,length⟩
      have pages : (view buffer).length / 65536 = ty.limits.min.val := by omega
      simp only [decodeStore,appended,List.map_append,List.map_cons,List.map_nil,decodeMemory,pages]
  define_table_with := by
    intro A memory allocator allocator_correct code store store_invariant ty
    apply WP.spec_mono (_root_.Itasca.runtime.store.Store.define_table_with.spec memory allocator allocator_correct view code store store_invariant ty)
    rintro ⟨result, after⟩ held
    cases result with
    | Err error => exact ⟨held.1,held.2.1.public,held.2.2⟩
    | Ok address =>
      obtain ⟨owner,index,issued,elements,zeros,appended⟩ := held.2.2
      refine ⟨held.1,held.2.1.public,owner,index,issued,?_⟩
      simp only [decodeStore,appended,List.map_append,List.map_cons,List.map_nil,decodeTable,
        alloc.vec.Vec.length,zeros,List.length_replicate,List.map_replicate,decodeRef]
      rfl
  define_global_with := by
    intro A memory allocator allocator_correct code store store_invariant ty value issued
    apply Aeneas.Std.WP.spec_mono (_root_.Itasca.runtime.store.Store.define_global_with.spec memory allocator allocator_correct view code store store_invariant ty value issued)
    rintro ⟨result, after⟩ held
    cases result <;> simp only [uncurry_apply_pair, RustResult.Post] at * <;>
      exact ⟨held.1, held.2.1.public, held.2.2⟩
  set_global := by
    intro memory code store store_invariant address value issued value_issued
    apply WP.spec_mono (_root_.Itasca.runtime.store.Store.set_global.spec memory view code store store_invariant address value issued value_issued)
    rintro ⟨result,after⟩ ⟨valid,retained,effect⟩
    refine ⟨valid,retained.public,?_⟩
    cases result with
    | Err error => exact effect
    | Ok unitValue =>
      cases unitValue
      obtain ⟨mutation,old,found,mutable,typed,written⟩ := effect
      exact global_update_from_words view code store after address value mutation old found mutable typed written
  set_table := by
    intro memory code store store_invariant address index value issued value_issued
    apply WP.spec_mono (_root_.Itasca.runtime.store.Store.set_table.spec memory view code store store_invariant address index value issued value_issued)
    rintro ⟨result,after⟩ ⟨valid,retained,effect⟩
    refine ⟨valid,retained.public,?_⟩
    cases result with
    | Err error => exact effect
    | Ok unitValue =>
      cases unitValue
      obtain ⟨old,words,found,inside,typed,encoded,owned,_,rfl⟩ := effect
      exact table_update_from_words view code store address index value old words owned found inside typed encoded
  memory_mut := by
    intro memory memory_laws code store store_invariant address issued
    apply WP.spec_mono (_root_.Itasca.runtime.store.Store.memory_mut.spec memory view memory_laws code store store_invariant address issued)
    rintro ⟨result,back⟩ effect
    cases result with
    | Err error =>
      refine ⟨effect.1,effect.2.1,?_⟩
      intro reply
      have returned := effect.2.2 reply
      exact ⟨returned.1,returned.2.1.public,returned.2.2⟩
    | Ok bytes =>
      obtain ⟨object,owner,found,rfl,written,failed⟩ := effect
      refine ⟨decodeMemory view object,owner,?_,rfl,?_,?_⟩
      · simp only [decodeStore,List.getElem?_map,found,Option.map_some]
      · intro replacement length
        obtain ⟨valid,mutation,retained,decoded⟩ := written replacement length
        refine ⟨valid,retained.public,?_⟩
        exact memory_update_from_buffer view code store _ address object (decodeBytes replacement.val) found
          (by simpa only [decodeBytes,List.length_map] using length) mutation decoded
      · intro error
        exact ⟨(failed error).1,(failed error).2.public⟩
  grow_memory_with := by
    intro memory memory_laws code store store_invariant address delta issued
    apply Aeneas.Std.WP.spec_mono (_root_.Itasca.runtime.store.Store.grow_memory_with.spec memory view memory_laws code store store_invariant address delta issued)
    rintro ⟨result, after⟩ held
    cases result <;> simp only [uncurry_apply_pair, RustResult.Post] at * <;>
      exact ⟨held.1, held.2.1.public, held.2.2⟩
  grow_table_with := by
    intro A memory allocator allocator_correct code store store_invariant address delta value issued value_issued
    apply Aeneas.Std.WP.spec_mono (_root_.Itasca.runtime.store.Store.grow_table_with.spec memory allocator allocator_correct view code store store_invariant address delta value issued value_issued)
    rintro ⟨result, after⟩ held
    cases result <;> simp only [uncurry_apply_pair, RustResult.Post] at * <;>
      exact ⟨held.1, held.2.1.public, held.2.2⟩
  global := by
    intro memory code store store_invariant address issued
    apply WP.spec_mono (_root_.Itasca.runtime.store.Store.global.spec memory view code store store_invariant address issued)
    intro result held
    cases result with
    | Err error => exact held
    | Ok value =>
      obtain ⟨owner,object,_,found,owned,typed,returned⟩ := held
      refine ⟨owner,decodeGlobal object,found,owned,returned,Itasca.Translation.mutability object.ty.mutability,?_⟩
      simp only [decodeGlobal,typed,source_value_type]
  memory := by
    intro memory memory_laws code store address issued
    apply WP.spec_mono (_root_.Itasca.runtime.store.Store.memory.spec memory view memory_laws code store address issued)
    intro result held
    cases result with
    | Err error => exact held
    | Ok bytes =>
      obtain ⟨owner,object,_,_,found,returned⟩ := held
      exact ⟨owner,decodeMemory view object,found,returned⟩
  table_size := by
    intro memory code store store_invariant address issued
    apply WP.spec_mono (_root_.Itasca.runtime.store.Store.table_size.spec memory view code store store_invariant address issued)
    intro result held
    cases result with
    | Err error => exact held
    | Ok size =>
      obtain ⟨owner,object,_,_,found,sizeEq⟩ := held
      exact ⟨owner,decodeTable object,found,sizeEq⟩
  table_get := by
    intro memory code store store_invariant address index issued
    apply WP.spec_mono (_root_.Itasca.runtime.store.Store.table_get.spec memory view code store store_invariant address index issued)
    intro result held
    cases result with
    | Err error =>
      rcases held with foreign | ⟨reported,owner,object,found,bound⟩
      · exact Or.inl foreign
      · refine Or.inr ⟨reported,owner,decodeTable object,?_,?_⟩
        · simp only [decodeStore,List.getElem?_map,found,Option.map_some]
        · simpa only [decodeTable,List.length_map] using bound
    | Ok value =>
      obtain ⟨owner,object,word,_,_,found,selected,owned,returned⟩ := held
      exact ⟨owner,decodeTable object,decodeRef object.ty word,found,selected,owned,
        by simpa only [ref_val_eq] using returned⟩
  func_type := by
    intro memory code store store_invariant address issued
    apply WP.spec_mono (_root_.Itasca.runtime.store.Store.func_type.spec memory view code store store_invariant address issued)
    intro result held
    cases result with
    | Err error => exact held
    | Ok signature =>
      obtain ⟨owner,function,_,_,found,typed⟩ := held
      exact ⟨owner,decodeFunction code store function,found,typed⟩
  extern_identity := by
    intro memory store address issued
    apply Aeneas.Std.WP.spec_mono (_root_.Itasca.runtime.store.Store.extern_identity.spec memory store address issued)
    intro result held
    cases result <;> simpa only [uncurry_apply_pair, RustResult.Post] using held
  export_lookup := by
    intro memory code store store_invariant address query index_if_owned
    apply WP.spec_mono (_root_.Itasca.runtime.store.Store.export.spec memory view code store store_invariant address query index_if_owned)
    intro result post
    cases result with
    | Err error => exact post
    | Ok found =>
      obtain ⟨owner,inst,lookup,foundEq,missing,_⟩ := post
      refine ⟨owner,inst,lookup,missing,?_⟩
      intro external returned
      obtain ⟨entry,member,named,resolved⟩ := export_search_some inst query external (foundEq.symm.trans returned)
      have shape := store_invariant.shape.instances inst (List.mem_of_getElem? lookup)
      have bounds := store_invariant.exportBounds address.index.val inst lookup
      subst external
      refine ⟨resolve_export_in_store store inst bounds shape entry member,entry,member,named,?_⟩
      have addressEq := resolve_export_source store inst bounds shape entry member
      change (⟨Itasca.Binary.nameOfBytes entry.name.val,(decodeExport inst entry).ADDR⟩ : exportinst) = _
      rw [named,addressEq]
  instantiate := by
    intro P F A memory hooks floats allocator memory_laws allocator_correct before module imports platform oldCode store_invariant imports_issued bytes limits compilation_accepted raw source_encoding
    have result := instantiate_compiled_source memory hooks floats allocator view memory_laws allocator_correct before module imports platform
      oldCode store_invariant imports_issued bytes limits compilation_accepted raw source_encoding
    refine ⟨result.1, WP.spec_mono result.2 ?_⟩
    rintro ⟨status, after, nextPlatform⟩ ⟨valid, retained, extension, outcome, _causes⟩
    exact ⟨valid, retained, extension, outcome⟩
  behaves := by
    intro P F A memory hooks floats allocator platform_laws code host_laws exec store platform store_invariant address args results function_issued arguments_issued initial source_invocation
    have original := invoke_executable_world_behaves memory hooks floats allocator view platform_laws code host_laws
      exec store platform store_invariant address args results function_issued arguments_issued initial source_invocation
    refine ⟨?_, original.2⟩
    have observed := invoke_executable_world_source_resources memory (Platform.observing hooks) floats allocator
      view platform_laws.observing code host_laws.observing exec store (platform,[]) store_invariant address args results
      function_issued arguments_issued initial source_invocation
    rw [←observing_invoke_erase memory hooks floats allocator exec store platform address args results []]
    apply WP.dspec_bind observed
    rintro ⟨result,execution,after,⟨nextPlatform,observations⟩,returned⟩ ⟨events,recorded,outcome,_⟩
    simp only [Std.uncurry,WP.dspec_ok]
    have observedRun : runtime.interp.invoke_with memory (Platform.observing hooks) floats allocator exec store
        (platform,[]) address args results = .ok (result,execution,after,(nextPlatform,observations),returned) := by
      rw [←recorded_invoke_with_erase memory (Platform.observing hooks) floats allocator exec store
        (platform,[]) address args results [],recorded,bind_ok]
      rfl
    have matched := recorded_invoke_observations memory hooks floats allocator
      (observing_call memory hooks floats allocator ⟨platform_laws.allocCorrect,platform_laws.interruptsReturn⟩)
      (exec,store) (platform,[]) address (args,results) [] (Platform.ObservationExtension.refl []) _ recorded
    obtain ⟨fresh,same,matched⟩ := matched
    change observations = fresh at same
    subst fresh
    refine ⟨observations,events,observedRun,matched,?_⟩
    obtain ⟨afterCode,agrees,store_invariant,metadata,extension,reached,success,failure⟩ := outcome
    refine ⟨afterCode,agrees,store_invariant,metadata,extension,reached,?_⟩
    cases result with
    | Ok value =>
      cases value
      exact success rfl
    | Err error =>
      rcases failure error rfl with ⟨rejected,unchanged,noEvents⟩ | executed
      · obtain ⟨kind, invalid⟩ := rejected.public memory view code store address args
        have same := congrArg (fun out : InvocationResult M (P × List (Platform.HostObservation M)) =>
          (out.1,out.2.1,out.2.2.1,out.2.2.2.1.1,out.2.2.2.2)) unchanged
        rcases kind with rfl | rfl <;> exact ⟨invalid, same, noEvents⟩
      · cases error <;> simp only [EventfulInvocationError] at executed ⊢
        all_goals exact executed

  resource_complete := by
    intro P F A memory hooks floats allocator platformLaws code hostLaws available
      exec store platform invariant address args results owner issued arguments initial invoked typed
      allowance budget
    exact invoke_executable_world_no_spurious_errors memory hooks floats allocator view platformLaws
      code hostLaws available.limits exec store platform invariant address args results owner issued
      arguments initial invoked typed (budget.internal (by cases invoked; assumption))
      (fun T values n _ => available.allocations T values n) available.interrupts available.hosts

/-- A verified store protocol exists for every memory representation.
Clients choose its predicate once and use its laws for every subsequent API call. -/
theorem runtime_contract_exists {M : Type} (view : M → Slice U8) :
    ∃ Inv, RuntimeContract view Inv :=
  ⟨ExecutableInv view, executable_contract view⟩

/-- Divergence reflection recovers normal return when both divergence causes
are excluded; every returned error and preservation guarantee is retained. -/
theorem InvocationBehavior.returns {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {Inv : CodeInterpretation → runtime.store.Store M → Prop}
    {code : CodeInterpretation} {exec : runtime.interp.Execution} {store : runtime.store.Store M}
    {platform : P} {address : runtime.FuncAddr} {args : Slice runtime.Value}
    {results : alloc.vec.Vec runtime.Value} {initial : config} {outcome}
    (behavior : InvocationBehavior memory hooks floats allocator view Inv code exec store platform address args results initial outcome)
    (finite : ¬ Spec.InfiniteSourceWithEvents initial)
    (callbacks : ¬ HostCallDiverged hooks view initial) :
    outcome ⦃ (result, execution, after, nextPlatform, returned) => ∃ observations events,
    runtime.interp.invoke_with memory (Platform.observing hooks) floats allocator exec store
      (platform,[]) address args results = .ok (result,execution,after,(nextPlatform,observations),returned) ∧
    List.Forall₂ Platform.HostObservation.Matches observations events ∧
    InvocationOutcome view Inv code store exec platform address args results initial result execution after nextPlatform returned events ⦄ := by
  rcases (Computation.DivSpec.of_dspec behavior.1 behavior.2).imp_exists with ⟨out, called, post⟩ | ⟨_, cause⟩
  · rw [called, WP.spec_ok]
    exact post
  · exact (cause.elim finite callbacks).elim

end Itasca.Integration
