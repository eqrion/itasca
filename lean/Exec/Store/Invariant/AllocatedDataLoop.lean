import Exec.Store.Preparation.AllocationInitializers
import Exec.Store.Preparation.StagingAddresses
import Exec.Store.Initialization.InitializerMetadata
import Exec.Store.Initialization.ElementTypes
import Exec.Store.Initialization.DataStagingLoop
import Exec.Store.Initialization.ElementContentEffect
import Exec.Store.Initialization.DataContentLoop
import Exec.Store.Initialization.DataResultEffect

import Exec.Store.Initialization.SegmentGlobalMetadata

namespace Exec.Store
open Aeneas Aeneas.Std

theorem data_allocated_loop {M A : Type}
    (memory : runtime.platform.MemoryBuffer M) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (view : M → Slice U8)
    (before store : runtime.store.Store M) (instIndex start : Usize)
    (inst : runtime.store.Instance) (status : core.result.Result Unit runtime.ExecError)
    (staged : StagedPrefix before store) (fresh : before.instances.length ≤ instIndex.val)
    (found : store.instances.val[instIndex.val]? = some inst)
    (bindings : InitializerBindings store inst) (imports : InitializerImports store inst)
    (segments : InitializerSegmentBindings store inst)
    (objectBound : objectCount store ≤ Usize.max)
    (allocated : AllocationShape view store)
    (startBound : start.val ≤ inst.module.module.tail.data.val.length)
    (storeCapacity : store.datas.length + (inst.module.module.tail.data.val.length - start.val) ≤ Usize.max)
    (mapCapacity : inst.data.length + (inst.module.module.tail.data.val.length - start.val) ≤ Usize.max)
    (matching : ElementTypeMap store inst.module.module.env.elements.val inst.elements.val)
    (contents : ElementContents store)
    (issued : ∀ address ∈ inst.data.val, address.val < store.datas.length) :
    runtime.store.instantiate.Store.instantiate_inner_loop9 memory allocator store status start instIndex
      ⦃ out => ∃ after finalStatus,
        out = storeStateParts after finalStatus ∧ StagedPrefix before after ∧
        objectCount after ≤ Usize.max ∧ AllocationShape view after ∧ ElementContents after ∧ after.globals = store.globals ∧ (SegmentAccounting store → SegmentAccounting after) ∧
        InitializerFunctionMetadataAt store inst after instIndex ∧ ∃ next,
          after.instances.val[instIndex.val]? = some next ∧ next.module = inst.module ∧
          (∀ address ∈ next.data.val, address.val < after.datas.length) ∧ next.globals = inst.globals ∧
          InitializerBindings after next ∧ InitializerImports after next ∧ InitializerSegmentBindings after next ∧
          ElementTypeMap after inst.module.module.env.elements.val next.elements.val ∧
          (finalStatus = .Ok () → next.data.length = inst.data.length + (inst.module.module.tail.data.val.length - start.val)) ⦄ := by
  unfold runtime.store.instantiate.Store.instantiate_inner_loop9
  apply loop.spec_decr_nat (fun state => inst.module.module.tail.data.val.length - state.2.2.val)
    (fun state => StagedPrefix before state.1 ∧ objectCount state.1 ≤ Usize.max ∧ AllocationShape view state.1 ∧ ElementContents state.1 ∧ state.1.globals = store.globals ∧ (SegmentAccounting store → SegmentAccounting state.1) ∧
      InitializerFunctionMetadataAt store inst state.1 instIndex ∧
      state.2.2.val ≤ inst.module.module.tail.data.val.length ∧
      ∃ currentInst, state.1.instances.val[instIndex.val]? = some currentInst ∧ currentInst.module = inst.module ∧
        (∀ address ∈ currentInst.data.val, address.val < state.1.datas.length) ∧ currentInst.globals = inst.globals ∧
        InitializerBindings state.1 currentInst ∧ InitializerImports state.1 currentInst ∧
        InitializerSegmentBindings state.1 currentInst ∧
        currentInst.data.length + (inst.module.module.tail.data.val.length - state.2.2.val) ≤ Usize.max ∧
        state.1.datas.length + (inst.module.module.tail.data.val.length - state.2.2.val) ≤ Usize.max ∧
        ElementTypeMap state.1 inst.module.module.env.elements.val currentInst.elements.val ∧
        (state.2.1 = .Ok () → currentInst.data.length + start.val = inst.data.length + state.2.2.val))
  · rintro ⟨current, result, index⟩ ⟨hstaged, hobjects, hallocated, hcontents, hglobals, haccounted, hmetadata, hindex,
      currentInst, hfound, hsource, hissued, hglobalMap, hbindings, himports, hsegments, hcapacity, hstoreCapacity, htyped, hcount⟩
    dsimp only at hstaged hobjects hallocated hcontents hglobals haccounted hmetadata hindex hfound hsource hissued hglobalMap hbindings himports hsegments hcapacity hstoreCapacity htyped hcount ⊢
    unfold runtime.store.instantiate.Store.instantiate_inner_loop9.body
    step with Interp.vec_index_given current.instances instIndex currentInst hfound as ⟨actual, hactual⟩
    subst actual
    simp only [runtime.compiler.ExecutableModule.tail, module.Module.tail,
      Itasca.module.Module.impl.tail, bind_ok, hsource]
    split
    · rename_i more
      have hmore : index.val < inst.module.module.tail.data.val.length := by simpa using more
      cases result with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨current, .Err error, rfl, hstaged, hobjects, hallocated, hcontents, hglobals, haccounted, hmetadata,
          currentInst, hfound, hsource, hissued, hglobalMap, hbindings, himports, hsegments, htyped, by simp⟩
      | Ok unitValue =>
        cases unitValue
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        have room : current.datas.length < Usize.max := by omega
        have mapRoom : currentInst.data.length < Usize.max := by omega
        step with add_instance_data_result_effect memory allocator law current instIndex index currentInst
          hfound (by simpa only [hsource] using hmore) room mapRoom
          as ⟨state, after, resultEffect⟩
        have effect := resultEffect.effect
        obtain ⟨nextInst, nextFound, nextSource, nextBindings, nextImports, nextSegments, nextSize, nextStoreSize⟩ :=
          effect.context hfound hbindings himports hsegments
        have nextMetadata : InitializerFunctionMetadataAt store inst after instIndex :=
          ⟨nextInst, nextFound, (hmetadata.resolve hfound).trans (effect.function_metadata hfound nextFound)⟩
        have nextStaged := effect.staged hstaged fresh
        have nextObjects : objectCount after ≤ Usize.max := by simpa only [effect.object_count] using hobjects
        have counterCapacity := inst.module.module.tail.data.property
        step as ⟨next, hnext⟩
        refine ⟨nextStaged, nextObjects, effect.allocated hallocated, effect.contents hcontents, effect.globals.trans hglobals, (fun h => effect.segment_accounting hfound (haccounted h)), nextMetadata, ?_, ⟨nextInst, nextFound,
          nextSource.trans hsource, effect.addresses hfound nextFound hissued, (effect.global_map hfound nextFound).trans hglobalMap, nextBindings, nextImports, nextSegments, ?_, ?_,
          effect.element_types hfound nextFound htyped, ?_⟩, ?_⟩
        · omega
        · omega
        · omega
        · intro success
          have nextCount := resultEffect.count (List.getElem?_eq_some_iff.mp hfound).1 nextFound success
          have oldCount := hcount rfl
          omega
        · omega
    · rename_i stopped
      have endIndex : index.val = inst.module.module.tail.data.val.length := by
        simp [alloc.vec.Vec.deref] at stopped
        omega
      simp only [WP.spec_ok]
      exact ⟨current, result, rfl, hstaged, hobjects, hallocated, hcontents, hglobals, haccounted, hmetadata,
        currentInst, hfound, hsource, hissued, hglobalMap, hbindings, himports, hsegments, htyped, fun success => by have counted := hcount success; omega⟩
  · exact ⟨staged, objectBound, allocated, contents, rfl, (fun h => h), ⟨inst, found, .refl _ _⟩, startBound, inst, found, rfl, issued, rfl, bindings, imports, segments, mapCapacity, storeCapacity, matching, fun _ => by simp⟩

end Exec.Store
