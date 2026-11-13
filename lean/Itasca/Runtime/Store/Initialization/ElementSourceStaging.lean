import Itasca.Runtime.Representation.Values
import Itasca.Runtime.Store.Initialization.ElementTypedEffect
import Itasca.Runtime.Store.Initialization.ElementShapeLoop
import Itasca.Runtime.Store.Initialization.DataEffects
import Itasca.Runtime.Store.Invariant.Typing
import Itasca.Runtime.Store.Initialization.Data
import Itasca.Runtime.Store.Initialization.SegmentReady
import Itasca.Runtime.Store.Initialization.ElementTypes
import Itasca.Runtime.Store.Invariant.FunctionSignatures
import Itasca.Runtime.Compiler.Local.Relations.Function.Function

/-!
Sections, each formerly its own module: ElementContentEffect, SegmentGlobalMetadata, DataValueMetadata, SegmentBoundsEffects, ElementCompleteLoop, InitializerMetadataCertificates, ElementSourceLoop, ElementValues, ElementSourceStaging.
-/

/-! ## ElementContentEffect -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- Exact element staging retains the source reference type in the newly
allocated segment and distinguishes a normal refusal from successful append. -/
inductive ElementContentEffect {M : Type} (store : runtime.store.Store M)
    (instIndex : Usize) (inst : runtime.store.ModuleInst) (source : Itasca.metadata.Element) :
    core.result.Result Unit runtime.ExecError → runtime.store.Store M → Prop where
  | failed (error : runtime.ExecError) : ElementContentEffect store instIndex inst source (.Err error) store
  | appended (elements : alloc.vec.Vec runtime.store.ElemInst) (addresses : alloc.vec.Vec Usize)
      (values : alloc.vec.Vec U64)
      (elementValues : elements.val = store.elems.val ++ [{ty := source.elem, refs := values}])
      (addressValues : addresses.val = inst.elems.val ++ [store.elems.len])
      (canonical : ∀ word ∈ values.val, ReferenceShape store source.elem word) :
      ElementContentEffect store instIndex inst source (.Ok ())
        {store with elems := elements, instances := store.instances.set instIndex {inst with elems := addresses}}

theorem ElementContentEffect.typed {M : Type} {store after : runtime.store.Store M}
    {instIndex inst source status} (typed : ElementContentEffect store instIndex inst source status after) :
    ElementTypedEffect store instIndex inst source status after := by
  cases typed with
  | failed error => exact .failed error
  | appended elements addresses values stored mapped canonical => exact .appended elements addresses values stored mapped

def ElementContents {M : Type} (store : runtime.store.Store M) : Prop :=
  ∀ element ∈ store.elems.val, ∀ word ∈ element.refs.val, ReferenceShape store element.ty word

theorem ElementContentEffect.contents {M : Type} {store after : runtime.store.Store M}
    {instIndex inst source status} (effect : ElementContentEffect store instIndex inst source status after)
    (before : ElementContents store) : ElementContents after := by
  cases effect with
  | failed error => exact before
  | appended elements addresses values stored mapped canonical =>
    intro element member word contained
    simp only [stored, List.mem_append, List.mem_singleton] at member
    rcases member with old | rfl
    · simpa only [ReferenceShape] using before element old word contained
    · simpa only [ReferenceShape] using canonical word contained

theorem add_instance_element_content_effect {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex index : Usize)
    (inst : runtime.store.ModuleInst) (segment : Itasca.metadata.Element)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (helem : inst.module.module.env.elements.val[index.val]? = some segment)
    (certificates : ElementInitializers store inst index segment)
    (bindings : InitializerBindings store inst)
    (room : store.elems.length < Usize.max) (mapRoom : inst.elems.length < Usize.max) :
    runtime.store.instantiate.Store.add_instance_element memory hooks floats allocator store platform instIndex index
      ⦃ out => ElementContentEffect store instIndex inst segment out.1 out.2.1 ∧ out.2.2 = platform ⦄ := by
  unfold runtime.store.instantiate.Store.add_instance_element
  step with Interp.vec_index_given store.instances instIndex inst hi as ⟨found, hfound⟩
  subst found
  simp only [runtime.compiler.ExecutableModule.env,
    Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.elements, bind_ok]
  step with Itasca.Runtime.Representation.slice_index_given inst.module.module.env.elements.deref index segment
    (by simpa [alloc.vec.Vec.deref] using helem) as ⟨found, hfound⟩
  subst found
  obtain ⟨reserved, hreserve⟩ := reserve_wrapper_eq allocator law (alloc.vec.Vec.new U64) segment.init.len
  rw [hreserve]
  cases reserved with
  | false =>
    simpa [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using (ElementContentEffect.failed (store := store) (instIndex := instIndex) (inst := inst) (source := segment) (.Exhausted .Allocation))
  | true =>
    simp only [↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with element_initializers_shape_loop memory hooks floats allocator law store platform instIndex index
      segment.init.len inst segment hi helem (by simp) certificates bindings
      (alloc.vec.Vec.new U64) 0#usize (.Ok ()) (by simp) (by scalar_tac) (by simp)
      as ⟨after, host, values, status, hs, hp, hvalues, refs⟩
    subst after host
    cases status with
    | Err error =>
      simpa [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using (ElementContentEffect.failed (store := store) (instIndex := instIndex) (inst := inst) (source := segment) error)
    | Ok unit =>
      cases unit
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      obtain ⟨reserved, hreserve⟩ := reserve_wrapper_eq allocator law store.elems 1#usize
      rw [hreserve]
      cases reserved with
      | false =>
        simpa [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using (ElementContentEffect.failed (store := store) (instIndex := instIndex) (inst := inst) (source := segment) (.Exhausted .Allocation))
      | true =>
        simp only [↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        step with Interp.vec_index_given store.instances instIndex inst hi as ⟨found, hfound⟩
        subst found
        step with Itasca.Runtime.Representation.slice_index_given inst.module.module.env.elements.deref index segment
          (by simpa [alloc.vec.Vec.deref] using helem) as ⟨found, hfound⟩
        subst found
        step as ⟨elements, helements⟩
        have instanceBound : instIndex.val < store.instances.length :=
          (List.getElem?_eq_some_iff.mp hi).1
        step as ⟨old, back, hold, hback⟩
        have old_eq : old = inst := by
          have hread := List.getElem?_eq_getElem instanceBound
          rw [hi] at hread
          exact hold.trans (Option.some.inj hread).symm
        subst old
        step as ⟨addresses, haddresses⟩
        have instanceRead : store.instances.val[instIndex.val] = inst :=
          Option.some.inj ((List.getElem?_eq_getElem instanceBound).symm.trans hi)
        have effect := ElementContentEffect.appended (store := store) (instIndex := instIndex) (inst := inst) (source := segment)
          elements addresses values helements
          (by simpa only [instanceRead] using haddresses) refs
        simpa [hback, instanceRead] using And.intro effect (rfl : platform = platform)


end Itasca.Runtime.Store

end

/-! ## SegmentGlobalMetadata -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem ElementStageEffect.globals {M : Type} {store after : runtime.store.Store M}
    {index inst} (effect : ElementStageEffect store index inst after) : after.globals = store.globals := by
  cases effect <;> rfl

theorem ElementStageEffect.global_map {M : Type} {store after : runtime.store.Store M}
    {index inst next} (effect : ElementStageEffect store index inst after)
    (found : store.instances.val[index.val]? = some inst)
    (nextFound : after.instances.val[index.val]? = some next) : next.globals = inst.globals := by
  cases effect with
  | unchanged =>
    have same := Option.some.inj (found.symm.trans nextFound)
    subst next
    rfl
  | appended elements addresses element stored mapped =>
    have bound := (List.getElem?_eq_some_iff.mp found).1
    simp only [alloc.vec.Vec.set_val_eq, List.getElem?_set, if_pos bound, ↓reduceIte, Option.some.injEq] at nextFound
    subst next
    rfl

theorem DataStageEffect.globals {M : Type} {store after : runtime.store.Store M}
    {index inst} (effect : DataStageEffect store index inst after) : after.globals = store.globals := by
  cases effect <;> rfl

theorem DataStageEffect.global_map {M : Type} {store after : runtime.store.Store M}
    {index inst next} (effect : DataStageEffect store index inst after)
    (found : store.instances.val[index.val]? = some inst)
    (nextFound : after.instances.val[index.val]? = some next) : next.globals = inst.globals := by
  cases effect with
  | unchanged =>
    have same := Option.some.inj (found.symm.trans nextFound)
    subst next
    rfl
  | appended datas addresses data stored mapped =>
    have bound := (List.getElem?_eq_some_iff.mp found).1
    simp only [alloc.vec.Vec.set_val_eq, List.getElem?_set, if_pos bound, ↓reduceIte, Option.some.injEq] at nextFound
    subst next
    rfl

end Itasca.Runtime.Store

end

/-! ## DataValueMetadata -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem DataStageEffect.elements {M : Type} {store after : runtime.store.Store M}
    {index inst} (effect : DataStageEffect store index inst after) : after.elems = store.elems := by
  cases effect <;> rfl

theorem DataStageEffect.element_map {M : Type} {store after : runtime.store.Store M}
    {index inst next} (effect : DataStageEffect store index inst after)
    (found : store.instances.val[index.val]? = some inst)
    (nextFound : after.instances.val[index.val]? = some next) : next.elems = inst.elems := by
  cases effect with
  | unchanged =>
    have same := Option.some.inj (found.symm.trans nextFound)
    subst next
    rfl
  | appended datas addresses data stored mapped =>
    have bound := (List.getElem?_eq_some_iff.mp found).1
    simp only [alloc.vec.Vec.set_val_eq, List.getElem?_set, if_pos bound, ↓reduceIte, Option.some.injEq] at nextFound
    subst next
    rfl
end Itasca.Runtime.Store

end

/-! ## SegmentBoundsEffects -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem SegmentBounds.same {M : Type} {before after : runtime.store.Store M}
    (bounded : SegmentBounds before) (elements : after.elems = before.elems) (datas : after.datas = before.datas) :
    SegmentBounds after := by
  constructor
  · simpa [elements] using bounded.elements
  · simpa [datas] using bounded.data

/-- Data staging copies the accepted source payload exactly, hence cannot grow
it beyond its binary vector count. Allocation refusal leaves all bounds intact. -/
theorem add_instance_data_bounds {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (instIndex index : Usize) (inst : runtime.store.ModuleInst)
    (found : store.instances.val[instIndex.val]? = some inst)
    (bound : index.val < inst.module.module.tail.data.val.length)
    (room : store.datas.length < Usize.max) (mapRoom : inst.datas.length < Usize.max)
    (sourceBound : ∀ data ∈ inst.module.module.tail.data.val, data.init.length < 2^32)
    (bounded : SegmentBounds store) :
    runtime.store.instantiate.Store.add_instance_data memory allocator store instIndex index
      ⦃ out => SegmentBounds out.2 ⦄ := by
  have instanceBound : instIndex.val < store.instances.length := (List.getElem?_eq_some_iff.mp found).1
  have instanceRead : store.instances.val[instIndex.val] = inst := (List.getElem?_eq_some_iff.mp found).2
  apply WP.spec_mono (add_instance_data_effect memory allocator law store instIndex index instanceBound
    (by simpa only [instanceRead] using bound) room (by simpa only [instanceRead] using mapRoom))
  intro out effect
  rcases effect with ⟨error, rfl⟩ | ⟨bytes, datas, addresses, copied, appended, mapped, rfl⟩
  · exact bounded
  · constructor
    · exact bounded.elements
    · intro data member
      simp only [appended, List.mem_append, List.mem_singleton] at member
      rcases member with old | rfl
      · exact bounded.data data old
      · have source := sourceBound _ (List.getElem_mem bound)
        simpa only [alloc.vec.Vec.length, copied, instanceRead] using source
end Itasca.Runtime.Store

end

/-! ## ElementCompleteLoop -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem element_complete_staging_loop {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (before store : runtime.store.Store M) (platform : P) (instIndex start : Usize)
    (inst : runtime.store.ModuleInst) (status : core.result.Result Unit runtime.ExecError)
    (staged : StagedPrefix before store) (fresh : before.instances.length ≤ instIndex.val)
    (found : store.instances.val[instIndex.val]? = some inst)
    (compiled : Compiler.InitializerMappings inst.module)
    (valid : ∀ segment ∈ inst.module.module.env.elements.val,
      Itasca.ModuleSegments.elementValid inst.module.module.env segment)
    (bindings : InitializerBindings store inst) (imports : InitializerImports store inst)
    (segments : InitializerSegmentBindings store inst)
    (objectBound : objectCount store ≤ Usize.max)
    (startBound : start.val ≤ inst.module.module.env.elements.val.length)
    (storeCapacity : store.elems.length + (inst.module.module.env.elements.val.length - start.val) ≤ Usize.max)
    (mapCapacity : inst.elems.length + (inst.module.module.env.elements.val.length - start.val) ≤ Usize.max)
    (matching : status = .Ok () → ElementTypeMap store (inst.module.module.env.elements.val.take start.val) inst.elems.val)
    (contents : ElementContents store) :
    runtime.store.instantiate.Store.prepare_instance_loop8 memory hooks floats allocator store platform status start instIndex
      ⦃ out => ∃ after finalStatus,
        out = storeParts after platform finalStatus ∧ StagedPrefix before after ∧
        objectCount after ≤ Usize.max ∧ ElementContents after ∧ after.globals = store.globals ∧ (SegmentAccounting store → SegmentAccounting after) ∧
        InitializerFunctionMetadataAt store inst after instIndex ∧ ∃ next,
          after.instances.val[instIndex.val]? = some next ∧ next.module = inst.module ∧ next.globals = inst.globals ∧
          InitializerBindings after next ∧ InitializerImports after next ∧ InitializerSegmentBindings after next ∧
          after.datas = store.datas ∧ next.datas = inst.datas ∧
          (finalStatus = .Ok () → ElementTypeMap after inst.module.module.env.elements.val next.elems.val) ⦄ := by
  unfold runtime.store.instantiate.Store.prepare_instance_loop8
  apply loop.spec_decr_nat (fun state => inst.module.module.env.elements.val.length - state.2.2.2.val)
    (fun state => state.2.1 = platform ∧ StagedPrefix before state.1 ∧ objectCount state.1 ≤ Usize.max ∧ ElementContents state.1 ∧ state.1.globals = store.globals ∧ (SegmentAccounting store → SegmentAccounting state.1) ∧
      InitializerFunctionMetadataAt store inst state.1 instIndex ∧
      state.2.2.2.val ≤ inst.module.module.env.elements.val.length ∧
      ∃ currentInst, state.1.instances.val[instIndex.val]? = some currentInst ∧ currentInst.module = inst.module ∧ currentInst.globals = inst.globals ∧
        InitializerBindings state.1 currentInst ∧ InitializerImports state.1 currentInst ∧
        InitializerSegmentBindings state.1 currentInst ∧
        currentInst.elems.length + (inst.module.module.env.elements.val.length - state.2.2.2.val) ≤ Usize.max ∧
        state.1.elems.length + (inst.module.module.env.elements.val.length - state.2.2.2.val) ≤ Usize.max ∧
        state.1.datas = store.datas ∧ currentInst.datas = inst.datas ∧
        (state.2.2.1 = .Ok () → ElementTypeMap state.1 (inst.module.module.env.elements.val.take state.2.2.2.val) currentInst.elems.val))
  · rintro ⟨current, host, result, index⟩ ⟨hhost, hstaged, hobjects, hcontents, hglobals, haccounted, hmetadata, hindex,
      currentInst, hfound, hsource, hglobalMap, hbindings, himports, hsegments, hcapacity, hstoreCapacity, hdatas, hmapData, htyped⟩
    dsimp only at hhost hstaged hobjects hcontents hglobals haccounted hmetadata hindex hfound hsource hglobalMap hbindings himports hsegments hcapacity hstoreCapacity hdatas hmapData htyped ⊢
    subst host
    unfold runtime.store.instantiate.Store.prepare_instance_loop8.body
    step with Interp.vec_index_given current.instances instIndex currentInst hfound as ⟨actual, hactual⟩
    subst actual
    simp only [runtime.compiler.ExecutableModule.env,
      Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.elements, bind_ok, hsource]
    split
    · rename_i more
      have hmore : index.val < inst.module.module.env.elements.val.length := by
        simpa [alloc.vec.Vec.deref] using more
      cases result with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨current, .Err error, rfl, hstaged, hobjects, hcontents, hglobals, haccounted, hmetadata,
          currentInst, hfound, hsource, hglobalMap, hbindings, himports, hsegments, hdatas, hmapData, by simp⟩
      | Ok unitValue =>
        cases unitValue
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        let segment := inst.module.module.env.elements.val[index.val]
        have hsegment : currentInst.module.module.env.elements.val[index.val]? = some segment := by
          rw [hsource]
          exact List.getElem?_eq_getElem hmore
        have hvalid : Itasca.ModuleSegments.elementValid currentInst.module.module.env segment := by
          rw [hsource]
          exact valid segment (List.mem_of_getElem? (List.getElem?_eq_getElem hmore))
        have certificates := element_initializer_certificates current currentInst index segment
          (by simpa [hsource] using compiled) hsegment hvalid hbindings himports
        have room : current.elems.length < Usize.max := by omega
        have mapRoom : currentInst.elems.length < Usize.max := by omega
        step with add_instance_element_content_effect memory hooks floats allocator law current platform instIndex index
          currentInst segment hfound hsegment certificates hbindings room mapRoom
          as ⟨state, after, host', contentEffect, hhost'⟩
        subst host'
        have typedEffect := contentEffect.typed
        have effect := typedEffect.effect
        obtain ⟨nextInst, nextFound, nextSource, nextBindings, nextImports, nextSegments, nextSize, nextStoreSize, nextData⟩ :=
          effect.context hfound hbindings himports hsegments
        have nextMetadata : InitializerFunctionMetadataAt store inst after instIndex :=
          ⟨nextInst, nextFound, (hmetadata.resolve hfound).trans (effect.function_metadata hfound nextFound)⟩
        have nextStaged := effect.staged hstaged fresh
        have nextObjects : objectCount after ≤ Usize.max := by simpa only [effect.object_count] using hobjects
        have counterCapacity := inst.module.module.env.elements.property
        step as ⟨next, hnext⟩
        refine ⟨nextStaged, nextObjects, contentEffect.contents hcontents, effect.globals.trans hglobals, (fun h => effect.segment_accounting hfound (haccounted h)), nextMetadata, ?_, ⟨nextInst, nextFound,
          nextSource.trans hsource, (effect.global_map hfound nextFound).trans hglobalMap, nextBindings, nextImports, nextSegments, ?_,
          ?_, effect.data.trans hdatas, nextData.trans hmapData, ?_⟩, ?_⟩
        · omega
        · omega
        · omega
        · intro success
          have typed := typedEffect.type_map (List.getElem?_eq_some_iff.mp hfound).1 nextFound (htyped rfl) success
          simpa only [hnext, List.take_succ_eq_append_getElem hmore] using typed
        · omega
    · rename_i stopped
      have atEnd : index.val = inst.module.module.env.elements.val.length := by
        simp [alloc.vec.Vec.deref] at stopped
        omega
      simp only [WP.spec_ok]
      exact ⟨current, result, rfl, hstaged, hobjects, hcontents, hglobals, haccounted, hmetadata,
        currentInst, hfound, hsource, hglobalMap, hbindings, himports, hsegments, hdatas, hmapData, fun success => by simpa only [atEnd, List.take_length] using htyped success⟩
  · exact ⟨rfl, staged, objectBound, contents, rfl, (fun h => h), ⟨inst, found, .refl _ _⟩, startBound, inst, found, rfl, rfl, bindings, imports, segments, mapCapacity, storeCapacity, rfl, rfl, matching⟩

end Itasca.Runtime.Store

end

/-! ## InitializerMetadataCertificates -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
open Itasca.ModuleEnv

theorem InitializerFunctionMetadata.type_entries {M : Type}
    {store after : runtime.store.Store M} {inst next : runtime.store.ModuleInst}
    (metadata : InitializerFunctionMetadata store inst after next)
    {source : List Itasca.wasm_types.FuncType} (entries : TypeEntries store source inst.types.val) :
    TypeEntries after source next.types.val := by
  simpa only [TypeEntries, metadata.signatures, metadata.typeMap] using entries

theorem InitializerFunctionMetadata.function_table {M : Type}
    {store after : runtime.store.Store M} {inst next : runtime.store.ModuleInst}
    (metadata : InitializerFunctionMetadata store inst after next)
    {types : List functype} (table : Interp.FunctionTable store inst types) :
    Interp.FunctionTable after next types := by
  simpa only [Interp.FunctionTable, metadata.identity, metadata.functions,
    metadata.signatures, metadata.functionMap] using table

theorem InitializerFunctionMetadata.staged_functions {M : Type}
    {before store after : runtime.store.Store M} {inst next : runtime.store.ModuleInst}
    (metadata : InitializerFunctionMetadata store inst after next) {index : Usize}
    {types : List Itasca.wasm_types.FuncType} (staged : StagedFunctionSignatures before store index types) :
    StagedFunctionSignatures before after index types := by
  simpa only [StagedFunctionSignatures, metadata.functions, metadata.signatures] using staged

end Itasca.Runtime.Store

end

/-! ## ElementSourceLoop -/

section

/-!
Source values of allocated element segments. Constant evaluation and encoded pushes establish the source-element initializer loop relation.
-/

/-! ## Element Source Values -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

def ElementSourceValues (sourceStore : _root_.store) (sourceInstance : moduleinst)
    (ty : Itasca.wasm_types.ElemType) (expressions : List Itasca.wasm_types.ConstExpr) (words : List U64) : Prop :=
  List.Forall₂ (fun expr word => Eval_expr ⟨sourceStore, ⟨[], sourceInstance⟩⟩
    (Itasca.ModuleConstants.expression expr) ⟨sourceStore, ⟨[], sourceInstance⟩⟩
    [refVal (decodeRef ty word)]) expressions words

theorem eval_const_source {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex function : Usize)
    (inst : runtime.store.ModuleInst) (code : runtime.bytecode.CompiledFunction)
    (expr : Itasca.wasm_types.ConstExpr) (ty : Itasca.wasm_types.ValueType) (words : List U64)
    (found : store.instances.val[instIndex.val]? = some inst)
    (codeFound : inst.module.functions.val[function.val]? = some code)
    (compiled : Compiler.InitializerCode code expr ty)
    (resolved : Interp.InitializerResolution store inst expr ty words)
    (bindings : InitializerBindings store inst)
    (sourceStore : _root_.store) (sourceInstance : moduleinst)
    (storeWf : wf_store sourceStore) (frameWf : wf_frame ⟨[], sourceInstance⟩)
    (context : InitializerSourceContext sourceStore sourceInstance store inst)
    (valid : Itasca.ModuleConstants.Valid inst.module.module.env expr ty) :
    runtime.interp.eval_const memory hooks floats allocator store platform instIndex function ty
      ⦃ out => out.2.1 = store ∧ out.2.2 = platform ∧ ∀ value, out.1 = .Ok value →
        ValueInStore store value ∧ Interp.rawType value = ty ∧
        Eval_expr ⟨sourceStore, ⟨[], sourceInstance⟩⟩ (Itasca.ModuleConstants.expression expr)
          ⟨sourceStore, ⟨[], sourceInstance⟩⟩ [Interp.sourceValue value] ⦄ := by
  have exactValue := eval_const_effect memory hooks floats allocator law store platform instIndex function
    inst code expr ty words found codeFound compiled resolved (initializer_reference_bound resolved bindings)
  obtain ⟨result, run, owned⟩ := WP.spec_imp_exists
    (eval_const_owned memory hooks floats allocator law store platform instIndex function
      inst code expr ty words found codeFound compiled resolved bindings)
  rw [run] at exactValue ⊢
  simp only [WP.spec_ok] at exactValue ⊢
  refine ⟨owned.1, owned.2.1, ?_⟩
  intro value success
  refine ⟨(owned.2.2 value success).1, (owned.2.2 value success).2, ?_⟩
  rw [(exactValue.2.2 value success).2]
  exact context.expression valid resolved storeWf frameWf

theorem encode_push_source {M : Type} (store : runtime.store.Store M)
    (values : alloc.vec.Vec U64) (value : runtime.Value) (ty : Itasca.wasm_types.ElemType)
    (typed : elementValueType ty = Interp.rawType value) (owned : ValueInStore store value)
    (previous : ∀ word ∈ values.val, ReferenceShape store ty word)
    (room : values.length < Usize.max)
    (sourceStore : _root_.store) (sourceInstance : moduleinst)
    (expressions : List Itasca.wasm_types.ConstExpr) (expr : Itasca.wasm_types.ConstExpr)
    (matched : ElementSourceValues sourceStore sourceInstance ty expressions values.val)
    (evaluated : Eval_expr ⟨sourceStore, ⟨[], sourceInstance⟩⟩ (Itasca.ModuleConstants.expression expr)
      ⟨sourceStore, ⟨[], sourceInstance⟩⟩ [Interp.sourceValue value]) :
    (do let (lo, _) ← runtime.value.encode value
        let next ← alloc.vec.Vec.push values lo
        .ok (next, (core.result.Result.Ok () : core.result.Result Unit runtime.ExecError)))
      ⦃ out => out.1.length = values.length + 1 ∧ out.2 = .Ok () ∧
        (∀ word ∈ out.1.val, ReferenceShape store ty word) ∧
        ElementSourceValues sourceStore sourceInstance ty (expressions ++ [expr]) out.1.val ⦄ := by
  obtain ⟨pair, encoded, canonical⟩ := WP.spec_imp_exists (encode_reference_shape store value ty typed owned)
  rw [encoded, bind_ok]
  rcases pair with ⟨lo, hi⟩
  have decoded := decode_encoded_value store value owned (lo, hi) encoded
  rw [← typed] at decoded
  have exactRef : refVal (decodeRef ty lo) = Interp.sourceValue value := by
    cases ty <;> simpa only [elementValueType, decodeWords] using decoded
  step as ⟨next, stored⟩
  refine ⟨by simp [stored], ?_, ?_⟩
  · intro word member
    simp only [stored, List.mem_append, List.mem_singleton] at member
    rcases member with old | rfl
    · exact previous word old
    · exact canonical
  · unfold ElementSourceValues at matched ⊢
    rw [stored]
    exact List.rel_append matched (.cons (by simpa only [exactRef] using evaluated) .nil)
end Itasca.Runtime.Store

end

/-! ## Element Source Loop -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

private theorem elem_value_type_eq (ty : Itasca.wasm_types.ElemType) :
    wasm_types.ElemType.value_type ty = .ok (elementValueType ty) := by cases ty <;> rfl

theorem element_initializers_source_loop {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex index length : Usize)
    (inst : runtime.store.ModuleInst) (segment : Itasca.metadata.Element)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (helem : inst.module.module.env.elements.val[index.val]? = some segment)
    (hlength : length.val = segment.init.length)
    (certificates : ElementInitializers store inst index segment)
    (bindings : InitializerBindings store inst)
    (values : alloc.vec.Vec U64) (j : Usize) (status : core.result.Result Unit runtime.ExecError)
    (hvalues : values.length ≤ j.val) (hj : j.val ≤ length.val)
    (shaped : ∀ word ∈ values.val, ReferenceShape store segment.elem word)
    (sourceStore : _root_.store) (sourceInstance : moduleinst)
    (storeWf : wf_store sourceStore) (frameWf : wf_frame ⟨[], sourceInstance⟩)
    (context : InitializerSourceContext sourceStore sourceInstance store inst)
    (valid : ∀ expr ∈ segment.init.val,
      Itasca.ModuleConstants.Valid inst.module.module.env expr (elementValueType segment.elem))
    (matched : status = .Ok () → ElementSourceValues sourceStore sourceInstance segment.elem
      (segment.init.val.take j.val) values.val) :
    runtime.store.instantiate.Store.add_instance_element_loop memory hooks floats allocator store platform
      instIndex index length values j status ⦃ out =>
        out.1 = store ∧ out.2.1 = platform ∧ out.2.2.1.length ≤ length.val ∧
        (∀ word ∈ out.2.2.1.val, ReferenceShape store segment.elem word) ∧
        (out.2.2.2 = .Ok () → ElementSourceValues sourceStore sourceInstance segment.elem segment.init.val out.2.2.1.val) ⦄ := by
  have segmentLength : length.val = segment.init.val.length := hlength
  unfold runtime.store.instantiate.Store.add_instance_element_loop
  apply loop.spec_decr_nat (fun p => length.val - p.2.2.2.1.val)
    (fun p => p.1 = store ∧ p.2.1 = platform ∧
      p.2.2.1.length ≤ p.2.2.2.1.val ∧ p.2.2.2.1.val ≤ length.val ∧
      (∀ word ∈ p.2.2.1.val, ReferenceShape store segment.elem word) ∧
      (p.2.2.2.2 = .Ok () → ElementSourceValues sourceStore sourceInstance segment.elem
        (segment.init.val.take p.2.2.2.1.val) p.2.2.1.val))
  · rintro ⟨current, host, vals, k, state⟩ ⟨hcurrent, hhost, hvals, hk, refs, currentMatched⟩
    dsimp only at hcurrent hhost hvals hk refs currentMatched ⊢
    subst current host
    change vals.val.length ≤ k.val at hvals
    unfold runtime.store.instantiate.Store.add_instance_element_loop.body
    split
    · rename_i more
      have hmore : k.val < length.val := by scalar_tac
      cases state with
      | Err error =>
        simp [core.result.Result.is_ok]
        exact ⟨by omega, refs⟩
      | Ok unit =>
        cases unit
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        obtain ⟨functions, mapping, certificates⟩ := certificates
        obtain ⟨expr, function, code, words, hexpr, hfunction, hcode, compiled, resolved⟩ :=
          certificates k (by omega)
        step with Interp.vec_index_given store.instances instIndex inst hi as ⟨found, hfound⟩
        subst found
        step with Interp.vec_index_given inst.module.element_initializers index functions mapping
          as ⟨found, hfound⟩
        subst found
        step with Interp.vec_index_given functions k function hfunction as ⟨found, hfound⟩
        subst found
        simp only [runtime.compiler.ExecutableModule.env,
          Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.elements, bind_ok]
        step with Itasca.Runtime.Representation.slice_index_given inst.module.module.env.elements.deref index segment
          (by simpa [alloc.vec.Vec.deref] using helem) as ⟨found, hfound⟩
        subst found
        rw [elem_value_type_eq, bind_ok]
        step with eval_const_source memory hooks floats allocator law store platform instIndex function
          inst code expr (elementValueType segment.elem) words hi hcode compiled resolved bindings
          sourceStore sourceInstance storeWf frameWf context
          (valid expr (List.mem_of_getElem? hexpr))
          as ⟨result, after, host', hs, hp, hvalue⟩
        subst after host'
        cases result with
        | Err error =>
          step as ⟨next, hnext⟩
          change vals.val.length ≤ next.val ∧ next.val ≤ length.val ∧
            (∀ word ∈ vals.val, ReferenceShape store segment.elem word) ∧
            ((core.result.Result.Err error : core.result.Result Unit runtime.ExecError) = .Ok () → _ ) ∧
            length.val - next.val < length.val - k.val
          exact ⟨by omega, by omega, refs, by simp, by omega⟩
        | Ok value =>
          obtain ⟨owned, typed, evaluated⟩ := hvalue value rfl
          have room : vals.length < Usize.max := by scalar_tac
          apply WP.spec_bind (encode_push_source store vals value segment.elem typed.symm owned refs room
            sourceStore sourceInstance (segment.init.val.take k.val) expr (currentMatched rfl) evaluated)
          rintro ⟨pushed, nextStatus⟩ ⟨hpush, hstatus, pushedRefs, pushedMatched⟩
          step as ⟨next, hnext⟩
          refine ⟨?_, by omega, pushedRefs, ?_, by omega⟩
          · rw [hpush]
            change vals.val.length + 1 ≤ next.val
            omega
          · intro _
            rw [hnext, List.take_succ_eq_append_getElem (by omega)]
            have exprEq := (List.getElem?_eq_some_iff.mp hexpr).2
            simpa only [exprEq] using pushedMatched
    · have hstop : length.val ≤ k.val := by scalar_tac
      simp only [WP.spec_ok]
      simp only [true_and]
      change vals.val.length ≤ length.val ∧ (∀ word ∈ vals.val, ReferenceShape store segment.elem word) ∧
        (state = .Ok () → ElementSourceValues sourceStore sourceInstance segment.elem segment.init.val vals.val)
      refine ⟨by omega, refs, ?_⟩
      intro success
      have atEnd : k.val = segment.init.val.length := by omega
      simpa only [atEnd, List.take_length] using currentMatched success
  · exact ⟨rfl, rfl, hvalues, hj, shaped, matched⟩

end Itasca.Runtime.Store

end

end

/-! ## ElementValues -/

section

/-!
Allocated element values and their decoded source-segment relation. Typed content and loop shape remain lower certificates used independently by initialization.
-/

/-! ## Element Value Effect -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

inductive ElementValueEffect {M : Type} (sourceStore : _root_.store) (sourceInstance : moduleinst)
    (store : runtime.store.Store M) (instIndex : Usize) (inst : runtime.store.ModuleInst)
    (source : Itasca.metadata.Element) : core.result.Result Unit runtime.ExecError → runtime.store.Store M → Prop where
  | failed (error : runtime.ExecError) : ElementValueEffect sourceStore sourceInstance store instIndex inst source (.Err error) store
  | appended (elements : alloc.vec.Vec runtime.store.ElemInst) (addresses : alloc.vec.Vec Usize)
      (values : alloc.vec.Vec U64)
      (elementValues : elements.val = store.elems.val ++ [{ty := source.elem, refs := values}])
      (addressValues : addresses.val = inst.elems.val ++ [store.elems.len])
      (canonical : ∀ word ∈ values.val, ReferenceShape store source.elem word)
      (evaluated : ElementSourceValues sourceStore sourceInstance source.elem source.init.val values.val) :
      ElementValueEffect sourceStore sourceInstance store instIndex inst source (.Ok ())
        {store with elems := elements, instances := store.instances.set instIndex {inst with elems := addresses}}

theorem ElementValueEffect.content {M : Type} {sourceStore sourceInstance}
    {store after : runtime.store.Store M} {instIndex inst source status}
    (effect : ElementValueEffect sourceStore sourceInstance store instIndex inst source status after) :
    ElementContentEffect store instIndex inst source status after := by
  cases effect with
  | failed error => exact .failed error
  | appended elements addresses values stored mapped canonical evaluated =>
    exact .appended elements addresses values stored mapped canonical

theorem add_instance_element_value_effect {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex index : Usize)
    (inst : runtime.store.ModuleInst) (segment : Itasca.metadata.Element)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (helem : inst.module.module.env.elements.val[index.val]? = some segment)
    (certificates : ElementInitializers store inst index segment)
    (bindings : InitializerBindings store inst)
    (room : store.elems.length < Usize.max) (mapRoom : inst.elems.length < Usize.max)
    (sourceStore : _root_.store) (sourceInstance : moduleinst)
    (storeWf : wf_store sourceStore) (frameWf : wf_frame ⟨[], sourceInstance⟩)
    (context : InitializerSourceContext sourceStore sourceInstance store inst)
    (valid : ∀ expr ∈ segment.init.val,
      Itasca.ModuleConstants.Valid inst.module.module.env expr (elementValueType segment.elem)) :
    runtime.store.instantiate.Store.add_instance_element memory hooks floats allocator store platform instIndex index
      ⦃ out => ElementValueEffect sourceStore sourceInstance store instIndex inst segment out.1 out.2.1 ∧ out.2.2 = platform ⦄ := by
  unfold runtime.store.instantiate.Store.add_instance_element
  step with Interp.vec_index_given store.instances instIndex inst hi as ⟨found, hfound⟩
  subst found
  simp only [runtime.compiler.ExecutableModule.env,
    Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.elements, bind_ok]
  step with Itasca.Runtime.Representation.slice_index_given inst.module.module.env.elements.deref index segment
    (by simpa [alloc.vec.Vec.deref] using helem) as ⟨found, hfound⟩
  subst found
  obtain ⟨reserved, hreserve⟩ := reserve_wrapper_eq allocator law (alloc.vec.Vec.new U64) segment.init.len
  rw [hreserve]
  cases reserved with
  | false =>
    simpa [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using (ElementValueEffect.failed (sourceStore := sourceStore) (sourceInstance := sourceInstance) (store := store) (instIndex := instIndex) (inst := inst) (source := segment) (.Exhausted .Allocation))
  | true =>
    simp only [↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with element_initializers_source_loop memory hooks floats allocator law store platform instIndex index
      segment.init.len inst segment hi helem (by simp) certificates bindings
      (alloc.vec.Vec.new U64) 0#usize (.Ok ()) (by simp) (by scalar_tac) (by simp)
      sourceStore sourceInstance storeWf frameWf context valid (by simp [ElementSourceValues])
      as ⟨after, host, values, status, hs, hp, hvalues, refs, evaluated⟩
    subst after host
    cases status with
    | Err error =>
      simpa [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using (ElementValueEffect.failed (sourceStore := sourceStore) (sourceInstance := sourceInstance) (store := store) (instIndex := instIndex) (inst := inst) (source := segment) error)
    | Ok unit =>
      cases unit
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      obtain ⟨reserved, hreserve⟩ := reserve_wrapper_eq allocator law store.elems 1#usize
      rw [hreserve]
      cases reserved with
      | false =>
        simpa [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using (ElementValueEffect.failed (sourceStore := sourceStore) (sourceInstance := sourceInstance) (store := store) (instIndex := instIndex) (inst := inst) (source := segment) (.Exhausted .Allocation))
      | true =>
        simp only [↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        step with Interp.vec_index_given store.instances instIndex inst hi as ⟨found, hfound⟩
        subst found
        step with Itasca.Runtime.Representation.slice_index_given inst.module.module.env.elements.deref index segment
          (by simpa [alloc.vec.Vec.deref] using helem) as ⟨found, hfound⟩
        subst found
        step as ⟨elements, helements⟩
        have instanceBound : instIndex.val < store.instances.length :=
          (List.getElem?_eq_some_iff.mp hi).1
        step as ⟨old, back, hold, hback⟩
        have old_eq : old = inst := by
          have hread := List.getElem?_eq_getElem instanceBound
          rw [hi] at hread
          exact hold.trans (Option.some.inj hread).symm
        subst old
        step as ⟨addresses, haddresses⟩
        have instanceRead : store.instances.val[instIndex.val] = inst :=
          Option.some.inj ((List.getElem?_eq_getElem instanceBound).symm.trans hi)
        have effect := ElementValueEffect.appended (sourceStore := sourceStore) (sourceInstance := sourceInstance) (store := store) (instIndex := instIndex) (inst := inst) (source := segment)
          elements addresses values helements
          (by simpa only [instanceRead] using haddresses) refs (evaluated rfl)
        simpa [hback, instanceRead] using And.intro effect (rfl : platform = platform)


end Itasca.Runtime.Store

end

/-! ## Element Value Source -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

def ElementSourceSegments (sourceStore : _root_.store) (sourceInstance : moduleinst)
    (source : List Itasca.metadata.Element) (values : List runtime.store.ElemInst) : Prop :=
  List.Forall₂ (fun original actual => actual.ty = original.elem ∧
    ElementSourceValues sourceStore sourceInstance original.elem original.init.val actual.refs.val) source values

theorem ElementStageEffect.source_context {M : Type} {store after : runtime.store.Store M}
    {instIndex inst next sourceStore sourceInstance}
    (effect : ElementStageEffect store instIndex inst after)
    (found : store.instances.val[instIndex.val]? = some inst)
    (nextFound : after.instances.val[instIndex.val]? = some next)
    (context : InitializerSourceContext sourceStore sourceInstance store inst) :
    InitializerSourceContext sourceStore sourceInstance after next := by
  cases effect with
  | unchanged =>
    have same := Option.some.inj (found.symm.trans nextFound)
    subst next
    exact context
  | appended elements addresses element stored mapped =>
    have bound := (List.getElem?_eq_some_iff.mp found).1
    simp only [alloc.vec.Vec.set_val_eq, List.getElem?_set, if_pos bound, ↓reduceIte, Option.some.injEq] at nextFound
    subst next
    exact ⟨context.functions, context.globals⟩

theorem ElementValueEffect.source_values {M : Type} {store after : runtime.store.Store M}
    {instIndex inst sourceStore sourceInstance status}
    {original : Itasca.metadata.Element}
    (effect : ElementValueEffect sourceStore sourceInstance store instIndex inst original status after)
    {sources : List Itasca.metadata.Element} {base produced : List runtime.store.ElemInst}
    (stored : store.elems.val = base ++ produced)
    (previous : ElementSourceSegments sourceStore sourceInstance sources produced)
    (success : status = .Ok ()) :
    ∃ values, after.elems.val = base ++ values ∧
      ElementSourceSegments sourceStore sourceInstance (sources ++ [original]) values := by
  cases effect with
  | failed error => simp at success
  | appended elements addresses values entries mapped canonical evaluated =>
    refine ⟨produced ++ [{ty := original.elem, refs := values}], ?_, ?_⟩
    · simpa only [stored, List.append_assoc] using entries
    · exact List.rel_append previous (.cons ⟨rfl, evaluated⟩ .nil)
end Itasca.Runtime.Store

end

end

/-! ## ElementSourceStaging -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem element_source_staging_loop {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (before store : runtime.store.Store M) (platform : P) (instIndex start : Usize)
    (inst : runtime.store.ModuleInst) (status : core.result.Result Unit runtime.ExecError)
    (staged : StagedPrefix before store) (fresh : before.instances.length ≤ instIndex.val)
    (found : store.instances.val[instIndex.val]? = some inst)
    (compiled : Compiler.InitializerMappings inst.module)
    (valid : ∀ segment ∈ inst.module.module.env.elements.val,
      Itasca.ModuleSegments.elementValid inst.module.module.env segment)
    (bindings : InitializerBindings store inst) (imports : InitializerImports store inst)
    (segments : InitializerSegmentBindings store inst)
    (objectBound : objectCount store ≤ Usize.max)
    (startBound : start.val ≤ inst.module.module.env.elements.val.length)
    (storeCapacity : store.elems.length + (inst.module.module.env.elements.val.length - start.val) ≤ Usize.max)
    (mapCapacity : inst.elems.length + (inst.module.module.env.elements.val.length - start.val) ≤ Usize.max)
    (sourceStore : _root_.store) (sourceInstance : moduleinst)
    (storeWf : wf_store sourceStore) (frameWf : wf_frame ⟨[], sourceInstance⟩)
    (sourceContext : InitializerSourceContext sourceStore sourceInstance store inst)
    (baseElements : List runtime.store.ElemInst)
    (matching : status = .Ok () → ∃ produced, store.elems.val = baseElements ++ produced ∧
      ElementSourceSegments sourceStore sourceInstance
        (inst.module.module.env.elements.val.take start.val) produced) :
    runtime.store.instantiate.Store.prepare_instance_loop8 memory hooks floats allocator store platform status start instIndex
      ⦃ out => ∃ after finalStatus,
        out = storeParts after platform finalStatus ∧ StagedPrefix before after ∧
        objectCount after ≤ Usize.max ∧ (SegmentAccounting store → SegmentAccounting after) ∧
        InitializerFunctionMetadataAt store inst after instIndex ∧ ∃ next,
          after.instances.val[instIndex.val]? = some next ∧ next.module = inst.module ∧
          InitializerBindings after next ∧ InitializerImports after next ∧ InitializerSegmentBindings after next ∧
          after.datas = store.datas ∧ next.datas = inst.datas ∧ after.globals = store.globals ∧ next.globals = inst.globals ∧
          InitializerSourceContext sourceStore sourceInstance after next ∧
          (finalStatus = .Ok () → ∃ produced, after.elems.val = baseElements ++ produced ∧
            ElementSourceSegments sourceStore sourceInstance inst.module.module.env.elements.val produced) ⦄ := by
  unfold runtime.store.instantiate.Store.prepare_instance_loop8
  apply loop.spec_decr_nat (fun state => inst.module.module.env.elements.val.length - state.2.2.2.val)
    (fun state => state.2.1 = platform ∧ StagedPrefix before state.1 ∧ objectCount state.1 ≤ Usize.max ∧ (SegmentAccounting store → SegmentAccounting state.1) ∧
      InitializerFunctionMetadataAt store inst state.1 instIndex ∧
      state.2.2.2.val ≤ inst.module.module.env.elements.val.length ∧
      ∃ currentInst, state.1.instances.val[instIndex.val]? = some currentInst ∧ currentInst.module = inst.module ∧
        InitializerBindings state.1 currentInst ∧ InitializerImports state.1 currentInst ∧
        InitializerSegmentBindings state.1 currentInst ∧
        currentInst.elems.length + (inst.module.module.env.elements.val.length - state.2.2.2.val) ≤ Usize.max ∧
        state.1.elems.length + (inst.module.module.env.elements.val.length - state.2.2.2.val) ≤ Usize.max ∧
        state.1.datas = store.datas ∧ currentInst.datas = inst.datas ∧ state.1.globals = store.globals ∧ currentInst.globals = inst.globals ∧
        InitializerSourceContext sourceStore sourceInstance state.1 currentInst ∧
        (state.2.2.1 = .Ok () → ∃ produced, state.1.elems.val = baseElements ++ produced ∧
          ElementSourceSegments sourceStore sourceInstance
            (inst.module.module.env.elements.val.take state.2.2.2.val) produced))
  · rintro ⟨current, host, result, index⟩ ⟨hhost, hstaged, hobjects, haccounted, hmetadata, hindex,
      currentInst, hfound, hsource, hbindings, himports, hsegments, hcapacity, hstoreCapacity, hdatas, hmapData, hglobals, hglobalMap, hcontext, hmatching⟩
    dsimp only at hhost hstaged hobjects haccounted hmetadata hindex hfound hsource hbindings himports hsegments hcapacity hstoreCapacity hdatas hmapData hglobals hglobalMap hcontext hmatching ⊢
    subst host
    unfold runtime.store.instantiate.Store.prepare_instance_loop8.body
    step with Interp.vec_index_given current.instances instIndex currentInst hfound as ⟨actual, hactual⟩
    subst actual
    simp only [runtime.compiler.ExecutableModule.env,
      Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.elements, bind_ok, hsource]
    split
    · rename_i more
      have hmore : index.val < inst.module.module.env.elements.val.length := by
        simpa [alloc.vec.Vec.deref] using more
      cases result with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨current, .Err error, rfl, hstaged, hobjects, haccounted, hmetadata,
          currentInst, hfound, hsource, hbindings, himports, hsegments, hdatas, hmapData, hglobals, hglobalMap, hcontext, by simp⟩
      | Ok unitValue =>
        cases unitValue
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        let segment := inst.module.module.env.elements.val[index.val]
        have hsegment : currentInst.module.module.env.elements.val[index.val]? = some segment := by
          rw [hsource]
          exact List.getElem?_eq_getElem hmore
        have hvalid : Itasca.ModuleSegments.elementValid currentInst.module.module.env segment := by
          rw [hsource]
          exact valid segment (List.mem_of_getElem? (List.getElem?_eq_getElem hmore))
        have certificates := element_initializer_certificates current currentInst index segment
          (by simpa [hsource] using compiled) hsegment hvalid hbindings himports
        have room : current.elems.length < Usize.max := by omega
        have mapRoom : currentInst.elems.length < Usize.max := by omega
        step with add_instance_element_value_effect memory hooks floats allocator law current platform instIndex index
          currentInst segment hfound hsegment certificates hbindings room mapRoom
          sourceStore sourceInstance storeWf frameWf hcontext
          (by
            have sameType : Itasca.ModuleConstants.referenceValueType segment.elem = elementValueType segment.elem := by
              cases segment.elem <;> rfl
            simpa only [sameType] using hvalid.2)
          as ⟨state, after, host', valueEffect, hhost'⟩
        have effect := valueEffect.content.typed.effect
        subst host'
        obtain ⟨nextInst, nextFound, nextSource, nextBindings, nextImports, nextSegments, nextSize, nextStoreSize, nextData⟩ :=
          effect.context hfound hbindings himports hsegments
        have nextMetadata : InitializerFunctionMetadataAt store inst after instIndex :=
          ⟨nextInst, nextFound, (hmetadata.resolve hfound).trans (effect.function_metadata hfound nextFound)⟩
        have nextStaged := effect.staged hstaged fresh
        have nextObjects : objectCount after ≤ Usize.max := by simpa only [effect.object_count] using hobjects
        have counterCapacity := inst.module.module.env.elements.property
        step as ⟨next, hnext⟩
        refine ⟨nextStaged, nextObjects, (fun h => effect.segment_accounting hfound (haccounted h)), nextMetadata, ?_, ⟨nextInst, nextFound,
          nextSource.trans hsource, nextBindings, nextImports, nextSegments, ?_,
          ?_, effect.data.trans hdatas, nextData.trans hmapData, effect.globals.trans hglobals, (effect.global_map hfound nextFound).trans hglobalMap, effect.source_context hfound nextFound hcontext, ?_⟩, ?_⟩
        · omega
        · omega
        · omega
        · intro success
          obtain ⟨produced, stored, previous⟩ := hmatching rfl
          obtain ⟨values, storedNext, nextValues⟩ := valueEffect.source_values stored previous success
          refine ⟨values, storedNext, ?_⟩
          rw [hnext, List.take_succ_eq_append_getElem hmore]
          exact nextValues
        · omega
    · rename_i stopped
      have atEnd : index.val = inst.module.module.env.elements.val.length := by
        simp [alloc.vec.Vec.deref] at stopped
        omega
      simp only [WP.spec_ok]
      refine ⟨current, result, rfl, hstaged, hobjects, haccounted, hmetadata,
        currentInst, hfound, hsource, hbindings, himports, hsegments, hdatas, hmapData, hglobals, hglobalMap, hcontext, ?_⟩
      simpa only [atEnd, List.take_length] using hmatching
  · exact ⟨rfl, staged, objectBound, (fun h => h), ⟨inst, found, .refl _ _⟩, startBound, inst, found, rfl, bindings, imports, segments, mapCapacity, storeCapacity, rfl, rfl, rfl, rfl, sourceContext, matching⟩

end Itasca.Runtime.Store

end
