import Itasca.Generated.FunsInstantiate
import Itasca.Runtime.Store.Invariant.ErrorPost
import Itasca.Runtime.Store.Initialization.InitializerErrors
import Itasca.Runtime.Compiler.Local.Initializer.InitializerElementAppend
import Itasca.Runtime.Store.Initialization.ElementShapeLoop
import Itasca.Runtime.Store.Api.TableInitLists
import Itasca.Runtime.Store.Api.MemoryBindingLoop
import Itasca.Runtime.Store.Initialization.SegmentExtension
import Itasca.Runtime.Store.Invariant.AllocatedMemoryLoop
import Itasca.Runtime.Store.Initialization.ElementTypes
import Itasca.Runtime.Store.Preparation.AllocationTableMemory
import Itasca.Runtime.Store.Invariant.FunctionStaging
import Itasca.Runtime.Store.Preparation.PreparationResults

/-!
Sections, each formerly its own module: GlobalErrors, GlobalLoop, GlobalErrorLoop, TableTypes, GlobalLoopCertificates, GlobalMapPreservation, TableMemoryOrder, MemoryAllocationLoop.
-/

/-! ## GlobalErrors -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

theorem add_global_errors {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex index : Usize)
    (inst : runtime.store.ModuleInst) (global : Itasca.metadata.Global)
    (function : Usize) (code : runtime.bytecode.CompiledFunction) (words : List U64)
    (hi : store.instances.val[instIndex.val]? = some inst)
    (hg : inst.module.module.env.globals.val[index.val]? = some global)
    (hmapping : inst.module.global_initializers.val[index.val]? = some function)
    (hc : inst.module.functions.val[function.val]? = some code)
    (compiled : Compiler.InitializerCode code global.init global.gtype.valtype)
    (resolved : Interp.InitializerResolution store inst global.init global.gtype.valtype words)
    (bindings : InitializerBindings store inst)
    (out : core.result.Result Unit runtime.ExecError × runtime.store.Store M × P)
    (run : runtime.store.instantiate.Store.add_instance_global memory hooks floats allocator store platform instIndex index = .ok out) :
    ErrorAllowed ResourceError out.1 := by
  obtain ⟨evaluated, evalRun, sameStore, sameHost, success⟩ := WP.spec_imp_exists
    (eval_const_owned memory hooks floats allocator law store platform instIndex function
      inst code global.init global.gtype.valtype words hi hc compiled resolved bindings)
  rcases evaluated with ⟨value, after, host⟩
  dsimp only at sameStore sameHost success evalRun
  subst after host
  have errors := eval_const_errors memory hooks floats allocator law store platform instIndex function
    inst code global.init global.gtype.valtype words hi hc compiled resolved
    (initializer_reference_bound resolved bindings)
  rw [evalRun] at errors
  simp only [WP.spec_ok] at errors
  unfold runtime.store.instantiate.Store.add_instance_global at run
  simp only [Compiler.initializer_vec_index store.instances instIndex inst hi,
    runtime.compiler.ExecutableModule.env, Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.globals, bind_ok] at run
  rw [Compiler.initializer_slice_index inst.module.module.env.globals.deref index global (by simpa [alloc.vec.Vec.deref] using hg)] at run
  simp only [bind_ok,
    Compiler.initializer_vec_index inst.module.global_initializers index function hmapping,
    evalRun] at run
  cases value with
  | Err error =>
    obtain ⟨resource, rfl⟩ := errors.2.2.2 error rfl
    repeat' allocation_error_step run using allocator, law
  | Ok value =>
    obtain ⟨owned, typed⟩ := success value rfl
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at run
    obtain ⟨⟨status, after⟩, defined, rest⟩ := normal_bind_exists _ _ _ run
    have cause := define_global_errors memory allocator law store global.gtype value typed.symm owned.1 _ defined
    clear run
    rename' rest => run
    repeat' allocation_error_step run using allocator, law

end Itasca.Runtime.Store

end

/-! ## GlobalLoop -/

section

/-! The actual staged global loop preserves pre-existing store objects and the
linked initializer context through all allocation/refusal branches. -/
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

def InitializerContext {M : Type} (store : runtime.store.Store M) (index : Usize)
    (module : runtime.compiler.ExecutableModule) : Prop :=
  ∃ inst, store.instances.val[index.val]? = some inst ∧ inst.module = module ∧
    InitializerBindings store inst ∧ InitializerImports store inst ∧ InitializerSegmentBindings store inst

end Itasca.Runtime.Store

end

/-! ## GlobalErrorLoop -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
theorem global_staging_loop_errors {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (before store : runtime.store.Store M) (platform : P) (instIndex start : Usize)
    (inst : runtime.store.ModuleInst) (status : core.result.Result Unit runtime.ExecError)
    (allowed : ErrorAllowed ResourceError status)
    (staged : StagedPrefix before store) (fresh : before.instances.length ≤ instIndex.val)
    (found : store.instances.val[instIndex.val]? = some inst)
    (compiled : Compiler.InitializerMappings inst.module)
    (valid : ∀ global ∈ inst.module.module.env.globals.val,
      Itasca.ModuleConstants.Valid inst.module.module.env global.init global.gtype.valtype)
    (bindings : InitializerBindings store inst) (imports : InitializerImports store inst)
    (segments : InitializerSegmentBindings store inst)
    (objectBound : objectCount store ≤ Usize.max)
    (startBound : start.val ≤ inst.module.module.env.globals.val.length)
    (mapCapacity : inst.globals.length + (inst.module.module.env.globals.val.length - start.val) ≤ Usize.max) :
    runtime.store.instantiate.Store.prepare_instance_loop7 memory hooks floats allocator store platform status start instIndex
      ⦃ out => ∃ after finalStatus,
        out = storeParts after platform finalStatus ∧ ErrorAllowed ResourceError finalStatus ∧ StagedPrefix before after ∧
        objectCount after ≤ Usize.max ∧ (SegmentAccounting store → SegmentAccounting after) ∧
        InitializerFunctionMetadataAt store inst after instIndex ∧ ∃ next,
          after.instances.val[instIndex.val]? = some next ∧ next.module = inst.module ∧
          InitializerBindings after next ∧ InitializerImports after next ∧ InitializerSegmentBindings after next ∧
          after.elems = store.elems ∧ after.datas = store.datas ∧ next.elems = inst.elems ∧ next.datas = inst.datas ⦄ := by
  unfold runtime.store.instantiate.Store.prepare_instance_loop7
  apply loop.spec_decr_nat (fun state => inst.module.module.env.globals.val.length - state.2.2.2.val)
    (fun state => state.2.1 = platform ∧ ErrorAllowed ResourceError state.2.2.1 ∧ StagedPrefix before state.1 ∧ objectCount state.1 ≤ Usize.max ∧ (SegmentAccounting store → SegmentAccounting state.1) ∧
      InitializerFunctionMetadataAt store inst state.1 instIndex ∧
      state.2.2.2.val ≤ inst.module.module.env.globals.val.length ∧
      ∃ currentInst, state.1.instances.val[instIndex.val]? = some currentInst ∧ currentInst.module = inst.module ∧
        InitializerBindings state.1 currentInst ∧ InitializerImports state.1 currentInst ∧
        InitializerSegmentBindings state.1 currentInst ∧
        currentInst.globals.length + (inst.module.module.env.globals.val.length - state.2.2.2.val) ≤ Usize.max ∧
        state.1.elems = store.elems ∧ state.1.datas = store.datas ∧ currentInst.elems = inst.elems ∧ currentInst.datas = inst.datas)
  · rintro ⟨current, host, result, index⟩ ⟨hhost, errors, hstaged, hobjects, haccounted, hmetadata, hindex,
      currentInst, hfound, hsource, hbindings, himports, hsegments, hcapacity, helements, hdatas, hmapElements, hmapData⟩
    dsimp only at hhost errors hstaged hobjects haccounted hmetadata hindex hfound hsource hbindings himports hsegments hcapacity helements hdatas hmapElements hmapData ⊢
    subst host
    unfold runtime.store.instantiate.Store.prepare_instance_loop7.body
    step with Interp.vec_index_given current.instances instIndex currentInst hfound as ⟨actual, hactual⟩
    subst actual
    simp only [runtime.compiler.ExecutableModule.env,
      Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.globals, bind_ok, hsource]
    split
    · rename_i more
      have hmore : index.val < inst.module.module.env.globals.val.length := by
        simpa [alloc.vec.Vec.deref] using more
      cases result with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨current, .Err error, rfl, errors, hstaged, hobjects, haccounted, hmetadata,
          currentInst, hfound, hsource, hbindings, himports, hsegments, helements, hdatas, hmapElements, hmapData⟩
      | Ok unitValue =>
        cases unitValue
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        let global := inst.module.module.env.globals.val[index.val]
        have hglobal : currentInst.module.module.env.globals.val[index.val]? = some global := by
          rw [hsource]
          exact List.getElem?_eq_getElem hmore
        have hvalid : Itasca.ModuleConstants.Valid currentInst.module.module.env global.init global.gtype.valtype := by
          rw [hsource]
          exact valid global (List.mem_of_getElem? (List.getElem?_eq_getElem hmore))
        obtain ⟨function, code, words, hmapping, hc, hcompiled, hresolved⟩ :=
          global_initializer_certificate current currentInst index global (by simpa [hsource] using compiled)
            hglobal hvalid hbindings himports
        have room : currentInst.globals.length < Usize.max := by omega
        step with normal_return_post
          (add_instance_global_effect memory hooks floats allocator law current platform instIndex index
            currentInst global function code words hfound hglobal hmapping hc hcompiled hresolved hbindings hobjects room)
          (fun out called => add_global_errors memory hooks floats allocator law current platform instIndex index
            currentInst global function code words hfound hglobal hmapping hc hcompiled hresolved hbindings out called)
          as ⟨state, after, host', effect, hhost', nextErrors⟩
        subst host'
        obtain ⟨nextInst, nextFound, nextSource, nextBindings, nextImports, nextSegments, nextSize, nextElements, nextData⟩ :=
          effect.context hfound hbindings himports hsegments
        have nextMetadata : InitializerFunctionMetadataAt store inst after instIndex :=
          ⟨nextInst, nextFound, (hmetadata.resolve hfound).trans (effect.function_metadata hfound nextFound)⟩
        have nextStaged := effect.staged hstaged fresh
        have nextObjects := effect.object_bound hobjects
        have counterCapacity := inst.module.module.env.globals.property
        step as ⟨next, hnext⟩
        refine ⟨nextErrors, nextStaged, nextObjects, (fun h => effect.segment_accounting hfound (haccounted h)), nextMetadata, ?_, ⟨nextInst, nextFound,
          nextSource.trans hsource, nextBindings, nextImports, nextSegments, ?_,
          effect.segments.1.trans helements, effect.segments.2.trans hdatas,
          nextElements.trans hmapElements, nextData.trans hmapData⟩, ?_⟩
        · omega
        · omega
        · omega
    · simp only [WP.spec_ok]
      exact ⟨current, result, rfl, errors, hstaged, hobjects, haccounted, hmetadata,
        currentInst, hfound, hsource, hbindings, himports, hsegments, helements, hdatas, hmapElements, hmapData⟩
  · exact ⟨rfl, allowed, staged, objectBound, (fun h => h), ⟨inst, found, .refl _ _⟩, startBound, inst, found, rfl, bindings, imports, segments, mapCapacity, rfl, rfl, rfl, rfl⟩

end Itasca.Runtime.Store

end

/-! ## TableTypes -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

def TableTypeMap {M : Type} (store : runtime.store.Store M)
    (types : List Itasca.wasm_types.TableType) (addresses : List runtime.TableAddr) : Prop :=
  List.Forall₂ (fun ty address => ∃ table, store.tables.val[address.index.val]? = some table ∧ table.ty = ty.elem) types addresses

theorem TableTypeMap.prefix {M : Type} {store after : runtime.store.Store M} {types addresses}
    (matching : TableTypeMap store types addresses) (retained : after.tables.val.take store.tables.length = store.tables.val) :
    TableTypeMap after types addresses := by
  apply matching.imp
  rintro ty address ⟨table, found, equal⟩
  refine ⟨table, ?_, equal⟩
  have bound := (List.getElem?_eq_some_iff.mp found).1
  have lookup := congrArg (fun values : List runtime.store.TableInst => values[address.index.val]?) retained
  simp only [List.getElem?_take, alloc.vec.Vec.length, if_pos bound] at lookup
  exact lookup.trans found

theorem LinkedMaps.table_types {M : Type} {view : M → Slice U8} {store : runtime.store.Store M}
    {module entries inst} (linked : LinkedMaps view store module entries inst) :
    TableTypeMap store (Itasca.ModuleEnv.importedTables entries) inst.tables.val := by
  apply linked.tables.imp
  rintro ty address ⟨owner, table, found, typeEq, limits⟩
  exact ⟨table, found, typeEq⟩

theorem TableStageEffect.table_types {M : Type} {store : runtime.store.Store M}
    {inst : runtime.store.ModuleInst} {ty out} (effect : TableStageEffect store inst ty out)
    {types : List Itasca.wasm_types.TableType} (matching : TableTypeMap store types inst.tables.val)
    (success : out.1 = .Ok ()) : TableTypeMap out.2.1 (types ++ [ty]) out.2.2.tables.val := by
  rcases effect with ⟨error, rfl⟩ | ⟨tables, elements, addresses, count, zeros, appended, mapped, limits, capacity, counter, budget, rfl⟩
  · simp at success
  · have old := matching.prefix (after := {store with tables, table_elements := count}) (by simp [appended])
    change List.Forall₂ _ _ addresses.val
    rw [mapped]
    apply List.rel_append old
    exact .cons ⟨{elements, ty := ty.elem, maximum := ty.limits.max}, by simp [appended], rfl⟩ .nil

theorem TableTypeMap.bindings {M : Type} {store : runtime.store.Store M} {inst : runtime.store.ModuleInst}
    (matching : TableTypeMap store inst.module.module.env.table_types.val inst.tables.val) :
    ∀ (index : Nat) (source : Itasca.wasm_types.TableType) (address : runtime.TableAddr) (table : runtime.store.TableInst),
      inst.module.module.env.table_types.val[index]? = some source → inst.tables.val[index]? = some address →
      store.tables.val[address.index.val]? = some table → table.ty = source.elem := by
  intro index source address table sourceFound mapped found
  have left := (List.getElem?_eq_some_iff.mp sourceFound).1
  have right := (List.getElem?_eq_some_iff.mp mapped).1
  have related := matching.get left right
  simp only [List.get_eq_getElem] at related
  have sourceEq := (List.getElem?_eq_some_iff.mp sourceFound).2
  have addressEq := (List.getElem?_eq_some_iff.mp mapped).2
  rw [sourceEq, addressEq] at related
  obtain ⟨actual, actualFound, typed⟩ := related
  have same : actual = table := Option.some.inj (actualFound.symm.trans found)
  simpa only [same] using typed

end Itasca.Runtime.Store

end

/-! ## GlobalLoopCertificates -/

section

/-!
Global allocation-loop content, order, type and source certificates. These retain success and error distinctions used by preparation and instantiation.
-/

/-! ## Global Content Loop -/

section

/-! The actual staged global loop preserves pre-existing store objects and the
linked initializer context through all allocation/refusal branches. -/
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem global_content_staging_loop {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (before store : runtime.store.Store M) (platform : P) (instIndex start : Usize)
    (inst : runtime.store.ModuleInst) (status : core.result.Result Unit runtime.ExecError)
    (staged : StagedPrefix before store) (fresh : before.instances.length ≤ instIndex.val)
    (found : store.instances.val[instIndex.val]? = some inst)
    (compiled : Compiler.InitializerMappings inst.module)
    (valid : ∀ global ∈ inst.module.module.env.globals.val,
      Itasca.ModuleConstants.Valid inst.module.module.env global.init global.gtype.valtype)
    (bindings : InitializerBindings store inst) (imports : InitializerImports store inst)
    (segments : InitializerSegmentBindings store inst)
    (objectBound : objectCount store ≤ Usize.max)
    (startBound : start.val ≤ inst.module.module.env.globals.val.length)
    (mapCapacity : inst.globals.length + (inst.module.module.env.globals.val.length - start.val) ≤ Usize.max) :
    runtime.store.instantiate.Store.prepare_instance_loop7 memory hooks floats allocator store platform status start instIndex
      ⦃ out => ∃ after finalStatus,
        out = storeParts after platform finalStatus ∧ StagedPrefix before after ∧
        objectCount after ≤ Usize.max ∧ GlobalContents after ∧ (SegmentAccounting store → SegmentAccounting after) ∧
        InitializerFunctionMetadataAt store inst after instIndex ∧ ∃ next,
          after.instances.val[instIndex.val]? = some next ∧ next.module = inst.module ∧
          InitializerBindings after next ∧ InitializerImports after next ∧ InitializerSegmentBindings after next ∧
          after.elems = store.elems ∧ after.datas = store.datas ∧ next.elems = inst.elems ∧ next.datas = inst.datas ∧
          (finalStatus = .Ok () → next.globals.length = inst.globals.length + (inst.module.module.env.globals.val.length - start.val)) ⦄ := by
  have contents : GlobalContents store := bindings.globals
  unfold runtime.store.instantiate.Store.prepare_instance_loop7
  apply loop.spec_decr_nat (fun state => inst.module.module.env.globals.val.length - state.2.2.2.val)
    (fun state => state.2.1 = platform ∧ StagedPrefix before state.1 ∧ objectCount state.1 ≤ Usize.max ∧ GlobalContents state.1 ∧ (SegmentAccounting store → SegmentAccounting state.1) ∧
      InitializerFunctionMetadataAt store inst state.1 instIndex ∧
      state.2.2.2.val ≤ inst.module.module.env.globals.val.length ∧
      ∃ currentInst, state.1.instances.val[instIndex.val]? = some currentInst ∧ currentInst.module = inst.module ∧
        InitializerBindings state.1 currentInst ∧ InitializerImports state.1 currentInst ∧
        InitializerSegmentBindings state.1 currentInst ∧
        currentInst.globals.length + (inst.module.module.env.globals.val.length - state.2.2.2.val) ≤ Usize.max ∧
        state.1.elems = store.elems ∧ state.1.datas = store.datas ∧ currentInst.elems = inst.elems ∧ currentInst.datas = inst.datas ∧
        (state.2.2.1 = .Ok () → currentInst.globals.length + start.val = inst.globals.length + state.2.2.2.val))
  · rintro ⟨current, host, result, index⟩ ⟨hhost, hstaged, hobjects, hcontents, haccounted, hmetadata, hindex,
      currentInst, hfound, hsource, hbindings, himports, hsegments, hcapacity, helements, hdatas, hmapElements, hmapData, hcount⟩
    dsimp only at hhost hstaged hobjects hcontents haccounted hmetadata hindex hfound hsource hbindings himports hsegments hcapacity helements hdatas hmapElements hmapData hcount ⊢
    subst host
    unfold runtime.store.instantiate.Store.prepare_instance_loop7.body
    step with Interp.vec_index_given current.instances instIndex currentInst hfound as ⟨actual, hactual⟩
    subst actual
    simp only [runtime.compiler.ExecutableModule.env,
      Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.globals, bind_ok, hsource]
    split
    · rename_i more
      have hmore : index.val < inst.module.module.env.globals.val.length := by
        simpa [alloc.vec.Vec.deref] using more
      cases result with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨current, .Err error, rfl, hstaged, hobjects, hcontents, haccounted, hmetadata,
          currentInst, hfound, hsource, hbindings, himports, hsegments, helements, hdatas, hmapElements, hmapData, by simp⟩
      | Ok unitValue =>
        cases unitValue
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        let global := inst.module.module.env.globals.val[index.val]
        have hglobal : currentInst.module.module.env.globals.val[index.val]? = some global := by
          rw [hsource]
          exact List.getElem?_eq_getElem hmore
        have hvalid : Itasca.ModuleConstants.Valid currentInst.module.module.env global.init global.gtype.valtype := by
          rw [hsource]
          exact valid global (List.mem_of_getElem? (List.getElem?_eq_getElem hmore))
        obtain ⟨function, code, words, hmapping, hc, hcompiled, hresolved⟩ :=
          global_initializer_certificate current currentInst index global (by simpa [hsource] using compiled)
            hglobal hvalid hbindings himports
        have room : currentInst.globals.length < Usize.max := by omega
        step with add_instance_global_result_effect memory hooks floats allocator law current platform instIndex index
          currentInst global function code words hfound hglobal hmapping hc hcompiled hresolved hbindings hobjects room
          as ⟨state, after, host', resultEffect, hhost'⟩
        subst host'
        have effect := resultEffect.effect
        obtain ⟨nextInst, nextFound, nextSource, nextBindings, nextImports, nextSegments, nextSize, nextElements, nextData⟩ :=
          effect.context hfound hbindings himports hsegments
        have nextMetadata : InitializerFunctionMetadataAt store inst after instIndex :=
          ⟨nextInst, nextFound, (hmetadata.resolve hfound).trans (effect.function_metadata hfound nextFound)⟩
        have nextStaged := effect.staged hstaged fresh
        have nextObjects := effect.object_bound hobjects
        have counterCapacity := inst.module.module.env.globals.property
        step as ⟨next, hnext⟩
        refine ⟨nextStaged, nextObjects, effect.contents hcontents, (fun h => effect.segment_accounting hfound (haccounted h)), nextMetadata, ?_, ⟨nextInst, nextFound,
          nextSource.trans hsource, nextBindings, nextImports, nextSegments, ?_,
          effect.segments.1.trans helements, effect.segments.2.trans hdatas,
          nextElements.trans hmapElements, nextData.trans hmapData, ?_⟩, ?_⟩
        · omega
        · omega
        · intro success
          have nextCount := resultEffect.count (List.getElem?_eq_some_iff.mp hfound).1 nextFound success
          have oldCount := hcount rfl
          omega
        · omega
    · rename_i stopped
      have endIndex : index.val = inst.module.module.env.globals.val.length := by
        simp [alloc.vec.Vec.deref] at stopped
        omega
      simp only [WP.spec_ok]
      exact ⟨current, result, rfl, hstaged, hobjects, hcontents, haccounted, hmetadata,
        currentInst, hfound, hsource, hbindings, himports, hsegments, helements, hdatas, hmapElements, hmapData, fun success => by have counted := hcount success; omega⟩
  · exact ⟨rfl, staged, objectBound, contents, (fun h => h), ⟨inst, found, .refl _ _⟩, startBound, inst, found, rfl, bindings, imports, segments, mapCapacity, rfl, rfl, rfl, rfl, fun _ => by simp⟩

end Itasca.Runtime.Store

end

/-! ## Global Order Loop -/

section

/-! The actual staged global loop preserves pre-existing store objects and the
linked initializer context through all allocation/refusal branches. -/

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem global_order_loop {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (before store : runtime.store.Store M) (platform : P) (instIndex start : Usize)
    (inst : runtime.store.ModuleInst) (status : core.result.Result Unit runtime.ExecError)
    (staged : StagedPrefix before store) (fresh : before.instances.length ≤ instIndex.val)
    (found : store.instances.val[instIndex.val]? = some inst)
    (compiled : Compiler.InitializerMappings inst.module)
    (valid : ∀ global ∈ inst.module.module.env.globals.val,
      Itasca.ModuleConstants.Valid inst.module.module.env global.init global.gtype.valtype)
    (bindings : InitializerBindings store inst) (imports : InitializerImports store inst)
    (segments : InitializerSegmentBindings store inst)
    (objectBound : objectCount store ≤ Usize.max)
    (startBound : start.val ≤ inst.module.module.env.globals.val.length)
    (mapCapacity : inst.globals.length + (inst.module.module.env.globals.val.length - start.val) ≤ Usize.max)
    (base : Nat) (initial : List Nat)
    (ordered : AddressOrder base initial store.globals.length (inst.globals.val.map (fun address => address.index.val))) :
    runtime.store.instantiate.Store.prepare_instance_loop7 memory hooks floats allocator store platform status start instIndex
      ⦃ out => ∃ after finalStatus,
        out = storeParts after platform finalStatus ∧ StagedPrefix before after ∧
        objectCount after ≤ Usize.max ∧ (SegmentAccounting store → SegmentAccounting after) ∧
        InitializerFunctionMetadataAt store inst after instIndex ∧ ∃ next,
          after.instances.val[instIndex.val]? = some next ∧ next.module = inst.module ∧
          AddressOrder base initial after.globals.length (next.globals.val.map (fun address => address.index.val)) ∧
          InitializerBindings after next ∧ InitializerImports after next ∧ InitializerSegmentBindings after next ∧
          after.elems = store.elems ∧ after.datas = store.datas ∧ next.elems = inst.elems ∧ next.datas = inst.datas ⦄ := by
  unfold runtime.store.instantiate.Store.prepare_instance_loop7
  apply loop.spec_decr_nat (fun state => inst.module.module.env.globals.val.length - state.2.2.2.val)
    (fun state => state.2.1 = platform ∧ StagedPrefix before state.1 ∧ objectCount state.1 ≤ Usize.max ∧ (SegmentAccounting store → SegmentAccounting state.1) ∧
      InitializerFunctionMetadataAt store inst state.1 instIndex ∧
      state.2.2.2.val ≤ inst.module.module.env.globals.val.length ∧
      ∃ currentInst, state.1.instances.val[instIndex.val]? = some currentInst ∧ currentInst.module = inst.module ∧
        AddressOrder base initial state.1.globals.length (currentInst.globals.val.map (fun address => address.index.val)) ∧
        InitializerBindings state.1 currentInst ∧ InitializerImports state.1 currentInst ∧
        InitializerSegmentBindings state.1 currentInst ∧
        currentInst.globals.length + (inst.module.module.env.globals.val.length - state.2.2.2.val) ≤ Usize.max ∧
        state.1.elems = store.elems ∧ state.1.datas = store.datas ∧ currentInst.elems = inst.elems ∧ currentInst.datas = inst.datas)
  · rintro ⟨current, host, result, index⟩ ⟨hhost, hstaged, hobjects, haccounted, hmetadata, hindex,
      currentInst, hfound, hsource, horder, hbindings, himports, hsegments, hcapacity, helements, hdatas, hmapElements, hmapData⟩
    dsimp only at hhost hstaged hobjects haccounted hmetadata hindex hfound hsource horder hbindings himports hsegments hcapacity helements hdatas hmapElements hmapData ⊢
    subst host
    unfold runtime.store.instantiate.Store.prepare_instance_loop7.body
    step with Interp.vec_index_given current.instances instIndex currentInst hfound as ⟨actual, hactual⟩
    subst actual
    simp only [runtime.compiler.ExecutableModule.env,
      Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.globals, bind_ok, hsource]
    split
    · rename_i more
      have hmore : index.val < inst.module.module.env.globals.val.length := by
        simpa [alloc.vec.Vec.deref] using more
      cases result with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨current, .Err error, rfl, hstaged, hobjects, haccounted, hmetadata,
          currentInst, hfound, hsource, horder, hbindings, himports, hsegments, helements, hdatas, hmapElements, hmapData⟩
      | Ok unitValue =>
        cases unitValue
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        let global := inst.module.module.env.globals.val[index.val]
        have hglobal : currentInst.module.module.env.globals.val[index.val]? = some global := by
          rw [hsource]
          exact List.getElem?_eq_getElem hmore
        have hvalid : Itasca.ModuleConstants.Valid currentInst.module.module.env global.init global.gtype.valtype := by
          rw [hsource]
          exact valid global (List.mem_of_getElem? (List.getElem?_eq_getElem hmore))
        obtain ⟨function, code, words, hmapping, hc, hcompiled, hresolved⟩ :=
          global_initializer_certificate current currentInst index global (by simpa [hsource] using compiled)
            hglobal hvalid hbindings himports
        have room : currentInst.globals.length < Usize.max := by omega
        step with add_instance_global_effect memory hooks floats allocator law current platform instIndex index
          currentInst global function code words hfound hglobal hmapping hc hcompiled hresolved hbindings hobjects room
          as ⟨state, after, host', effect, hhost'⟩
        subst host'
        obtain ⟨nextInst, nextFound, nextSource, nextBindings, nextImports, nextSegments, nextSize, nextElements, nextData⟩ :=
          effect.context hfound hbindings himports hsegments
        have nextMetadata : InitializerFunctionMetadataAt store inst after instIndex :=
          ⟨nextInst, nextFound, (hmetadata.resolve hfound).trans (effect.function_metadata hfound nextFound)⟩
        have nextStaged := effect.staged hstaged fresh
        have nextObjects := effect.object_bound hobjects
        have counterCapacity := inst.module.module.env.globals.property
        step as ⟨next, hnext⟩
        refine ⟨nextStaged, nextObjects, (fun h => effect.segment_accounting hfound (haccounted h)), nextMetadata, ?_, ⟨nextInst, nextFound,
          nextSource.trans hsource, effect.address_order hfound nextFound horder, nextBindings, nextImports, nextSegments, ?_,
          effect.segments.1.trans helements, effect.segments.2.trans hdatas,
          nextElements.trans hmapElements, nextData.trans hmapData⟩, ?_⟩
        · omega
        · omega
        · omega
    · simp only [WP.spec_ok]
      exact ⟨current, result, rfl, hstaged, hobjects, haccounted, hmetadata,
        currentInst, hfound, hsource, horder, hbindings, himports, hsegments, helements, hdatas, hmapElements, hmapData⟩
  · exact ⟨rfl, staged, objectBound, (fun h => h), ⟨inst, found, .refl _ _⟩, startBound, inst, found, rfl, ordered, bindings, imports, segments, mapCapacity, rfl, rfl, rfl, rfl⟩

end Itasca.Runtime.Store

end

/-! ## Global Source Loop -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem global_source_staging_loop {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (before store : runtime.store.Store M) (platform : P) (instIndex start : Usize)
    (inst : runtime.store.ModuleInst) (status : core.result.Result Unit runtime.ExecError)
    (staged : StagedPrefix before store) (fresh : before.instances.length ≤ instIndex.val)
    (found : store.instances.val[instIndex.val]? = some inst)
    (compiled : Compiler.InitializerMappings inst.module)
    (valid : ∀ global ∈ inst.module.module.env.globals.val,
      Itasca.ModuleConstants.Valid inst.module.module.env global.init global.gtype.valtype)
    (bindings : InitializerBindings store inst) (imports : InitializerImports store inst)
    (segments : InitializerSegmentBindings store inst)
    (objectBound : objectCount store ≤ Usize.max)
    (startBound : start.val ≤ inst.module.module.env.globals.val.length)
    (mapCapacity : inst.globals.length + (inst.module.module.env.globals.val.length - start.val) ≤ Usize.max)
    (sourceStore : _root_.store) (sourceInstance : moduleinst)
    (storeWf : wf_store sourceStore) (frameWf : wf_frame ⟨[], sourceInstance⟩)
    (sourceContext : InitializerSourceContext sourceStore sourceInstance store inst)
    (baseGlobals : List runtime.store.GlobalInst)
    (matching : status = .Ok () → ∃ produced,
      store.globals.val = baseGlobals ++ produced ∧
      GlobalSourceValues sourceStore sourceInstance
        (inst.module.module.env.globals.val.take start.val) produced) :
    runtime.store.instantiate.Store.prepare_instance_loop7 memory hooks floats allocator store platform status start instIndex
      ⦃ out => ∃ after finalStatus,
        out = storeParts after platform finalStatus ∧ StagedPrefix before after ∧
        objectCount after ≤ Usize.max ∧ (SegmentAccounting store → SegmentAccounting after) ∧
        InitializerFunctionMetadataAt store inst after instIndex ∧ ∃ next,
          after.instances.val[instIndex.val]? = some next ∧ next.module = inst.module ∧
          InitializerBindings after next ∧ InitializerImports after next ∧ InitializerSegmentBindings after next ∧
          after.elems = store.elems ∧ after.datas = store.datas ∧ next.elems = inst.elems ∧ next.datas = inst.datas ∧
          InitializerSourceContext sourceStore sourceInstance after next ∧
          (finalStatus = .Ok () → ∃ produced, after.globals.val = baseGlobals ++ produced ∧
            GlobalSourceValues sourceStore sourceInstance inst.module.module.env.globals.val produced) ⦄ := by
  unfold runtime.store.instantiate.Store.prepare_instance_loop7
  apply loop.spec_decr_nat (fun state => inst.module.module.env.globals.val.length - state.2.2.2.val)
    (fun state => state.2.1 = platform ∧ StagedPrefix before state.1 ∧ objectCount state.1 ≤ Usize.max ∧ (SegmentAccounting store → SegmentAccounting state.1) ∧
      InitializerFunctionMetadataAt store inst state.1 instIndex ∧
      state.2.2.2.val ≤ inst.module.module.env.globals.val.length ∧
      ∃ currentInst, state.1.instances.val[instIndex.val]? = some currentInst ∧ currentInst.module = inst.module ∧
        InitializerBindings state.1 currentInst ∧ InitializerImports state.1 currentInst ∧
        InitializerSegmentBindings state.1 currentInst ∧
        currentInst.globals.length + (inst.module.module.env.globals.val.length - state.2.2.2.val) ≤ Usize.max ∧
        state.1.elems = store.elems ∧ state.1.datas = store.datas ∧ currentInst.elems = inst.elems ∧ currentInst.datas = inst.datas ∧
        InitializerSourceContext sourceStore sourceInstance state.1 currentInst ∧
        (state.2.2.1 = .Ok () → ∃ produced, state.1.globals.val = baseGlobals ++ produced ∧
          GlobalSourceValues sourceStore sourceInstance
            (inst.module.module.env.globals.val.take state.2.2.2.val) produced))
  · rintro ⟨current, host, result, index⟩ ⟨hhost, hstaged, hobjects, haccounted, hmetadata, hindex,
      currentInst, hfound, hsource, hbindings, himports, hsegments, hcapacity, helements, hdatas, hmapElements, hmapData, hsourceContext, htyped⟩
    dsimp only at hhost hstaged hobjects haccounted hmetadata hindex hfound hsource hbindings himports hsegments hcapacity helements hdatas hmapElements hmapData hsourceContext htyped ⊢
    subst host
    unfold runtime.store.instantiate.Store.prepare_instance_loop7.body
    step with Interp.vec_index_given current.instances instIndex currentInst hfound as ⟨actual, hactual⟩
    subst actual
    simp only [runtime.compiler.ExecutableModule.env,
      Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.globals, bind_ok, hsource]
    split
    · rename_i more
      have hmore : index.val < inst.module.module.env.globals.val.length := by
        simpa [alloc.vec.Vec.deref] using more
      cases result with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨current, .Err error, rfl, hstaged, hobjects, haccounted, hmetadata,
          currentInst, hfound, hsource, hbindings, himports, hsegments, helements, hdatas, hmapElements, hmapData, hsourceContext, by simp⟩
      | Ok unitValue =>
        cases unitValue
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        let global := inst.module.module.env.globals.val[index.val]
        have hglobal : currentInst.module.module.env.globals.val[index.val]? = some global := by
          rw [hsource]
          exact List.getElem?_eq_getElem hmore
        have hvalid : Itasca.ModuleConstants.Valid currentInst.module.module.env global.init global.gtype.valtype := by
          rw [hsource]
          exact valid global (List.mem_of_getElem? (List.getElem?_eq_getElem hmore))
        obtain ⟨function, code, words, hmapping, hc, hcompiled, hresolved⟩ :=
          global_initializer_certificate current currentInst index global (by simpa [hsource] using compiled)
            hglobal hvalid hbindings himports
        have room : currentInst.globals.length < Usize.max := by omega
        step with add_instance_global_value_effect memory hooks floats allocator law current platform instIndex index
          currentInst global function code words hfound hglobal hmapping hc hcompiled hresolved hbindings hobjects room
          as ⟨state, after, host', typedEffect, hhost'⟩
        subst host'
        have evaluated := hsourceContext.expression hvalid hresolved storeWf frameWf
        have effect := typedEffect.effect
        obtain ⟨nextInst, nextFound, nextSource, nextBindings, nextImports, nextSegments, nextSize, nextElements, nextData⟩ :=
          effect.context hfound hbindings himports hsegments
        have nextMetadata : InitializerFunctionMetadataAt store inst after instIndex :=
          ⟨nextInst, nextFound, (hmetadata.resolve hfound).trans (effect.function_metadata hfound nextFound)⟩
        have nextSourceContext := effect.source_context hfound nextFound himports hsourceContext
        have nextStaged := effect.staged hstaged fresh
        have nextObjects := effect.object_bound hobjects
        have counterCapacity := inst.module.module.env.globals.property
        step as ⟨next, hnext⟩
        refine ⟨nextStaged, nextObjects, (fun h => effect.segment_accounting hfound (haccounted h)), nextMetadata, ?_, ⟨nextInst, nextFound,
          nextSource.trans hsource, nextBindings, nextImports, nextSegments, ?_,
          effect.segments.1.trans helements, effect.segments.2.trans hdatas,
          nextElements.trans hmapElements, nextData.trans hmapData, nextSourceContext, ?_⟩, ?_⟩
        · omega
        · omega
        · intro success
          obtain ⟨produced, stored, previous⟩ := htyped rfl
          obtain ⟨values, nextStored, nextValues⟩ := typedEffect.source_values evaluated stored previous success
          refine ⟨values, nextStored, ?_⟩
          simpa only [hnext, List.take_succ_eq_append_getElem hmore] using nextValues
        · omega
    · rename_i stopped
      have atEnd : index.val = inst.module.module.env.globals.val.length := by
        simp [alloc.vec.Vec.deref] at stopped
        omega
      simp only [WP.spec_ok]
      exact ⟨current, result, rfl, hstaged, hobjects, haccounted, hmetadata,
        currentInst, hfound, hsource, hbindings, himports, hsegments, helements, hdatas, hmapElements, hmapData, hsourceContext, fun success => by simpa only [atEnd, List.take_length] using htyped success⟩
  · exact ⟨rfl, staged, objectBound, (fun h => h), ⟨inst, found, .refl _ _⟩, startBound, inst, found, rfl, bindings, imports, segments, mapCapacity, rfl, rfl, rfl, rfl, sourceContext, matching⟩

end Itasca.Runtime.Store

end

/-! ## Global Type Loop -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem global_type_staging_loop {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (before store : runtime.store.Store M) (platform : P) (instIndex start : Usize)
    (inst : runtime.store.ModuleInst) (status : core.result.Result Unit runtime.ExecError)
    (staged : StagedPrefix before store) (fresh : before.instances.length ≤ instIndex.val)
    (found : store.instances.val[instIndex.val]? = some inst)
    (compiled : Compiler.InitializerMappings inst.module)
    (valid : ∀ global ∈ inst.module.module.env.globals.val,
      Itasca.ModuleConstants.Valid inst.module.module.env global.init global.gtype.valtype)
    (bindings : InitializerBindings store inst) (imports : InitializerImports store inst)
    (segments : InitializerSegmentBindings store inst)
    (objectBound : objectCount store ≤ Usize.max)
    (startBound : start.val ≤ inst.module.module.env.globals.val.length)
    (mapCapacity : inst.globals.length + (inst.module.module.env.globals.val.length - start.val) ≤ Usize.max)
    (importTypes : List Itasca.wasm_types.GlobalType)
    (matching : status = .Ok () → GlobalTypeMap store
      (importTypes ++ (inst.module.module.env.globals.val.take start.val).map Itasca.metadata.Global.gtype) inst.globals.val) :
    runtime.store.instantiate.Store.prepare_instance_loop7 memory hooks floats allocator store platform status start instIndex
      ⦃ out => ∃ after finalStatus,
        out = storeParts after platform finalStatus ∧ StagedPrefix before after ∧
        objectCount after ≤ Usize.max ∧ (SegmentAccounting store → SegmentAccounting after) ∧
        InitializerFunctionMetadataAt store inst after instIndex ∧ ∃ next,
          after.instances.val[instIndex.val]? = some next ∧ next.module = inst.module ∧
          InitializerBindings after next ∧ InitializerImports after next ∧ InitializerSegmentBindings after next ∧
          after.elems = store.elems ∧ after.datas = store.datas ∧ next.elems = inst.elems ∧ next.datas = inst.datas ∧
          (finalStatus = .Ok () → GlobalTypeMap after
            (importTypes ++ inst.module.module.env.globals.val.map Itasca.metadata.Global.gtype) next.globals.val) ⦄ := by
  unfold runtime.store.instantiate.Store.prepare_instance_loop7
  apply loop.spec_decr_nat (fun state => inst.module.module.env.globals.val.length - state.2.2.2.val)
    (fun state => state.2.1 = platform ∧ StagedPrefix before state.1 ∧ objectCount state.1 ≤ Usize.max ∧ (SegmentAccounting store → SegmentAccounting state.1) ∧
      InitializerFunctionMetadataAt store inst state.1 instIndex ∧
      state.2.2.2.val ≤ inst.module.module.env.globals.val.length ∧
      ∃ currentInst, state.1.instances.val[instIndex.val]? = some currentInst ∧ currentInst.module = inst.module ∧
        InitializerBindings state.1 currentInst ∧ InitializerImports state.1 currentInst ∧
        InitializerSegmentBindings state.1 currentInst ∧
        currentInst.globals.length + (inst.module.module.env.globals.val.length - state.2.2.2.val) ≤ Usize.max ∧
        state.1.elems = store.elems ∧ state.1.datas = store.datas ∧ currentInst.elems = inst.elems ∧ currentInst.datas = inst.datas ∧
        (state.2.2.1 = .Ok () → GlobalTypeMap state.1
          (importTypes ++ (inst.module.module.env.globals.val.take state.2.2.2.val).map Itasca.metadata.Global.gtype) currentInst.globals.val))
  · rintro ⟨current, host, result, index⟩ ⟨hhost, hstaged, hobjects, haccounted, hmetadata, hindex,
      currentInst, hfound, hsource, hbindings, himports, hsegments, hcapacity, helements, hdatas, hmapElements, hmapData, htyped⟩
    dsimp only at hhost hstaged hobjects haccounted hmetadata hindex hfound hsource hbindings himports hsegments hcapacity helements hdatas hmapElements hmapData htyped ⊢
    subst host
    unfold runtime.store.instantiate.Store.prepare_instance_loop7.body
    step with Interp.vec_index_given current.instances instIndex currentInst hfound as ⟨actual, hactual⟩
    subst actual
    simp only [runtime.compiler.ExecutableModule.env,
      Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.globals, bind_ok, hsource]
    split
    · rename_i more
      have hmore : index.val < inst.module.module.env.globals.val.length := by
        simpa [alloc.vec.Vec.deref] using more
      cases result with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨current, .Err error, rfl, hstaged, hobjects, haccounted, hmetadata,
          currentInst, hfound, hsource, hbindings, himports, hsegments, helements, hdatas, hmapElements, hmapData, by simp⟩
      | Ok unitValue =>
        cases unitValue
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        let global := inst.module.module.env.globals.val[index.val]
        have hglobal : currentInst.module.module.env.globals.val[index.val]? = some global := by
          rw [hsource]
          exact List.getElem?_eq_getElem hmore
        have hvalid : Itasca.ModuleConstants.Valid currentInst.module.module.env global.init global.gtype.valtype := by
          rw [hsource]
          exact valid global (List.mem_of_getElem? (List.getElem?_eq_getElem hmore))
        obtain ⟨function, code, words, hmapping, hc, hcompiled, hresolved⟩ :=
          global_initializer_certificate current currentInst index global (by simpa [hsource] using compiled)
            hglobal hvalid hbindings himports
        have room : currentInst.globals.length < Usize.max := by omega
        step with add_instance_global_typed_effect memory hooks floats allocator law current platform instIndex index
          currentInst global function code words hfound hglobal hmapping hc hcompiled hresolved hbindings hobjects room
          as ⟨state, after, host', typedEffect, hhost'⟩
        subst host'
        have effect := typedEffect.effect
        obtain ⟨nextInst, nextFound, nextSource, nextBindings, nextImports, nextSegments, nextSize, nextElements, nextData⟩ :=
          effect.context hfound hbindings himports hsegments
        have nextMetadata : InitializerFunctionMetadataAt store inst after instIndex :=
          ⟨nextInst, nextFound, (hmetadata.resolve hfound).trans (effect.function_metadata hfound nextFound)⟩
        have nextStaged := effect.staged hstaged fresh
        have nextObjects := effect.object_bound hobjects
        have counterCapacity := inst.module.module.env.globals.property
        step as ⟨next, hnext⟩
        refine ⟨nextStaged, nextObjects, (fun h => effect.segment_accounting hfound (haccounted h)), nextMetadata, ?_, ⟨nextInst, nextFound,
          nextSource.trans hsource, nextBindings, nextImports, nextSegments, ?_,
          effect.segments.1.trans helements, effect.segments.2.trans hdatas,
          nextElements.trans hmapElements, nextData.trans hmapData, ?_⟩, ?_⟩
        · omega
        · omega
        · intro success
          have typed := typedEffect.type_map (List.getElem?_eq_some_iff.mp hfound).1 nextFound (htyped rfl) success
          simpa only [hnext, List.take_succ_eq_append_getElem hmore, List.map_append,
            List.map_cons, List.map_nil, List.append_assoc] using typed
        · omega
    · rename_i stopped
      have atEnd : index.val = inst.module.module.env.globals.val.length := by
        simp [alloc.vec.Vec.deref] at stopped
        omega
      simp only [WP.spec_ok]
      exact ⟨current, result, rfl, hstaged, hobjects, haccounted, hmetadata,
        currentInst, hfound, hsource, hbindings, himports, hsegments, helements, hdatas, hmapElements, hmapData, fun success => by simpa only [atEnd, List.take_length] using htyped success⟩
  · exact ⟨rfl, staged, objectBound, (fun h => h), ⟨inst, found, .refl _ _⟩, startBound, inst, found, rfl, bindings, imports, segments, mapCapacity, rfl, rfl, rfl, rfl, matching⟩

end Itasca.Runtime.Store

end

end

/-! ## GlobalMapPreservation -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem ElementStageEffect.global_types {M : Type} {store after : runtime.store.Store M}
    {inst next : runtime.store.ModuleInst} {index : Usize}
    (effect : ElementStageEffect store index inst after)
    (found : store.instances.val[index.val]? = some inst)
    (nextFound : after.instances.val[index.val]? = some next)
    {types} (mapping : GlobalTypeMap store types inst.globals.val) :
    GlobalTypeMap after types next.globals.val := by
  cases effect with
  | unchanged =>
    have same := Option.some.inj (found.symm.trans nextFound)
    simpa only [same] using mapping
  | appended elements addresses segment stored mapped =>
    have bound := (List.getElem?_eq_some_iff.mp found).1
    simp only [alloc.vec.Vec.set_val_eq, List.getElem?_set, if_pos bound, ↓reduceIte, Option.some.injEq] at nextFound
    subst next
    exact mapping

theorem DataStageEffect.global_types {M : Type} {store after : runtime.store.Store M}
    {inst next : runtime.store.ModuleInst} {index : Usize}
    (effect : DataStageEffect store index inst after)
    (found : store.instances.val[index.val]? = some inst)
    (nextFound : after.instances.val[index.val]? = some next)
    {types} (mapping : GlobalTypeMap store types inst.globals.val) :
    GlobalTypeMap after types next.globals.val := by
  cases effect with
  | unchanged =>
    have same := Option.some.inj (found.symm.trans nextFound)
    simpa only [same] using mapping
  | appended datas addresses segment stored mapped =>
    have bound := (List.getElem?_eq_some_iff.mp found).1
    simp only [alloc.vec.Vec.set_val_eq, List.getElem?_set, if_pos bound, ↓reduceIte, Option.some.injEq] at nextFound
    subst next
    exact mapping

end Itasca.Runtime.Store

end

/-! ## TableMemoryOrder -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem TableStageEffect.address_order {M : Type} {store : runtime.store.Store M}
    {inst : runtime.store.ModuleInst} {ty out} {start initial}
    (effect : TableStageEffect store inst ty out)
    (ordered : AddressOrder start initial store.tables.length (inst.tables.val.map fun address => address.index.val)) :
    AddressOrder start initial out.2.1.tables.length (out.2.2.tables.val.map fun address => address.index.val) := by
  rcases effect with ⟨error, rfl⟩ | ⟨tables, elements, addresses, count, zeros, stored, mapped, limits, capacity, counter, budget, rfl⟩
  · exact ordered
  · simpa [stored, mapped] using ordered.append

theorem MemoryStageEffect.address_order {M : Type} {view : M → Slice U8} {store : runtime.store.Store M}
    {inst : runtime.store.ModuleInst} {ty out} {start initial}
    (effect : MemoryStageEffect view store inst ty out)
    (ordered : AddressOrder start initial store.memories.length (inst.memories.val.map fun address => address.index.val)) :
    AddressOrder start initial out.2.1.memories.length (out.2.2.memories.val.map fun address => address.index.val) := by
  rcases effect with ⟨error, rfl⟩ | ⟨memories, buffer, addresses, count, zeros, stored, mapped, limits, capacity, counter, budget, rfl⟩
  · exact ordered
  · simpa [stored, mapped] using ordered.append
end Itasca.Runtime.Store

end

/-! ## MemoryAllocationLoop -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- The actual memory loop allocates a decoded source suffix in order and issues
consecutive fresh addresses, preserving all previous objects. -/
theorem memory_allocation_staging_loop {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (before store : runtime.store.Store M) (seed inst : runtime.store.ModuleInst)
    (start : Usize)
    (startBound : start.val ≤ seed.module.module.env.mem_types.val.length)
    (changed : store = {before with memories := store.memories, memory_bytes := store.memory_bytes})
    (instChanged : inst = {seed with memories := inst.memories})
    (retained : StagedPrefix before store) (objectBound : objectCount store ≤ Usize.max)
    (issued : ∀ address ∈ inst.memories.val, address.index.val < store.memories.length)
    (count : inst.memories.length = start.val)
    (base : Nat) (initial : List Nat) (allocationStart : Nat) (original : List meminst)
    (startOrder : allocationStart ≤ start.val)
    (ordered : AddressOrder base initial store.memories.length (inst.memories.val.map fun address => address.index.val))
    (matching : AllocationPrefix (fun ty => Spec.allocationMemory (Itasca.EnvTranslation.memType ty))
      seed.module.module.env.mem_types.val allocationStart original (store.memories.val.map (decodeMemory view)) start.val) :
    runtime.store.instantiate.Store.prepare_instance_loop6 memory allocator store (.Ok ()) start inst
      ⦃ out => ∃ after next status, out = typeParts after status next ∧
        after = {before with memories := after.memories, memory_bytes := after.memory_bytes} ∧ next = {seed with memories := next.memories} ∧
        StagedPrefix before after ∧ objectCount after ≤ Usize.max ∧
        (∀ address ∈ next.memories.val, address.index.val < after.memories.length) ∧
        (status = .Ok () → next.memories.length = seed.module.module.env.mem_types.val.length) ∧
        AddressOrder base initial after.memories.length (next.memories.val.map fun address => address.index.val) ∧
        (status = .Ok () → AllocationPrefix (fun ty => Spec.allocationMemory (Itasca.EnvTranslation.memType ty))
          seed.module.module.env.mem_types.val allocationStart original (after.memories.val.map (decodeMemory view))
          seed.module.module.env.mem_types.val.length) ⦄ := by
  have capacity := seed.module.module.env.mem_types.property
  unfold runtime.store.instantiate.Store.prepare_instance_loop6
  apply loop.spec_decr_nat (fun state => seed.module.module.env.mem_types.val.length - state.2.2.1.val)
    (fun state => state.1 = {before with memories := state.1.memories, memory_bytes := state.1.memory_bytes} ∧
      state.2.2.2 = {seed with memories := state.2.2.2.memories} ∧ StagedPrefix before state.1 ∧
      objectCount state.1 ≤ Usize.max ∧
      (∀ address ∈ state.2.2.2.memories.val, address.index.val < state.1.memories.length) ∧
      allocationStart ≤ state.2.2.1.val ∧
      AddressOrder base initial state.1.memories.length (state.2.2.2.memories.val.map fun address => address.index.val) ∧
      state.2.2.1.val ≤ seed.module.module.env.mem_types.val.length ∧
      (state.2.1 = .Ok () → state.2.2.2.memories.length = state.2.2.1.val) ∧
      (state.2.1 = .Ok () → AllocationPrefix (fun ty => Spec.allocationMemory (Itasca.EnvTranslation.memType ty))
        seed.module.module.env.mem_types.val allocationStart original (state.1.memories.val.map (decodeMemory view)) state.2.2.1.val))
  · rintro ⟨current, status, index, currentInst⟩ ⟨currentChanged, mapChanged, prefixStore, bound, currentIssued, indexLower, currentOrder, indexBound, counting, typed⟩
    dsimp only at currentChanged mapChanged prefixStore bound currentIssued indexLower currentOrder indexBound counting typed ⊢
    have source : currentInst.module = seed.module := by
      have eq := congrArg runtime.store.ModuleInst.module mapChanged
      exact eq
    unfold runtime.store.instantiate.Store.prepare_instance_loop6.body
    simp only [runtime.compiler.ExecutableModule.env, Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.mem_types, source, bind_ok]
    split
    · rename_i more
      have within : index.val < seed.module.module.env.mem_types.val.length := by
        simpa [alloc.vec.Vec.deref] using more
      cases status with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨current, currentInst, .Err error, by simp [typeParts, source], currentChanged,
          mapChanged, prefixStore, bound, currentIssued, by simp, currentOrder, by simp⟩
      | Ok value =>
        cases value
        have size := counting rfl
        have actualBound : index.val < currentInst.module.module.env.mem_types.val.length := by simpa only [source] using within
        have room : currentInst.memories.length < Usize.max := by omega
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        step with add_instance_memory_effect memory allocator law view laws current currentInst index
          actualBound bound room as ⟨status, after, nextInst, effect⟩
        obtain ⟨afterChanged, nextChanged, prefixNext, nextBound⟩ := effect.context bound
        have afterExact : after = {before with memories := after.memories, memory_bytes := after.memory_bytes} := by
          calc
            after = {current with memories := after.memories, memory_bytes := after.memory_bytes} := afterChanged
            _ = _ := by rw [currentChanged]
        have nextExact : nextInst = {seed with memories := nextInst.memories} := by
          calc
            nextInst = {currentInst with memories := nextInst.memories} := nextChanged
            _ = _ := by rw [mapChanged]
        step as ⟨next, increment⟩
        refine ⟨afterExact, nextExact, prefixStore.trans prefixNext, nextBound,
          effect.issued currentIssued, ?_, effect.address_order currentOrder, ?_, ?_, ?_, ?_⟩
        · omega
        · omega
        · intro success
          have appended := effect.count success
          dsimp only at appended
          omega
        · intro success
          have grown := (typed rfl).append indexLower within
          have actual := effect.decoded success
          dsimp only at actual
          unfold AllocationPrefix
          rw [actual]
          simpa only [AllocationPrefix, source, increment] using grown
        · omega
    · rename_i stopped
      have atEnd : index.val = seed.module.module.env.mem_types.val.length := by
        simp [alloc.vec.Vec.deref] at stopped
        omega
      simp only [WP.spec_ok]
      refine ⟨current, currentInst, status, by simp [typeParts, source], currentChanged,
        mapChanged, prefixStore, bound, currentIssued, ?_, currentOrder, ?_⟩
      · intro success
        simpa only [atEnd] using counting success
      · intro success
        simpa only [atEnd] using typed success
  · exact ⟨changed, instChanged, retained, objectBound, issued, startOrder, ordered, startBound, (fun _ => count), (fun _ => matching)⟩


/-- An accepted full memory allocation run has the exact source-defined append
and the consecutive address map required by module allocation. -/
theorem memory_allocation_success {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (before after : runtime.store.Store M) (inst next : runtime.store.ModuleInst) (start : Usize)
    (bound : start.val ≤ inst.module.module.env.mem_types.val.length)
    (objectBound : objectCount before ≤ Usize.max)
    (issued : ∀ address ∈ inst.memories.val, address.index.val < before.memories.length)
    (count : inst.memories.length = start.val)
    (run : runtime.store.instantiate.Store.prepare_instance_loop6 memory allocator before (.Ok ()) start inst =
      .ok (typeParts after (.Ok ()) next)) :
    after.memories.val.map (decodeMemory view) = before.memories.val.map (decodeMemory view) ++
      (inst.module.module.env.mem_types.val.drop start.val).map
        (fun ty => Spec.allocationMemory (Itasca.EnvTranslation.memType ty)) ∧
    after.memories.length = before.memories.length + (inst.module.module.env.mem_types.val.length - start.val) ∧
    next.memories.val.map (fun address => address.index.val) =
      inst.memories.val.map (fun address => address.index.val) ++
        List.range' before.memories.length (inst.module.module.env.mem_types.val.length - start.val) := by
  have checked := memory_allocation_staging_loop memory allocator law view laws before before inst inst start bound rfl rfl
    (.refl _) objectBound issued count before.memories.length (inst.memories.val.map fun address => address.index.val)
    start.val (before.memories.val.map (decodeMemory view)) (by omega) (.refl _ _) (.initial _ _ _ _)
  rw [run, WP.spec_ok] at checked
  obtain ⟨actual, actualInst, status, same, changed, instChanged, retained, objects, addresses, finalCount, ordered, contents⟩ := checked
  obtain ⟨rfl, rfl, rfl⟩ := (type_parts_inj _ _ _ _ _ _).mp same
  have fullCount := finalCount rfl
  have complete := ordered.complete (count := inst.module.module.env.mem_types.val.length - start.val)
    (by simp only [List.length_map]; change next.memories.length = inst.memories.length + _; omega)
  exact ⟨(contents rfl).complete, complete.1, complete.2⟩

end Itasca.Runtime.Store

end
