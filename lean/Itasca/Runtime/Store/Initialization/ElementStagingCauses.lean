import Itasca.Runtime.Representation.Collection
import Itasca.Runtime.Store.Invariant.OwnedInitializerCauses
import Itasca.Runtime.Store.Invariant.PrecommitError
import Itasca.Runtime.Store.Initialization.ElementLoop
import Itasca.Runtime.Store.Preparation.AllocationCauses
import Itasca.Runtime.Store.Preparation.AllocationErrors
import Itasca.Runtime.Compiler.Local.Initializer.InitializerMappings
import Itasca.Runtime.Store.Initialization.InitializerMetadata
import Itasca.Runtime.Store.Initialization.ElementEffects
import Itasca.Runtime.Store.Initialization.ElementErrors
import Itasca.Runtime.Store.Preparation.PreparationCalls
import Itasca.Runtime.Store.Invariant.ErrorPost

/-!
Element-segment staging resource causes. Initializer-loop failures and element allocation requests assemble the resource classification for the complete staging loop.
-/

/-! ## Element Value Causes -/

section

/-! Finite preparation of element initializer values. Each input certificate
connects an actual source expression and retained synthetic function; no
execution premise is accepted. The loop leaves the store and platform intact. -/
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- The refused synthetic function belongs to an actual source initializer
of this element segment; the store argument is the unchanged evaluation state. -/
def ElementInitializerCause {M A : Type} (allocator : runtime.platform.Alloc A)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (index : Usize)
    (segment : Itasca.metadata.Element) (error : runtime.ExecError) : Prop :=
  ∃ (k : Usize), ∃ functions function code expr,
    k.val < segment.init.length ∧
    inst.module.element_initializers.val[index.val]? = some functions ∧
    functions.val[k.val]? = some function ∧ segment.init.val[k.val]? = some expr ∧
    inst.module.functions.val[function.val]? = some code ∧
    Compiler.InitializerCode code expr (elementValueType segment.elem) ∧
    Interp.SyntheticPreparationCause allocator store code error

private theorem elem_value_type_eq (ty : Itasca.wasm_types.ElemType) :
    wasm_types.ElemType.value_type ty = .ok (elementValueType ty) := by cases ty <;> rfl

private theorem encode_push {M : Type} (store : runtime.store.Store M)
    (values : alloc.vec.Vec U64) (value : runtime.Value) (owned : ValueInStore store value)
    (room : values.length < Usize.max) :
    (do let (lo, _) ← runtime.value.encode value
        let next ← alloc.vec.Vec.push values lo
        .ok (next, (core.result.Result.Ok () : core.result.Result Unit runtime.ExecError)))
      ⦃ out => out.1.length = values.length + 1 ∧ out.2 = .Ok () ⦄ := by
  step with Interp.encode_value_spec value store.id owned.1 as ⟨pair, hencoded⟩
  rcases pair with ⟨lo, high⟩
  step as ⟨next, hnext⟩
  simp [alloc.vec.Vec.length, hnext]

theorem element_initializers_loop_causes {M P F A : Type}
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
    (allowed : ErrorAllowed (ElementInitializerCause allocator store inst index segment) status)
    (hvalues : values.length ≤ j.val) (hj : j.val ≤ length.val) :
    runtime.store.instantiate.Store.add_instance_element_loop memory hooks floats allocator store platform
      instIndex index length values j status ⦃ out =>
        out.1 = store ∧ out.2.1 = platform ∧ out.2.2.1.length ≤ length.val ∧ ErrorAllowed (ElementInitializerCause allocator store inst index segment) out.2.2.2 ⦄ := by
  unfold runtime.store.instantiate.Store.add_instance_element_loop
  apply loop.spec_decr_nat (fun p => length.val - p.2.2.2.1.val)
    (fun p => p.1 = store ∧ p.2.1 = platform ∧
      p.2.2.1.length ≤ p.2.2.2.1.val ∧ p.2.2.2.1.val ≤ length.val ∧
      ErrorAllowed (ElementInitializerCause allocator store inst index segment) p.2.2.2.2)
  · rintro ⟨current, host, vals, k, state⟩ ⟨hcurrent, hhost, hvals, hk, hallowed⟩
    dsimp only at hcurrent hhost hvals hk hallowed ⊢
    subst current host
    change vals.val.length ≤ k.val at hvals
    unfold runtime.store.instantiate.Store.add_instance_element_loop.body
    split
    · rename_i more
      have hmore : k.val < length.val := by scalar_tac
      cases state with
      | Err error =>
        simp [core.result.Result.is_ok, hallowed]
        omega
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
        step with eval_const_owned_resource_causes memory hooks floats allocator law store platform instIndex function
          inst code expr (elementValueType segment.elem) words hi hcode compiled resolved bindings
          as ⟨result, after, host', hs, hp, hvalue, errors⟩
        subst after host'
        cases result with
        | Err error =>
          step as ⟨next, hnext⟩
          change vals.val.length ≤ next.val ∧ next.val ≤ length.val ∧ ErrorAllowed (ElementInitializerCause allocator store inst index segment) (.Err error) ∧ length.val - next.val < length.val - k.val
          exact ⟨by omega, by omega, ⟨k,functions,function,code,expr,by omega,mapping,hfunction,hexpr,hcode,compiled,errors error rfl⟩, by omega⟩
        | Ok value =>
          obtain ⟨owned, typed⟩ := hvalue value rfl
          have room : vals.length < Usize.max := by scalar_tac
          apply WP.spec_bind (encode_push store vals value owned room)
          rintro ⟨pushed, nextStatus⟩ ⟨hpush, hstatus⟩
          dsimp only at hstatus
          subst nextStatus
          step as ⟨next, hnext⟩
          refine ⟨?_, by omega, True.intro, by omega⟩
          rw [hpush]
          change vals.val.length + 1 ≤ next.val
          omega
    · have hstop : length.val ≤ k.val := by scalar_tac
      simp only [WP.spec_ok]
      simp only [true_and]
      change vals.val.length ≤ length.val ∧ ErrorAllowed (ElementInitializerCause allocator store inst index segment) state
      exact ⟨by omega, hallowed⟩
  · exact ⟨rfl, rfl, hvalues, hj, allowed⟩

end Itasca.Runtime.Store

end

/-! ## Element Allocation Causes -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
set_option maxRecDepth 8192

/-- Segment storage refusals retain their exact source-sized initial request,
final store-vector request, or source initializer witness. -/
def ElementAllocationCause {M A : Type} (allocator : runtime.platform.Alloc A)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (index : Usize)
    (segment : Itasca.metadata.Element) (error : runtime.ExecError) : Prop :=
  (error = .Exhausted .Allocation ∧
    (allocator.reserve (alloc.vec.Vec.new U64) segment.init.len = .ok (false,alloc.vec.Vec.new U64) ∨
      allocator.reserve store.elems 1#usize = .ok (false,store.elems))) ∨
  ElementInitializerCause allocator store inst index segment error

theorem add_element_resource_cause {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (platform : P) (instIndex index : Usize)
    (inst : runtime.store.ModuleInst) (segment : Itasca.metadata.Element)
    (found : store.instances.val[instIndex.val]? = some inst)
    (element : inst.module.module.env.elements.val[index.val]? = some segment)
    (certificates : ElementInitializers store inst index segment)
    (bindings : InitializerBindings store inst)
    (error : runtime.ExecError) (after : runtime.store.Store M) (host : P)
    (run : runtime.store.instantiate.Store.add_instance_element memory hooks floats allocator store platform instIndex index = .ok (.Err error,after,host)) :
    after = store ∧ host = platform ∧ ElementAllocationCause allocator store inst index segment error := by
  unfold runtime.store.instantiate.Store.add_instance_element at run
  simp only [Compiler.initializer_vec_index store.instances instIndex inst found,
    runtime.compiler.ExecutableModule.env, Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.elements, bind_ok] at run
  rw [Compiler.initializer_slice_index inst.module.module.env.elements.deref index segment
    (by simpa [alloc.vec.Vec.deref] using element)] at run
  obtain ⟨reserved, reserveRun,refusal⟩ := reserve_with_cause allocator law (alloc.vec.Vec.new U64) segment.init.len
  simp only [bind_ok, reserveRun] at run
  cases reserved with
  | false =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at run
    obtain ⟨rfl,rfl,rfl⟩ := run
    exact ⟨rfl,rfl,Or.inl ⟨rfl,Or.inl refusal⟩⟩
  | true =>
    simp only [↓reduceIte,uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at run
    obtain ⟨⟨evaluated,finalHost,values,status⟩,loopRun,sameStore,sameHost,bound,errors⟩ := WP.spec_imp_exists
      (element_initializers_loop_causes memory hooks floats allocator law store platform instIndex index
        segment.init.len inst segment found element (by simp) certificates bindings
        (alloc.vec.Vec.new U64) 0#usize (.Ok ()) True.intro (by simp) (by scalar_tac))
    dsimp only at sameStore sameHost bound errors
    subst evaluated finalHost
    rw [loopRun] at run
    simp only [bind_ok,uncurry_apply_pair] at run
    cases status with
    | Err rejected =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at run
      obtain ⟨rfl,rfl,rfl⟩ := run
      exact ⟨rfl,rfl,Or.inr errors⟩
    | Ok done =>
      cases done
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at run
      obtain ⟨answer,reserved,refused⟩ := reserve_with_cause allocator law store.elems 1#usize
      rw [reserved] at run
      cases answer
      · simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at run
        obtain ⟨rfl,rfl,rfl⟩ := run
        exact ⟨rfl,rfl,Or.inl ⟨rfl,Or.inr refused⟩⟩
      · simp [core.result.Result.Insts.CoreOpsTry.branch,
          runtime.compiler.ExecutableModule.env,Itasca.metadata.Module.impl.env,Itasca.metadata.Env.impl.elements] at run
        obtain ⟨current,read,run⟩ := normal_bind_exists _ _ _ run
        obtain ⟨declared,read,run⟩ := normal_bind_exists _ _ _ run
        obtain ⟨elements,pushed,run⟩ := normal_bind_exists _ _ _ run
        obtain ⟨⟨current,back⟩,read,run⟩ := normal_bind_exists _ _ _ run
        simp only [uncurry_apply_pair] at run
        obtain ⟨addresses,mapped,run⟩ := normal_bind_exists _ _ _ run
        simp at run
end Itasca.Runtime.Store

end

/-! ## Element Staging Causes -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

abbrev elementStageCall {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (instIndex : Usize)
    (state : runtime.store.Store M × P) (index : Usize) :=
  runtime.store.instantiate.Store.add_instance_element memory hooks floats allocator state.1 state.2 instIndex index

/-- A refused source element follows an actual successful prefix of the staging loop. -/
def ElementStagingCause {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (store : runtime.store.Store M) (platform : P)
    (instIndex start : Usize) (error : runtime.ExecError) : Prop :=
  ∃ current host index inst segment,
    PreparationCalls (elementStageCall memory hooks floats allocator instIndex) (store,platform) start (current,host) index ∧
    current.instances.val[instIndex.val]? = some inst ∧
    inst.module.module.env.elements.val[index.val]? = some segment ∧
    runtime.store.instantiate.Store.add_instance_element memory hooks floats allocator current host instIndex index = .ok (.Err error,current,host) ∧
    ElementAllocationCause allocator current inst index segment error

theorem element_staging_resource_loop {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator)
    (before store : runtime.store.Store M) (platform : P) (instIndex start : Usize)
    (inst : runtime.store.ModuleInst)
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
    (mapCapacity : inst.elems.length + (inst.module.module.env.elements.val.length - start.val) ≤ Usize.max) :
    runtime.store.instantiate.Store.prepare_instance_loop8 memory hooks floats allocator store platform (.Ok ()) start instIndex
      ⦃ out => ∃ after finalStatus,
        out = storeParts after platform finalStatus ∧
        (∀ error, finalStatus = .Err error → ElementStagingCause memory hooks floats allocator store platform instIndex start error) ∧ ErrorAllowed ResourceError finalStatus ∧ StagedPrefix before after ∧
        objectCount after ≤ Usize.max ∧ (SegmentAccounting store → SegmentAccounting after) ∧
        InitializerFunctionMetadataAt store inst after instIndex ∧ ∃ next,
          after.instances.val[instIndex.val]? = some next ∧ next.module = inst.module ∧
          InitializerBindings after next ∧ InitializerImports after next ∧ InitializerSegmentBindings after next ∧
          after.datas = store.datas ∧ next.datas = inst.datas ⦄ := by
  unfold runtime.store.instantiate.Store.prepare_instance_loop8
  apply loop.spec_decr_nat (fun state => inst.module.module.env.elements.val.length - state.2.2.2.val)
    (fun state => state.2.1 = platform ∧
      (state.2.2.1 = .Ok () → PreparationCalls (elementStageCall memory hooks floats allocator instIndex) (store,platform) start (state.1,state.2.1) state.2.2.2) ∧
      (∀ error, state.2.2.1 = .Err error → ElementStagingCause memory hooks floats allocator store platform instIndex start error) ∧ ErrorAllowed ResourceError state.2.2.1 ∧ StagedPrefix before state.1 ∧ objectCount state.1 ≤ Usize.max ∧ (SegmentAccounting store → SegmentAccounting state.1) ∧
      InitializerFunctionMetadataAt store inst state.1 instIndex ∧
      state.2.2.2.val ≤ inst.module.module.env.elements.val.length ∧
      ∃ currentInst, state.1.instances.val[instIndex.val]? = some currentInst ∧ currentInst.module = inst.module ∧
        InitializerBindings state.1 currentInst ∧ InitializerImports state.1 currentInst ∧
        InitializerSegmentBindings state.1 currentInst ∧
        currentInst.elems.length + (inst.module.module.env.elements.val.length - state.2.2.2.val) ≤ Usize.max ∧
        state.1.elems.length + (inst.module.module.env.elements.val.length - state.2.2.2.val) ≤ Usize.max ∧
        state.1.datas = store.datas ∧ currentInst.datas = inst.datas)
  · rintro ⟨current, host, result, index⟩ ⟨hhost, trace, causes, errors, hstaged, hobjects, haccounted, hmetadata, hindex,
      currentInst, hfound, hsource, hbindings, himports, hsegments, hcapacity, hstoreCapacity, hdatas, hmapData⟩
    dsimp only at hhost errors hstaged hobjects haccounted hmetadata hindex hfound hsource hbindings himports hsegments hcapacity hstoreCapacity hdatas hmapData ⊢
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
        exact ⟨current, .Err error, rfl, causes, errors, hstaged, hobjects, haccounted, hmetadata,
          currentInst, hfound, hsource, hbindings, himports, hsegments, hdatas, hmapData⟩
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
        have reached := trace rfl
        obtain ⟨⟨state,after,host'⟩,called,⟨effect,hhost'⟩,nextErrors⟩ := WP.spec_imp_exists (normal_return_post
          (add_instance_element_effect memory hooks floats allocator law current platform instIndex index
            currentInst segment hfound hsegment certificates hbindings room mapRoom)
          (fun out called => add_element_errors memory hooks floats allocator law current platform instIndex index
            currentInst segment hfound hsegment certificates hbindings out called))
        rw [called]
        simp only [bind_ok,uncurry_apply_pair]
        dsimp only at effect hhost' nextErrors
        subst host'
        obtain ⟨nextInst, nextFound, nextSource, nextBindings, nextImports, nextSegments, nextSize, nextStoreSize, nextData⟩ :=
          effect.context hfound hbindings himports hsegments
        have nextMetadata : InitializerFunctionMetadataAt store inst after instIndex :=
          ⟨nextInst, nextFound, (hmetadata.resolve hfound).trans (effect.function_metadata hfound nextFound)⟩
        have nextStaged := effect.staged hstaged fresh
        have nextObjects : objectCount after ≤ Usize.max := by simpa only [effect.object_count] using hobjects
        have counterCapacity := inst.module.module.env.elements.property
        step as ⟨next, hnext⟩
        refine ⟨?_,?_,nextErrors, nextStaged, nextObjects, (fun h => effect.segment_accounting hfound (haccounted h)), nextMetadata, ?_, ⟨nextInst, nextFound,
          nextSource.trans hsource, nextBindings, nextImports, nextSegments, ?_,
          ?_, effect.data.trans hdatas, nextData.trans hmapData⟩, ?_⟩
        · intro success
          subst state
          exact .next reached called hnext
        · intro error rejected
          subst state
          obtain ⟨sameStore,sameHost,cause⟩ := add_element_resource_cause memory hooks floats allocator law
            current platform instIndex index currentInst segment hfound hsegment certificates hbindings error after platform called
          subst after
          exact ⟨current,platform,index,currentInst,segment,reached,hfound,hsegment,called,cause⟩
        · omega
        · omega
        · omega
        · omega
    · simp only [WP.spec_ok]
      exact ⟨current, result, rfl, causes, errors, hstaged, hobjects, haccounted, hmetadata,
        currentInst, hfound, hsource, hbindings, himports, hsegments, hdatas, hmapData⟩
  · exact ⟨rfl, (fun _ => .refl _ _), (by simp), True.intro, staged, objectBound, (fun h => h), ⟨inst, found, .refl _ _⟩, startBound, inst, found, rfl, bindings, imports, segments, mapCapacity, storeCapacity, rfl, rfl⟩

end Itasca.Runtime.Store

end
