import Itasca.Generated.FunsInstantiate
import Itasca.Runtime.Store.Initialization.ElementLoop
import Itasca.Runtime.Store.Initialization.ElementTypedEffect
import Itasca.Runtime.Store.Initialization.DataEffects
import Itasca.Generated.Types
import Itasca.Runtime.Representation.Values

/-!
Sections, each formerly its own module: SegmentEffects, InitializerMetadata, StoreParts, ElementShapeLoop.
-/

/-! ## SegmentEffects -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem GlobalStageEffect.segment_accounting {M : Type} {store after : runtime.store.Store M}
    {index : Usize} {inst : runtime.store.ModuleInst}
    (effect : GlobalStageEffect store index inst after)
    (found : store.instances.val[index.val]? = some inst)
    (accounted : SegmentAccounting store) : SegmentAccounting after := by
  cases effect with
  | unchanged => exact accounted
  | appended globals addresses global globalValues addressValues shape room =>
    apply accounted.update_instance index inst {inst with globals := addresses} found rfl 0 0 <;> simp

theorem ElementStageEffect.segment_accounting {M : Type} {store after : runtime.store.Store M}
    {index : Usize} {inst : runtime.store.ModuleInst}
    (effect : ElementStageEffect store index inst after)
    (found : store.instances.val[index.val]? = some inst)
    (accounted : SegmentAccounting store) : SegmentAccounting after := by
  cases effect with
  | unchanged => exact accounted
  | appended elements addresses element elementValues addressValues =>
    apply accounted.update_instance index inst {inst with elems := addresses} found rfl 1 0
    · simpa using congrArg List.length elementValues
    · simp
    · simpa using congrArg List.length addressValues
    · simp

theorem DataStageEffect.segment_accounting {M : Type} {store after : runtime.store.Store M}
    {index : Usize} {inst : runtime.store.ModuleInst}
    (effect : DataStageEffect store index inst after)
    (found : store.instances.val[index.val]? = some inst)
    (accounted : SegmentAccounting store) : SegmentAccounting after := by
  cases effect with
  | unchanged => exact accounted
  | appended datas addresses data dataValues addressValues =>
    apply accounted.update_instance index inst {inst with datas := addresses} found rfl 0 1
    · simp
    · simpa using congrArg List.length dataValues
    · simp
    · simpa using congrArg List.length addressValues

end Itasca.Runtime.Store

end

/-! ## InitializerMetadata -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- Constant/segment staging changes only value and segment maps. The exact
metadata used by retained function certificates remains unchanged. -/
structure InitializerFunctionMetadata {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) (after : runtime.store.Store M) (next : runtime.store.ModuleInst) : Prop where
  identity : after.id = store.id
  functions : after.funcs = store.funcs
  signatures : after.types = store.types
  source : next.module = inst.module
  typeMap : next.types = inst.types
  functionMap : next.funcs = inst.funcs
  tables : after.tables = store.tables
  tableMap : next.tables = inst.tables
  memories : after.memories = store.memories
  memoryMap : next.memories = inst.memories
  instanceCount : after.instances.length = store.instances.length

theorem InitializerFunctionMetadata.refl {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) : InitializerFunctionMetadata store inst store inst := by
  constructor <;> rfl

theorem InitializerFunctionMetadata.trans {M : Type} {a b c : runtime.store.Store M}
    {i j k : runtime.store.ModuleInst} (first : InitializerFunctionMetadata a i b j)
    (second : InitializerFunctionMetadata b j c k) : InitializerFunctionMetadata a i c k := by
  exact ⟨second.identity.trans first.identity, second.functions.trans first.functions,
    second.signatures.trans first.signatures, second.source.trans first.source,
    second.typeMap.trans first.typeMap, second.functionMap.trans first.functionMap,
    second.tables.trans first.tables, second.tableMap.trans first.tableMap,
    second.memories.trans first.memories, second.memoryMap.trans first.memoryMap,
    second.instanceCount.trans first.instanceCount⟩

def InitializerFunctionMetadataAt {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.ModuleInst) (after : runtime.store.Store M) (index : Usize) : Prop :=
  ∃ next, after.instances.val[index.val]? = some next ∧ InitializerFunctionMetadata store inst after next

theorem InitializerFunctionMetadataAt.resolve {M : Type} {store after : runtime.store.Store M}
    {inst next : runtime.store.ModuleInst} {index : Usize}
    (metadata : InitializerFunctionMetadataAt store inst after index)
    (found : after.instances.val[index.val]? = some next) : InitializerFunctionMetadata store inst after next := by
  obtain ⟨actual, lookup, matching⟩ := metadata
  have same : actual = next := Option.some.inj (lookup.symm.trans found)
  exact same ▸ matching

theorem GlobalStageEffect.function_metadata {M : Type} {store after : runtime.store.Store M}
    {index : Usize} {inst next : runtime.store.ModuleInst}
    (effect : GlobalStageEffect store index inst after)
    (found : store.instances.val[index.val]? = some inst)
    (nextFound : after.instances.val[index.val]? = some next) :
    InitializerFunctionMetadata store inst after next := by
  cases effect with
  | unchanged =>
    have same : inst = next := Option.some.inj (found.symm.trans nextFound)
    subst next
    exact .refl _ _
  | appended globals addresses global globalValues addressValues canonical room =>
    have bound : index.val < store.instances.val.length := (List.getElem?_eq_some_iff.mp found).1
    simp only [alloc.vec.Vec.set_val_eq, List.getElem?_set, if_pos bound, ↓reduceIte,
      Option.some.injEq] at nextFound
    subst next
    constructor <;> try rfl
    simp [alloc.vec.Vec.length, alloc.vec.Vec.set_val_eq]

theorem ElementStageEffect.function_metadata {M : Type} {store after : runtime.store.Store M}
    {index : Usize} {inst next : runtime.store.ModuleInst}
    (effect : ElementStageEffect store index inst after)
    (found : store.instances.val[index.val]? = some inst)
    (nextFound : after.instances.val[index.val]? = some next) :
    InitializerFunctionMetadata store inst after next := by
  cases effect with
  | unchanged =>
    have same : inst = next := Option.some.inj (found.symm.trans nextFound)
    subst next
    exact .refl _ _
  | appended elements addresses element elementValues addressValues =>
    have bound : index.val < store.instances.val.length := (List.getElem?_eq_some_iff.mp found).1
    simp only [alloc.vec.Vec.set_val_eq, List.getElem?_set, if_pos bound, ↓reduceIte,
      Option.some.injEq] at nextFound
    subst next
    constructor <;> try rfl
    simp [alloc.vec.Vec.length, alloc.vec.Vec.set_val_eq]

theorem DataStageEffect.function_metadata {M : Type} {store after : runtime.store.Store M}
    {index : Usize} {inst next : runtime.store.ModuleInst}
    (effect : DataStageEffect store index inst after)
    (found : store.instances.val[index.val]? = some inst)
    (nextFound : after.instances.val[index.val]? = some next) :
    InitializerFunctionMetadata store inst after next := by
  cases effect with
  | unchanged =>
    have same : inst = next := Option.some.inj (found.symm.trans nextFound)
    subst next
    exact .refl _ _
  | appended datas addresses data dataValues addressValues =>
    have bound : index.val < store.instances.val.length := (List.getElem?_eq_some_iff.mp found).1
    simp only [alloc.vec.Vec.set_val_eq, List.getElem?_set, if_pos bound, ↓reduceIte,
      Option.some.injEq] at nextFound
    subst next
    constructor <;> try rfl
    simp [alloc.vec.Vec.length, alloc.vec.Vec.set_val_eq]

end Itasca.Runtime.Store

end

/-! ## StoreParts -/

section

/-!
# Store loop result components

`storeParts` lists the store fields, platform state and result reconstructed by
store preparation loops. Initialization, staging and allocation proofs use this
shared projection independently of the Wasm 1.0 segment prechecks.

This small definition module sits below those proof families so they can share
the loop result representation without importing precheck proofs.
-/

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- The components returned by store preparation loops, in extracted tuple order. -/
def storeParts {M P : Type} (store : runtime.store.Store M) (platform : P)
    (status : core.result.Result Unit runtime.ExecError) :=
  (store.id, store.limits, store.funcs, store.types, store.tables, store.memories,
    store.globals, store.instances, store.elems, store.datas, store.externs,
    store.instance_items, store.signature_values, store.memory_bytes, store.table_elements,
    platform, status)

end Itasca.Runtime.Store

end

/-! ## ElementShapeLoop -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

private theorem elem_value_type_eq (ty : Itasca.wasm_types.ElemType) :
    wasm_types.ElemType.value_type ty = .ok (elementValueType ty) := by cases ty <;> rfl

private theorem encode_push_shape {M : Type} (store : runtime.store.Store M)
    (values : alloc.vec.Vec U64) (value : runtime.Value) (ty : Itasca.wasm_types.ElemType)
    (typed : elementValueType ty = Interp.rawType value) (owned : ValueInStore store value)
    (previous : ∀ word ∈ values.val, ReferenceShape store ty word)
    (room : values.length < Usize.max) :
    (do let (lo, _) ← runtime.value.encode value
        let next ← alloc.vec.Vec.push values lo
        .ok (next, (core.result.Result.Ok () : core.result.Result Unit runtime.ExecError)))
      ⦃ out => out.1.length = values.length + 1 ∧ out.2 = .Ok () ∧
        ∀ word ∈ out.1.val, ReferenceShape store ty word ⦄ := by
  step with encode_reference_shape store value ty typed owned as ⟨lo, high, shaped⟩
  step as ⟨next, hnext⟩
  refine ⟨by simp [alloc.vec.Vec.length, hnext], ?_⟩
  intro word member
  simp only [hnext, List.mem_append, List.mem_singleton] at member
  rcases member with old | rfl
  · exact previous word old
  · exact shaped

theorem element_initializers_shape_loop {M P F A : Type}
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
    (shaped : ∀ word ∈ values.val, ReferenceShape store segment.elem word) :
    runtime.store.instantiate.Store.add_instance_element_loop memory hooks floats allocator store platform
      instIndex index length values j status ⦃ out =>
        out.1 = store ∧ out.2.1 = platform ∧ out.2.2.1.length ≤ length.val ∧
        ∀ word ∈ out.2.2.1.val, ReferenceShape store segment.elem word ⦄ := by
  unfold runtime.store.instantiate.Store.add_instance_element_loop
  apply loop.spec_decr_nat (fun p => length.val - p.2.2.2.1.val)
    (fun p => p.1 = store ∧ p.2.1 = platform ∧
      p.2.2.1.length ≤ p.2.2.2.1.val ∧ p.2.2.2.1.val ≤ length.val ∧
      ∀ word ∈ p.2.2.1.val, ReferenceShape store segment.elem word)
  · rintro ⟨current, host, vals, k, state⟩ ⟨hcurrent, hhost, hvals, hk, refs⟩
    dsimp only at hcurrent hhost hvals hk refs ⊢
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
        step with eval_const_owned memory hooks floats allocator law store platform instIndex function
          inst code expr (elementValueType segment.elem) words hi hcode compiled resolved bindings
          as ⟨result, after, host', hs, hp, hvalue⟩
        subst after host'
        cases result with
        | Err error =>
          step as ⟨next, hnext⟩
          change vals.val.length ≤ next.val ∧ next.val ≤ length.val ∧
            (∀ word ∈ vals.val, ReferenceShape store segment.elem word) ∧ length.val - next.val < length.val - k.val
          exact ⟨by omega, by omega, refs, by omega⟩
        | Ok value =>
          obtain ⟨owned, typed⟩ := hvalue value rfl
          have room : vals.length < Usize.max := by scalar_tac
          apply WP.spec_bind (encode_push_shape store vals value segment.elem typed.symm owned refs room)
          rintro ⟨pushed, nextStatus⟩ ⟨hpush, hstatus, pushedRefs⟩
          step as ⟨next, hnext⟩
          refine ⟨?_, by omega, pushedRefs, by omega⟩
          rw [hpush]
          change vals.val.length + 1 ≤ next.val
          omega
    · have hstop : length.val ≤ k.val := by scalar_tac
      simp only [WP.spec_ok]
      simp only [true_and]
      change vals.val.length ≤ length.val ∧ ∀ word ∈ vals.val, ReferenceShape store segment.elem word
      exact ⟨by omega, refs⟩
  · exact ⟨rfl, rfl, hvalues, hj, shaped⟩

end Itasca.Runtime.Store

end
