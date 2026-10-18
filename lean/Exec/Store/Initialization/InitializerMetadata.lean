import Exec.Store.Initialization.SegmentEffects

namespace Exec.Store
open Aeneas Aeneas.Std

/-- Constant/segment staging changes only value and segment maps. The exact
metadata used by retained function certificates remains unchanged. -/
structure InitializerFunctionMetadata {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.Instance) (after : runtime.store.Store M) (next : runtime.store.Instance) : Prop where
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
    (inst : runtime.store.Instance) : InitializerFunctionMetadata store inst store inst := by
  constructor <;> rfl

theorem InitializerFunctionMetadata.trans {M : Type} {a b c : runtime.store.Store M}
    {i j k : runtime.store.Instance} (first : InitializerFunctionMetadata a i b j)
    (second : InitializerFunctionMetadata b j c k) : InitializerFunctionMetadata a i c k := by
  exact ⟨second.identity.trans first.identity, second.functions.trans first.functions,
    second.signatures.trans first.signatures, second.source.trans first.source,
    second.typeMap.trans first.typeMap, second.functionMap.trans first.functionMap,
    second.tables.trans first.tables, second.tableMap.trans first.tableMap,
    second.memories.trans first.memories, second.memoryMap.trans first.memoryMap,
    second.instanceCount.trans first.instanceCount⟩

def InitializerFunctionMetadataAt {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.Instance) (after : runtime.store.Store M) (index : Usize) : Prop :=
  ∃ next, after.instances.val[index.val]? = some next ∧ InitializerFunctionMetadata store inst after next

theorem InitializerFunctionMetadataAt.resolve {M : Type} {store after : runtime.store.Store M}
    {inst next : runtime.store.Instance} {index : Usize}
    (metadata : InitializerFunctionMetadataAt store inst after index)
    (found : after.instances.val[index.val]? = some next) : InitializerFunctionMetadata store inst after next := by
  obtain ⟨actual, lookup, matching⟩ := metadata
  have same : actual = next := Option.some.inj (lookup.symm.trans found)
  exact same ▸ matching

theorem GlobalStageEffect.function_metadata {M : Type} {store after : runtime.store.Store M}
    {index : Usize} {inst next : runtime.store.Instance}
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
    {index : Usize} {inst next : runtime.store.Instance}
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
    {index : Usize} {inst next : runtime.store.Instance}
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

end Exec.Store
