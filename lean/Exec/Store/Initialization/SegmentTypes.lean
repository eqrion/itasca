import Exec.Store.Initialization.SegmentReady

namespace Exec.Store
open Aeneas Aeneas.Std

/-- The two reference type spaces stay fixed while segment instructions update
only table words and element-segment payloads. -/
structure SegmentTypes {M : Type} (before after : runtime.store.Store M) : Prop where
  tables : after.tables.val.map runtime.store.TableInst.ty = before.tables.val.map runtime.store.TableInst.ty
  elements : after.elems.val.map runtime.store.ElemInst.ty = before.elems.val.map runtime.store.ElemInst.ty

theorem SegmentTypes.refl {M : Type} (store : runtime.store.Store M) : SegmentTypes store store := ⟨rfl, rfl⟩

theorem SegmentTypes.trans {M : Type} {a b c : runtime.store.Store M}
    (ab : SegmentTypes a b) (bc : SegmentTypes b c) : SegmentTypes a c :=
  ⟨bc.tables.trans ab.tables, bc.elements.trans ab.elements⟩

private theorem map_replace_type {T U : Type} (values : List T) (index : Nat) (old value : T)
    (tag : T → U) (found : values[index]? = some old) (same : tag value = tag old) :
    (values.set index value).map tag = values.map tag := by
  induction values generalizing index with
  | nil => simp at found
  | cons head tail ih =>
    cases index with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at found; subst old; simp [same]
    | succ index =>
      simp only [List.getElem?_cons_succ] at found
      simpa using ih index found

theorem TableInitializationEffect.types {M : Type} {store : runtime.store.Store M}
    {index table segment destination source count out}
    (effect : TableInitializationEffect store index table segment destination source count out)
    (target : store.tables.val[index.val]? = some table) : SegmentTypes store out.2 := by
  unfold TableInitializationEffect at effect
  split at effect
  · obtain ⟨words, rfl, _⟩ := effect
    constructor
    · simpa only [alloc.vec.Vec.set_val_eq] using map_replace_type store.tables.val index.val table {table with elements := words} runtime.store.TableInst.ty target rfl
    · rfl
  · rw [effect]; exact .refl store

theorem MemoryInitializationEffect.types {M : Type} {view : M → Slice U8} {store : runtime.store.Store M}
    {index memory segment destination source count out}
    (effect : MemoryInitializationEffect view store index memory segment destination source count out) : SegmentTypes store out.2 := by
  unfold MemoryInitializationEffect at effect
  split at effect
  · obtain ⟨buffer, rfl, _⟩ := effect
    exact ⟨rfl, rfl⟩
  · rw [effect]; exact .refl store

theorem SegmentTypes.element_drop {M : Type} (store : runtime.store.Store M) (address : Usize)
    (segment : runtime.store.ElemInst) (found : store.elems.val[address.val]? = some segment) :
    SegmentTypes store {store with elems := store.elems.set address {segment with refs := alloc.vec.Vec.new U64}} := by
  constructor
  · rfl
  · simpa only [alloc.vec.Vec.set_val_eq] using map_replace_type store.elems.val address.val segment {segment with refs := alloc.vec.Vec.new U64}
      runtime.store.ElemInst.ty found rfl

/-- Raw staged table and element types agree with their source index spaces.
This is a link/staging metadata condition, not an interpreter postcondition. -/
structure SegmentTypeBindings {M : Type} (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) : Prop where
  tables : ∀ (index : Nat) (source : Itasca.types.TableType) (address : runtime.TableAddr) (table : runtime.store.TableInst),
    inst.module.module.env.table_types.val[index]? = some source → inst.tables.val[index]? = some address →
    store.tables.val[address.index.val]? = some table → table.ty = source.elem
  elements : ∀ (index : Nat) (source : Itasca.module.Element) (address : Usize) (segment : runtime.store.ElemInst),
    inst.module.module.env.elements.val[index]? = some source → inst.elems.val[index]? = some address →
    store.elems.val[address.val]? = some segment → segment.ty = source.elem

private theorem tags_lookup {T U : Type} {before after : List T} {tag : T → U}
    (same : after.map tag = before.map tag) {index : Nat} {value : T}
    (found : after[index]? = some value) : ∃ old, before[index]? = some old ∧ tag old = tag value := by
  have read := congrArg (fun values : List U => values[index]?) same
  simp only [List.getElem?_map, found, Option.map_some] at read
  cases previous : before[index]? with
  | none => simp [previous] at read
  | some old => exact ⟨old, rfl, by simpa [previous] using read.symm⟩

theorem SegmentTypeBindings.transport {M : Type} {store after : runtime.store.Store M} {inst : runtime.store.ModuleInst}
    (bindings : SegmentTypeBindings store inst) (types : SegmentTypes store after) : SegmentTypeBindings after inst := by
  constructor
  · intro index source address table sourceFound mapped found
    obtain ⟨old, oldFound, typeEq⟩ := tags_lookup types.tables found
    exact typeEq.symm.trans (bindings.tables index source address old sourceFound mapped oldFound)
  · intro index source address segment sourceFound mapped found
    obtain ⟨old, oldFound, typeEq⟩ := tags_lookup types.elements found
    exact typeEq.symm.trans (bindings.elements index source address old sourceFound mapped oldFound)

end Exec.Store
