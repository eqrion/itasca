import Exec.Store.Api.TableMemoryBindings
import Exec.Store.Initialization.SegmentTypes

namespace Exec.Store
open Aeneas Aeneas.Std

/-- Exact object metadata retained by initialization; payloads may be copied or dropped. -/
structure SegmentObjectMetadata {M : Type} (view : M → Slice U8)
    (before after : runtime.store.Store M) : Prop where
  space : SegmentAddressSpace before after
  tables : ∀ (index : Nat) (old : runtime.store.TableInst), before.tables.val[index]? = some old → ∃ (next : runtime.store.TableInst),
    after.tables.val[index]? = some next ∧ next.ty = old.ty ∧
    next.maximum = old.maximum ∧ next.elements.length = old.elements.length
  memories : ∀ (index : Nat) (old : runtime.store.MemInst M), before.memories.val[index]? = some old → ∃ (next : runtime.store.MemInst M),
    after.memories.val[index]? = some next ∧ next.maximum = old.maximum ∧
    (view next.buf).length = (view old.buf).length
  elements : ∀ (index : Nat) (old : runtime.store.ElemInst), before.elems.val[index]? = some old → ∃ (next : runtime.store.ElemInst),
    after.elems.val[index]? = some next ∧ next.ty = old.ty ∧
    (next.refs.val = old.refs.val ∨ next.refs.val = [])
  datas : ∀ (index : Nat) (old : runtime.store.DataInst), before.datas.val[index]? = some old → ∃ (next : runtime.store.DataInst),
    after.datas.val[index]? = some next ∧ (next.bytes.val = old.bytes.val ∨ next.bytes.val = [])

theorem SegmentObjectMetadata.refl {M : Type} (view : M → Slice U8) (store : runtime.store.Store M) :
    SegmentObjectMetadata view store store := by
  refine ⟨.refl _, ?_, ?_, ?_, ?_⟩
  · intro i old found; exact ⟨old, found, rfl, rfl, rfl⟩
  · intro i old found; exact ⟨old, found, rfl, rfl⟩
  · intro i old found; exact ⟨old, found, rfl, Or.inl rfl⟩
  · intro i old found; exact ⟨old, found, Or.inl rfl⟩

theorem SegmentObjectMetadata.trans {M : Type} {view : M → Slice U8} {a b c : runtime.store.Store M}
    (ab : SegmentObjectMetadata view a b) (bc : SegmentObjectMetadata view b c) :
    SegmentObjectMetadata view a c := by
  refine ⟨ab.space.trans bc.space, ?_, ?_, ?_, ?_⟩
  · intro i old found
    obtain ⟨mid, middle, ty, max, len⟩ := ab.tables i old found
    obtain ⟨next, last, ty', max', len'⟩ := bc.tables i mid middle
    exact ⟨next, last, ty'.trans ty, max'.trans max, len'.trans len⟩
  · intro i old found
    obtain ⟨mid, middle, max, len⟩ := ab.memories i old found
    obtain ⟨next, last, max', len'⟩ := bc.memories i mid middle
    exact ⟨next, last, max'.trans max, len'.trans len⟩
  · intro i old found
    obtain ⟨mid, middle, ty, content⟩ := ab.elements i old found
    obtain ⟨next, last, ty', content'⟩ := bc.elements i mid middle
    refine ⟨next, last, ty'.trans ty, ?_⟩
    rcases content' with same | empty
    · rcases content with original | dropped
      · exact Or.inl (same.trans original)
      · exact Or.inr (same.trans dropped)
    · exact Or.inr empty
  · intro i old found
    obtain ⟨mid, middle, content⟩ := ab.datas i old found
    obtain ⟨next, last, content'⟩ := bc.datas i mid middle
    refine ⟨next, last, ?_⟩
    rcases content' with same | empty
    · rcases content with original | dropped
      · exact Or.inl (same.trans original)
      · exact Or.inr (same.trans dropped)
    · exact Or.inr empty

theorem lookup_set_relation {T : Type} (values : List T) (index : Nat) (old replacement : T)
    (found : values[index]? = some old) (R : T → T → Prop)
    (refl : ∀ value, R value value) (changed : R old replacement) :
    ∀ (i : Nat) value, values[i]? = some value → ∃ next, (values.set index replacement)[i]? = some next ∧ R value next := by
  intro i value read
  by_cases same : i = index
  · subst i
    have equal : value = old := Option.some.inj (read.symm.trans found)
    subst value
    exact ⟨replacement, by simp [List.getElem?_set, (List.getElem?_eq_some_iff.mp found).1], changed⟩
  · exact ⟨value, by simp [List.getElem?_set, same, Ne.symm same, read], refl value⟩

end Exec.Store
