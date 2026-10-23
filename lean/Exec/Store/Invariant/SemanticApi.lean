import Exec.Store.Api.Write
import Exec.Store.Invariant.ValueDecode

namespace Exec.Store
open Aeneas Aeneas.Std

theorem decodeStore_global_update {M : Type} (view : M → Slice U8)
    (code : CodeInterpretation) (s : runtime.store.Store M)
    (globals : alloc.vec.Vec runtime.store.GlobalInst) :
    decodeStore view code {s with globals} =
      {decodeStore view code s with GLOBALS := globals.val.map decodeGlobal} := by rfl

theorem decodeStore_table_update {M : Type} (view : M → Slice U8)
    (code : CodeInterpretation) (s : runtime.store.Store M)
    (tables : alloc.vec.Vec runtime.store.TableInst) :
    decodeStore view code {s with tables} =
      {decodeStore view code s with TABLES := tables.val.map decodeTable} := by rfl

/-- A mutable global API write has exactly the corresponding specification-store
update, preserving every other observable component. -/
theorem global_write_boundary {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : CodeInterpretation)
    (s : runtime.store.Store M) (index : Usize) (value : runtime.Value)
    (hindex : index.val < s.globals.length)
    (hmutable : (s.globals.val[index.val]).ty.mutability = .Var)
    (htype : (s.globals.val[index.val]).ty.valtype = Interp.rawType value)
    (hv : ValueInStore s value) :
    runtime.store.Store.set_global ops s ⟨s.id, index⟩ value ⦃ answer =>
      answer.1 = .Ok () ∧ decodeStore view code answer.2 =
        {decodeStore view code s with GLOBALS :=
          ((decodeStore view code s).GLOBALS.set index.val
            {decodeGlobal (s.globals.val[index.val]) with VALUE := Interp.sourceValue value})} ⦄ := by
  apply WP.spec_mono (global_write ops s index value hindex hmutable htype hv.1)
  intro answer effect
  rcases effect with ⟨words, hencode, _, hanswer⟩
  rw [hanswer]
  constructor
  · rfl
  · rw [decodeStore_global_update]
    have hvalue := decode_encoded_value s value hv words hencode
    simp [decodeStore, alloc.vec.Vec.set_val_eq, List.map_set, decodeGlobal, htype, hvalue]

/-- A table API write changes precisely one decoded reference, preserving its
type, size, limits, and every other component of the specification store. -/
theorem table_write_boundary {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : CodeInterpretation)
    (s : runtime.store.Store M) (tableIndex : Usize) (index : U32) (value : runtime.Value)
    (htable : tableIndex.val < s.tables.length)
    (hindex : index.val < (s.tables.val[tableIndex.val]).elements.length)
    (htype : elementValueType (s.tables.val[tableIndex.val]).ty = Interp.rawType value)
    (hv : ValueInStore s value) :
    runtime.store.Store.set_table ops s ⟨s.id, tableIndex⟩ index value ⦃ answer =>
      ∃ reference : ref, refVal reference = Interp.sourceValue value ∧ answer.1 = .Ok () ∧
        decodeStore view code answer.2 =
          {decodeStore view code s with TABLES :=
            ((decodeStore view code s).TABLES.set tableIndex.val
              {decodeTable (s.tables.val[tableIndex.val]) with REFS :=
                ((decodeTable (s.tables.val[tableIndex.val])).REFS.set index.val reference)})} ⦄ := by
  apply WP.spec_mono (table_write ops s tableIndex index value htable hindex htype hv)
  intro answer effect
  rcases effect with ⟨words, hencode, hanswer⟩
  refine ⟨decodeRef (s.tables.val[tableIndex.val]).ty words.1, ?_, ?_, ?_⟩
  · have hvalue := decode_encoded_value s value hv words hencode
    rw [← htype] at hvalue
    cases ht : (s.tables.val[tableIndex.val]).ty <;>
      simpa [elementValueType, ht, decodeWords] using hvalue
  · rw [hanswer]
  · rw [hanswer, decodeStore_table_update]
    simp [decodeStore, alloc.vec.Vec.set_val_eq, List.map_set, decodeTable]

end Exec.Store
