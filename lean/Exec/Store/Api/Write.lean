import Exec.Store.Api.Read
import Exec.Store.Invariant.ValueShape

namespace Exec.Store
open Aeneas Aeneas.Std

@[simp] theorem value_type_exact (value : runtime.Value) :
    runtime.Value.value_type value = .ok (Interp.rawType value) := by
  cases value <;> rfl

theorem check_value_owned {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (s : runtime.store.Store M) (value : runtime.Value)
    (hv : Interp.ValueOwnedFits s.id value) :
    runtime.store.Store.check_value ops s value = .ok (.Ok ()) := by
  cases value <;> simp only [runtime.store.Store.check_value]
  case FuncRef address =>
    cases address with
    | none => rfl
    | some a => simp only [Interp.ValueOwnedFits] at hv; simp [runtime.store.Store.check, hv.1]
  case ExternRef address =>
    cases address with
    | none => rfl
    | some a => simp only [Interp.ValueOwnedFits] at hv; simp [runtime.store.Store.check, hv.1]

@[simp] theorem value_type_eq_self (ty : Itasca.types.ValueType) :
    types.ValueType.Insts.CoreCmpPartialEqValueType.eq ty ty = .ok true := by
  cases ty <;> rfl

/-- An owned, correctly typed write to a mutable global stores exactly the
actual slot encoder's words, leaving every other store component unchanged. -/
theorem global_write {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (s : runtime.store.Store M) (index : Usize) (value : runtime.Value)
    (hindex : index.val < s.globals.length)
    (hmutable : (s.globals.val[index.val]).ty.mutability = .Var)
    (htype : (s.globals.val[index.val]).ty.valtype = Interp.rawType value)
    (hv : Interp.ValueOwnedFits s.id value) :
    runtime.store.Store.set_global ops s ⟨s.id, index⟩ value ⦃ answer =>
      ∃ words : U64 × U64,
        runtime.value.encode value = .ok words ∧
        Interp.pairWords (Interp.rawType value) words = Code.encodeValue (Interp.sourceValue value) ∧
        answer = (.Ok (), {s with globals := (s.globals.set index
          {(s.globals.val[index.val]) with lo := words.1, hi := words.2})}) ⦄ := by
  obtain ⟨words, hencode, hwords⟩ := WP.spec_imp_exists (Interp.encode_value_spec value s.id hv)
  unfold runtime.store.Store.set_global
  simp [runtime.store.Store.check, core.result.Result.Insts.CoreOpsTry.branch]
  rw [check_value_owned ops s value hv]
  simp
  step as ⟨global, back, hglobal, hback⟩
  simp only [hglobal, hmutable]
  simp [core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
    types.Mut.Insts.CoreCmpPartialEqMut.eq, Itasca.types.Mut.Insts.CoreCmpPartialEqMut.eq]
  cases words
  simpa [htype, hencode, hback] using hwords


/-- The public mutable-global write preserves structural store validity for
an existing, correctly typed, owned reference or numeric value. -/
theorem global_write_preserves_shape {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (s : runtime.store.Store M) (hs : Shape view s)
    (index : Usize) (value : runtime.Value) (hindex : index.val < s.globals.length)
    (hmutable : (s.globals.val[index.val]).ty.mutability = .Var)
    (htype : (s.globals.val[index.val]).ty.valtype = Interp.rawType value)
    (hv : ValueInStore s value) :
    runtime.store.Store.set_global ops s ⟨s.id, index⟩ value ⦃ answer => Shape view answer.2 ⦄ := by
  apply WP.spec_mono (global_write ops s index value hindex hmutable htype hv.1)
  intro answer effect
  rcases effect with ⟨words, hencode, _, hanswer⟩
  have hcanonical := encode_global_shape s value (s.globals.val[index.val]).ty htype hv
  rw [hencode] at hcanonical
  simp only [WP.spec_ok] at hcanonical
  rw [hanswer]
  exact hs.global_replace index _ hcanonical


@[simp] theorem element_value_type_exact (ty : Itasca.types.ElemType) :
    types.ElemType.value_type ty = .ok (elementValueType ty) := by
  cases ty <;> rfl

/-- An in-bounds table write changes only the selected encoded reference. -/
theorem table_write {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (s : runtime.store.Store M) (tableIndex : Usize) (index : U32) (value : runtime.Value)
    (htable : tableIndex.val < s.tables.length)
    (hindex : index.val < (s.tables.val[tableIndex.val]).elements.length)
    (htype : elementValueType (s.tables.val[tableIndex.val]).ty = Interp.rawType value)
    (hv : ValueInStore s value) :
    runtime.store.Store.set_table ops s ⟨s.id, tableIndex⟩ index value ⦃ answer =>
      ∃ words : U64 × U64, runtime.value.encode value = .ok words ∧
        answer = (.Ok (), {s with tables := (s.tables.set tableIndex
          {(s.tables.val[tableIndex.val]) with elements :=
            (s.tables.val[tableIndex.val]).elements.set (UScalar.cast .Usize index) words.1})}) ⦄ := by
  obtain ⟨words, hencode, _⟩ := WP.spec_imp_exists (Interp.encode_value_spec value s.id hv.1)
  unfold runtime.store.Store.set_table
  simp [runtime.store.Store.check, core.result.Result.Insts.CoreOpsTry.branch]
  rw [check_value_owned ops s value hv.1]
  simp
  step as ⟨table, back, htab, hback⟩
  simp [htab, htype, core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default]
  have hcast : (UScalar.cast .Usize index).val < (s.tables.val[tableIndex.val]).elements.length := by scalar_tac
  have hbound : ¬ (s.tables.val[tableIndex.val]).elements.val.length ≤ index.val :=
    Nat.not_le.mpr hindex
  simp [lift, hbound, hencode]
  cases words with
  | mk lo hi =>
    simp
    step as ⟨word, wordBack, hword, hwordBack⟩
    simp [hback, hwordBack]


theorem table_write_preserves_shape {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (s : runtime.store.Store M) (hs : Shape view s)
    (tableIndex : Usize) (index : U32) (value : runtime.Value)
    (htable : tableIndex.val < s.tables.length)
    (hindex : index.val < (s.tables.val[tableIndex.val]).elements.length)
    (htype : elementValueType (s.tables.val[tableIndex.val]).ty = Interp.rawType value)
    (hv : ValueInStore s value) :
    runtime.store.Store.set_table ops s ⟨s.id, tableIndex⟩ index value ⦃ answer => Shape view answer.2 ⦄ := by
  apply WP.spec_mono (table_write ops s tableIndex index value htable hindex htype hv)
  intro answer effect
  rcases effect with ⟨words, hencode, hanswer⟩
  have hcanonical := encode_reference_shape s value (s.tables.val[tableIndex.val]).ty htype hv
  rw [hencode] at hcanonical
  simp only [WP.spec_ok] at hcanonical
  have hbefore := hs.tables (s.tables.val[tableIndex.val]) (by simp)
  rw [hanswer]
  apply hs.table_replace_same_length tableIndex htable _ ?_ (by simp)
  refine ⟨?_, ?_, ?_⟩
  · simpa using hbefore.1
  · simpa using hbefore.2.1
  · intro word hword
    simp only [alloc.vec.Vec.set_val_eq] at hword
    rcases List.mem_or_eq_of_mem_set hword with hold | heq
    · exact hbefore.2.2 word hold
    · subst word; exact hcanonical

end Exec.Store
