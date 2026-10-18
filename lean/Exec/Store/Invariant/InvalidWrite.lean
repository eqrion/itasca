import Exec.Store.Api.Define

namespace Exec.Store
open Aeneas Aeneas.Std

@[simp] theorem vec_set_current {T : Type} (values : alloc.vec.Vec T) (index : Usize)
    (hindex : index.val < values.length) : values.set index values.val[index.val] = values := by
  apply alloc.vec.Vec.ext
  simp [alloc.vec.Vec.set_val_eq, List.set_getElem_self]

@[simp] theorem value_type_eq_different (a b : Itasca.types.ValueType) (hne : a ≠ b) :
    types.ValueType.Insts.CoreCmpPartialEqValueType.eq a b = .ok false := by
  cases a <;> cases b <;> simp_all [types.ValueType.Insts.CoreCmpPartialEqValueType.eq,
    Itasca.types.ValueType.Insts.CoreCmpPartialEqValueType.eq]

/-- Rejected global writes retain every raw store field. -/
theorem global_write_rejected {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (s : runtime.store.Store M) (index : Usize) (value : runtime.Value)
    (hindex : index.val < s.globals.length) (hv : ValueInStore s value)
    (hreject : (s.globals.val[index.val]).ty.mutability ≠ .Var ∨
      (s.globals.val[index.val]).ty.valtype ≠ Interp.rawType value) :
    runtime.store.Store.set_global ops s ⟨s.id, index⟩ value ⦃ answer =>
      answer = (.Err .BadArguments, s) ⦄ := by
  unfold runtime.store.Store.set_global
  simp [runtime.store.Store.check, core.result.Result.Insts.CoreOpsTry.branch]
  rw [check_value_owned ops s value hv.1]
  simp
  step as ⟨global, back, hglobal, hback⟩
  simp only [hglobal]
  cases hmut : (s.globals.val[index.val]).ty.mutability
  · simp [core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
      types.Mut.Insts.CoreCmpPartialEqMut.eq, Itasca.types.Mut.Insts.CoreCmpPartialEqMut.eq,
      hback, hglobal, alloc.vec.Vec.set_val_eq]
  · have htype : (s.globals.val[index.val]).ty.valtype ≠ Interp.rawType value := by simpa [hmut] using hreject
    simp [core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
      types.Mut.Insts.CoreCmpPartialEqMut.eq, Itasca.types.Mut.Insts.CoreCmpPartialEqMut.eq,
      htype, hback, hglobal, alloc.vec.Vec.set_val_eq]

/-- Every owned API value preserves the store invariant on a global write;
wrong types and immutable destinations are ordinary unchanged-store errors. -/
theorem global_write_any_preserves_shape {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (s : runtime.store.Store M) (hs : Shape view s)
    (index : Usize) (value : runtime.Value) (hindex : index.val < s.globals.length)
    (hv : ValueInStore s value) :
    runtime.store.Store.set_global ops s ⟨s.id, index⟩ value ⦃ answer => Shape view answer.2 ⦄ := by
  by_cases hm : (s.globals.val[index.val]).ty.mutability = .Var
  · by_cases ht : (s.globals.val[index.val]).ty.valtype = Interp.rawType value
    · exact global_write_preserves_shape ops view s hs index value hindex hm ht hv
    · apply WP.spec_mono (global_write_rejected ops s index value hindex hv (Or.inr ht))
      intro answer heq
      simpa [heq] using hs
  · apply WP.spec_mono (global_write_rejected ops s index value hindex hv (Or.inl hm))
    intro answer heq
    simpa [heq] using hs

/-- Table type and bounds errors preserve every raw store field. -/
theorem table_write_rejected {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (s : runtime.store.Store M) (tableIndex : Usize) (index : U32) (value : runtime.Value)
    (htable : tableIndex.val < s.tables.length) (hv : ValueInStore s value)
    (hreject : elementValueType (s.tables.val[tableIndex.val]).ty ≠ Interp.rawType value ∨
      (s.tables.val[tableIndex.val]).elements.length ≤ index.val) :
    runtime.store.Store.set_table ops s ⟨s.id, tableIndex⟩ index value ⦃ answer =>
      ∃ error, answer = (.Err error, s) ⦄ := by
  unfold runtime.store.Store.set_table
  simp [runtime.store.Store.check, core.result.Result.Insts.CoreOpsTry.branch]
  rw [check_value_owned ops s value hv.1]
  simp
  step as ⟨table, back, htableEq, hback⟩
  simp only [htableEq]
  by_cases ht : elementValueType (s.tables.val[tableIndex.val]).ty = Interp.rawType value
  · have hbound : (s.tables.val[tableIndex.val]).elements.length ≤ index.val := by simpa [ht] using hreject
    simp [ht, core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
      lift, hbound, hback, htableEq, alloc.vec.Vec.set_val_eq]
  · simp [ht, core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
      hback, htableEq, alloc.vec.Vec.set_val_eq]

theorem table_write_any_preserves_shape {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (s : runtime.store.Store M) (hs : Shape view s)
    (tableIndex : Usize) (index : U32) (value : runtime.Value)
    (htable : tableIndex.val < s.tables.length) (hv : ValueInStore s value) :
    runtime.store.Store.set_table ops s ⟨s.id, tableIndex⟩ index value ⦃ answer => Shape view answer.2 ⦄ := by
  by_cases ht : elementValueType (s.tables.val[tableIndex.val]).ty = Interp.rawType value
  · by_cases hi : index.val < (s.tables.val[tableIndex.val]).elements.length
    · exact table_write_preserves_shape ops view s hs tableIndex index value htable hi ht hv
    · apply WP.spec_mono (table_write_rejected ops s tableIndex index value htable hv (Or.inr (by omega)))
      rintro answer ⟨error, heq⟩
      simpa [heq] using hs
  · apply WP.spec_mono (table_write_rejected ops s tableIndex index value htable hv (Or.inl ht))
    rintro answer ⟨error, heq⟩
    simpa [heq] using hs

/-- A global initializer of the wrong type is rejected without retaining an
object or changing any resource counter. -/
theorem define_global_wrong_type {M A : Type} (ops : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (s : runtime.store.Store M)
    (ty : Itasca.types.GlobalType) (value : runtime.Value)
    (hbound : objectCount s ≤ Usize.max) (hv : ValueInStore s value)
    (htype : ty.valtype ≠ Interp.rawType value) :
    runtime.store.Store.define_global_with ops allocator s ty value ⦃ answer => answer.2 = s ⦄ := by
  unfold runtime.store.Store.define_global_with
  step with room_spec ops s hbound as ⟨room, hroom⟩
  rw [hroom]
  by_cases hspace : objectCount s < s.limits.max_objects.val
  · simp only [if_pos hspace]
    simp [core.result.Result.Insts.CoreOpsTry.branch]
    rw [check_value_owned ops s value hv.1]
    simp [htype, core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default]
  · simp [hspace, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

theorem define_global_any_preserves_shape {M A : Type} (ops : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (ha : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (s : runtime.store.Store M) (hs : Shape view s)
    (ty : Itasca.types.GlobalType) (value : runtime.Value) (hv : ValueInStore s value) :
    runtime.store.Store.define_global_with ops allocator s ty value ⦃ answer => Shape view answer.2 ⦄ := by
  by_cases ht : ty.valtype = Interp.rawType value
  · exact define_global_preserves_shape ops allocator ha view s hs ty value ht hv
  · have hbound : objectCount s ≤ Usize.max := by
      have h := hs.object_count_bound
      scalar_tac
    apply WP.spec_mono (define_global_wrong_type ops allocator s ty value hbound hv ht)
    intro answer heq
    simpa [heq] using hs

/-- A mismatched table-growth initializer has no allocation or store effect. -/
theorem table_grow_wrong_type {M A : Type} (ops : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (s : runtime.store.Store M)
    (index : Usize) (delta : U32) (value : runtime.Value)
    (hindex : index.val < s.tables.length) (hv : ValueInStore s value)
    (htype : elementValueType (s.tables.val[index.val]).ty ≠ Interp.rawType value) :
    runtime.store.Store.grow_table_with ops allocator s ⟨s.id, index⟩ delta value ⦃ answer =>
      answer = (.Err .BadArguments, s) ⦄ := by
  unfold runtime.store.Store.grow_table_with
  simp [runtime.store.Store.check, core.result.Result.Insts.CoreOpsTry.branch]
  rw [check_value_owned ops s value hv.1]
  simp
  step as ⟨table, htable⟩
  simp [htable, ne_comm.mp htype, core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default]

theorem table_grow_any_preserves_shape {M A : Type} (ops : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (ha : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (s : runtime.store.Store M) (hs : Shape view s)
    (index : Usize) (delta : U32) (value : runtime.Value)
    (hindex : index.val < s.tables.length) (hv : ValueInStore s value) :
    runtime.store.Store.grow_table_with ops allocator s ⟨s.id, index⟩ delta value ⦃ answer => Shape view answer.2 ⦄ := by
  by_cases ht : elementValueType (s.tables.val[index.val]).ty = Interp.rawType value
  · exact table_grow_api_preserves_shape ops allocator ha view s hs index delta value hindex ht hv
  · apply WP.spec_mono (table_grow_wrong_type ops allocator s index delta value hindex hv ht)
    intro answer heq
    simpa [heq] using hs

end Exec.Store
