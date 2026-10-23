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

end Exec.Store
