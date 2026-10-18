import Exec.Store.Invariant.InvalidWrite

namespace Exec.Store
open Aeneas Aeneas.Std

/-- A reference value whose private handle belongs to another store. Numeric
values and null references are never foreign. -/
def ForeignValue {M : Type} (s : runtime.store.Store M) : runtime.Value → Prop
  | .FuncRef (some a) => a.store ≠ s.id
  | .ExternRef (some a) => a.store ≠ s.id
  | _ => False

theorem check_value_foreign {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (s : runtime.store.Store M) (value : runtime.Value) (hv : ForeignValue s value) :
    runtime.store.Store.check_value ops s value = .ok (.Err .WrongStore) := by
  cases value <;> simp only [ForeignValue] at hv
  all_goals try contradiction
  case FuncRef address =>
    cases address with
    | none => contradiction
    | some a => simpa [runtime.store.Store.check_value, runtime.store.Store.check, hv, ne_comm] using hv
  case ExternRef address =>
    cases address with
    | none => contradiction
    | some a => simpa [runtime.store.Store.check_value, runtime.store.Store.check, hv, ne_comm] using hv

theorem global_write_foreign_value {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (s : runtime.store.Store M) (index : Usize) (value : runtime.Value) (hv : ForeignValue s value) :
    runtime.store.Store.set_global ops s ⟨s.id, index⟩ value = .ok (.Err .WrongStore, s) := by
  simp [runtime.store.Store.set_global, runtime.store.Store.check,
    core.result.Result.Insts.CoreOpsTry.branch, check_value_foreign ops s value hv,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

theorem table_write_foreign_value {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (s : runtime.store.Store M) (tableIndex : Usize) (index : U32) (value : runtime.Value)
    (hv : ForeignValue s value) :
    runtime.store.Store.set_table ops s ⟨s.id, tableIndex⟩ index value = .ok (.Err .WrongStore, s) := by
  simp [runtime.store.Store.set_table, runtime.store.Store.check,
    core.result.Result.Insts.CoreOpsTry.branch, check_value_foreign ops s value hv,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

theorem table_grow_foreign_value {M A : Type} (ops : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (s : runtime.store.Store M)
    (index : Usize) (delta : U32) (value : runtime.Value) (hv : ForeignValue s value) :
    runtime.store.Store.grow_table_with ops allocator s ⟨s.id, index⟩ delta value = .ok (.Err .WrongStore, s) := by
  simp [runtime.store.Store.grow_table_with, runtime.store.Store.check,
    core.result.Result.Insts.CoreOpsTry.branch, check_value_foreign ops s value hv,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

theorem define_global_foreign_value {M A : Type} (ops : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (s : runtime.store.Store M)
    (ty : Itasca.types.GlobalType) (value : runtime.Value)
    (hbound : objectCount s ≤ Usize.max) (hv : ForeignValue s value) :
    runtime.store.Store.define_global_with ops allocator s ty value ⦃ answer =>
      ∃ error, answer = (.Err error, s) ⦄ := by
  unfold runtime.store.Store.define_global_with
  step with room_spec ops s hbound as ⟨room, hroom⟩
  rw [hroom]
  by_cases hspace : objectCount s < s.limits.max_objects.val
  · simp [hspace, core.result.Result.Insts.CoreOpsTry.branch,
      check_value_foreign ops s value hv,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  · simp [hspace, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

end Exec.Store
