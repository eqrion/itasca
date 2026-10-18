import Exec.Store.Api.ApiGrowth

namespace Exec.Store
open Aeneas Aeneas.Std

/-- Store ownership is checked before any resource or buffer access. -/
theorem memory_grow_wrong_store {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (s : runtime.store.Store M) (address : runtime.MemoryAddr) (delta : U32)
    (hwrong : address.store ≠ s.id) :
    runtime.store.Store.grow_memory_with ops s address delta =
      .ok (.Err .WrongStore, s) := by
  simp [runtime.store.Store.grow_memory_with, runtime.store.Store.check, hwrong,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]


theorem memory_wrong_store {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (s : runtime.store.Store M) (address : runtime.MemoryAddr) 
    (hwrong : address.store ≠ s.id) :
    runtime.store.Store.memory ops s address = .ok ( .Err .WrongStore) := by
  simp [runtime.store.Store.memory, runtime.store.Store.check, hwrong,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

theorem memory_mut_wrong_store {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (s : runtime.store.Store M) (address : runtime.MemoryAddr) 
    (hwrong : address.store ≠ s.id) :
    runtime.store.Store.memory_mut ops s address = .ok ((.Err .WrongStore, fun _ => s)) := by
  simp [runtime.store.Store.memory_mut, hwrong]

theorem global_wrong_store {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (s : runtime.store.Store M) (address : runtime.GlobalAddr) 
    (hwrong : address.store ≠ s.id) :
    runtime.store.Store.global ops s address = .ok ( .Err .WrongStore) := by
  simp [runtime.store.Store.global, runtime.store.Store.check, hwrong,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

theorem table_size_wrong_store {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (s : runtime.store.Store M) (address : runtime.TableAddr) 
    (hwrong : address.store ≠ s.id) :
    runtime.store.Store.table_size ops s address = .ok ( .Err .WrongStore) := by
  simp [runtime.store.Store.table_size, runtime.store.Store.check, hwrong,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

theorem table_get_wrong_store {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (s : runtime.store.Store M) (address : runtime.TableAddr) (index : U32)
    (hwrong : address.store ≠ s.id) :
    runtime.store.Store.table_get ops s address index = .ok ( .Err .WrongStore) := by
  simp [runtime.store.Store.table_get, runtime.store.Store.check, hwrong,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

theorem set_global_wrong_store {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (s : runtime.store.Store M) (address : runtime.GlobalAddr) (value : runtime.Value)
    (hwrong : address.store ≠ s.id) :
    runtime.store.Store.set_global ops s address value = .ok ((.Err .WrongStore, s)) := by
  simp [runtime.store.Store.set_global, runtime.store.Store.check, hwrong,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

theorem set_table_wrong_store {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (s : runtime.store.Store M) (address : runtime.TableAddr) (index : U32) (value : runtime.Value)
    (hwrong : address.store ≠ s.id) :
    runtime.store.Store.set_table ops s address index value = .ok ((.Err .WrongStore, s)) := by
  simp [runtime.store.Store.set_table, runtime.store.Store.check, hwrong,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

theorem table_grow_wrong_store {M A : Type} (ops : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (s : runtime.store.Store M)
    (address : runtime.TableAddr) (delta : U32) (value : runtime.Value)
    (hwrong : address.store ≠ s.id) :
    runtime.store.Store.grow_table_with ops allocator s address delta value =
      .ok (.Err .WrongStore, s) := by
  simp [runtime.store.Store.grow_table_with, runtime.store.Store.check, hwrong,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

end Exec.Store
