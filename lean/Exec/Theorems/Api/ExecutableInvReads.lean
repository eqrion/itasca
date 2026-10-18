import Exec.Theorems.Api.ExecutableInv
import Exec.Theorems.Api.CertifiedApiReads
import Exec.Store.Api.ReadOwnership
namespace Exec.Theorems.ExecutableInv
open Aeneas Aeneas.Std

theorem function_type {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (address : runtime.FuncAddr)
    (issued : address.store = store.id → address.index.val < store.funcs.length) :
    runtime.store.Store.func_type memory store address ⦃ result => ExecutableInv view code store ∧
      ((address.store ≠ store.id ∧ result = .Err .WrongStore) ∨
      (address.store = store.id ∧ ∃ ty, result = .Ok ty ∧
        ∀ found : address.index.val < store.funcs.length,
          Store.decodeFuncType ty = (Store.decodeFunction code store store.funcs.val[address.index.val]).TYPE)) ⦄ :=
  WP.spec_mono (CertifiedApi.function_type_issued memory view code store held.toCertifiedApiStore address issued)
    (fun _ post => ⟨held,post⟩)

theorem memory_read {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store) (address : runtime.MemoryAddr)
    (issued : address.store = store.id → address.index.val < store.memories.length) :
    runtime.store.Store.memory memory store address ⦃ result => ExecutableInv view code store ∧
      ((address.store ≠ store.id ∧ result = .Err .WrongStore) ∨
      (address.store = store.id ∧ ∀ found : address.index.val < store.memories.length,
        result = .Ok (view store.memories.val[address.index.val].buf))) ⦄ :=
  WP.spec_mono (CertifiedApi.memory_read_issued memory view laws store address issued) (fun _ post => ⟨held,post⟩)

theorem export_lookup {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (address : runtime.InstanceAddr) (query : Slice U8)
    (issued : address.store = store.id → address.index.val < store.instances.length) :
    runtime.store.Store.export memory store address query ⦃ result => ExecutableInv view code store ∧
      ((address.store ≠ store.id ∧ result = .Err .WrongStore) ∨
      (address.store = store.id ∧ ∃ found, result = .Ok found ∧
        ∀ external ∈ found, Store.ExternalIssued store external)) ⦄ :=
  WP.spec_mono (CertifiedApi.export_issued_certified memory view code store held.toCertifiedApiStore address query issued)
    (fun _ post => ⟨held,post⟩)

theorem global_read {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store) (address : runtime.GlobalAddr)
    (issued : address.store = store.id → address.index.val < store.globals.length) :
    runtime.store.Store.global memory store address ⦃ result => ExecutableInv view code store ∧
      ((address.store ≠ store.id ∧ result = .Err .WrongStore) ∨
      (address.store = store.id ∧ ∃ value, result = .Ok value ∧ Store.ValueInStore store value)) ⦄ := by
  by_cases owner : address.store = store.id
  · have bound := issued owner
    cases address with
    | mk id index =>
      dsimp only at owner bound
      subst id
      apply WP.spec_mono (Store.global_read_owned memory view store held.shape index bound)
      intro result post
      exact ⟨held,Or.inr ⟨rfl,post⟩⟩
  · simp [runtime.store.Store.global,runtime.store.Store.check,owner,
      core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,held]

theorem table_read {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store) (address : runtime.TableAddr) (index : U32)
    (issued : address.store = store.id → address.index.val < store.tables.length) :
    runtime.store.Store.table_get memory store address index ⦃ result => ExecutableInv view code store ∧
      ((address.store ≠ store.id ∧ result = .Err .WrongStore) ∨
      (address.store = store.id ∧ (result = .Err (.Trap .TableOutOfBounds) ∨
        ∃ value, result = .Ok value ∧ Store.ValueInStore store value))) ⦄ := by
  by_cases owner : address.store = store.id
  · have bound := issued owner
    cases address with
    | mk id tableIndex =>
      dsimp only at owner bound
      subst id
      apply WP.spec_mono (Store.table_read_owned memory view store held.shape tableIndex index bound)
      intro result post
      exact ⟨held,Or.inr ⟨rfl,post⟩⟩
  · simp [runtime.store.Store.table_get,runtime.store.Store.check,owner,
      core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,held]

theorem table_size {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store) (address : runtime.TableAddr)
    (issued : address.store = store.id → address.index.val < store.tables.length) :
    runtime.store.Store.table_size memory store address ⦃ result => ExecutableInv view code store ∧
      ((address.store ≠ store.id ∧ result = .Err .WrongStore) ∨
      (address.store = store.id ∧ ∃ size : U32, result = .Ok size ∧
        ∀ found : address.index.val < store.tables.length,
          size.val = (Store.decodeTable store.tables.val[address.index.val]).REFS.length)) ⦄ := by
  by_cases owner : address.store = store.id
  · have bound := issued owner
    cases address with
    | mk id index =>
      dsimp only at owner bound
      subst id
      apply WP.spec_mono (Store.table_size_read memory store index bound
        (held.shape.tables _ (List.getElem_mem bound)).1)
      rintro result ⟨size,returned,count⟩
      exact ⟨held,Or.inr ⟨rfl,size,returned,fun _ => count⟩⟩
  · simp [runtime.store.Store.table_size,runtime.store.Store.check,owner,
      core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,held]

theorem extern_identity {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store) (address : runtime.ExternAddr)
    (issued : address.store = store.id → address.index.val < store.externs.length) :
    runtime.store.Store.extern_identity memory store address ⦃ result => ExecutableInv view code store ∧
      ((address.store ≠ store.id ∧ result = .Err .WrongStore) ∨
      (address.store = store.id ∧ ∀ found : address.index.val < store.externs.length,
        result = .Ok store.externs.val[address.index.val])) ⦄ := by
  by_cases owner : address.store = store.id
  · have bound := issued owner
    cases address with
    | mk id index =>
      dsimp only at owner bound
      subst id
      apply WP.spec_mono (Store.extern_identity_read memory store index bound)
      intro result returned
      exact ⟨held,Or.inr ⟨rfl,fun _ => returned⟩⟩
  · simp [runtime.store.Store.extern_identity,runtime.store.Store.check,owner,
      core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,held]
end Exec.Theorems.ExecutableInv
