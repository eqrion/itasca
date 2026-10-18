import Exec.Store.Api.ExportLookup
import Exec.Theorems.Api.CertifiedApi
import Exec.Store.Api.ApiMetadata
namespace Exec.Theorems.CertifiedApi
open Aeneas Aeneas.Std
variable {emission : Interp.StructuredMachine.FunctionEmission} {allowed : instr → Prop}

/-- Issued function handles return their exact decoded signature or the
unchanged-store foreign-identity rejection. -/
theorem function_type_issued {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (certified : CertifiedApiStore emission allowed view code store)
    (address : runtime.FuncAddr)
    (issued : address.store = store.id → address.index.val < store.funcs.length) :
    runtime.store.Store.func_type memory store address ⦃ result =>
      (address.store ≠ store.id ∧ result = .Err .WrongStore) ∨
      (address.store = store.id ∧ ∃ ty, result = .Ok ty ∧
        ∀ found : address.index.val < store.funcs.length,
          Store.decodeFuncType ty = (Store.decodeFunction code store store.funcs.val[address.index.val]).TYPE) ⦄ := by
  by_cases owner : address.store = store.id
  · have bound := issued owner
    cases address with
    | mk id index =>
      dsimp only at owner bound
      subst id
      apply WP.spec_mono (Store.function_type_read memory view code store certified.shape index bound)
      rintro result ⟨ty,returned,typed⟩
      exact Or.inr ⟨rfl,ty,returned,fun _ => typed⟩
  · unfold runtime.store.Store.func_type
    simp [runtime.store.Store.check,owner,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

theorem memory_read_issued {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (store : runtime.store.Store M) (address : runtime.MemoryAddr)
    (issued : address.store = store.id → address.index.val < store.memories.length) :
    runtime.store.Store.memory memory store address ⦃ result =>
      (address.store ≠ store.id ∧ result = .Err .WrongStore) ∨
      (address.store = store.id ∧ ∀ found : address.index.val < store.memories.length,
        result = .Ok (view store.memories.val[address.index.val].buf)) ⦄ := by
  by_cases owner : address.store = store.id
  · have bound := issued owner
    cases address with
    | mk id index =>
      dsimp only at owner bound
      subst id
      apply WP.spec_mono (Store.memory_read memory view laws store index bound)
      intro result returned
      exact Or.inr ⟨rfl,fun _ => returned⟩
  · unfold runtime.store.Store.memory
    simp [runtime.store.Store.check,owner,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- Export lookup is total at issued instance handles, including foreign-store
rejection, and can only yield another issued external handle. -/
theorem export_issued_certified {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (certified : CertifiedApiStore emission allowed view code store)
    (address : runtime.InstanceAddr) (query : Slice U8)
    (issued : address.store = store.id → address.index.val < store.instances.length) :
    runtime.store.Store.export memory store address query ⦃ result =>
      (address.store ≠ store.id ∧ result = .Err .WrongStore) ∨
      (address.store = store.id ∧ ∃ found, result = .Ok found ∧
        ∀ external ∈ found, Store.ExternalIssued store external) ⦄ :=
  Store.export_issued memory view store certified.shape certified.exportBounds address query issued
end Exec.Theorems.CertifiedApi
