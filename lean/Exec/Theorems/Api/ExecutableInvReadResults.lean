import Exec.Theorems.Api.ExecutableInvReads
import Exec.Store.Invariant.IssuedValues
namespace Exec.Theorems.ExecutableInv
open Aeneas Aeneas.Std

/-- Owned read results satisfy the public issued-value argument discipline. -/
theorem value_issued {M : Type} {store : runtime.store.Store M} {value : runtime.Value}
    (owned : Store.ValueInStore store value) : Store.IssuedValue store value := by
  cases value <;> simp only [Store.IssuedValue, Store.ValueInStore] at owned ⊢
  all_goals try trivial
  all_goals rename_i address
  all_goals cases address <;> simp_all

theorem global_read_issued {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store) (address : runtime.GlobalAddr)
    (issued : address.store = store.id → address.index.val < store.globals.length) :
    runtime.store.Store.global memory store address ⦃ result => ExecutableInv view code store ∧
      ∀ value, result = .Ok value → Store.IssuedValue store value ⦄ := by
  apply WP.spec_mono (global_read memory view code store held address issued)
  rintro result ⟨fresh, rejected | ⟨owner,value,returned,owned⟩⟩
  · exact ⟨fresh, by simp [rejected.2]⟩
  · refine ⟨fresh, ?_⟩
    intro actual accepted
    cases returned.symm.trans accepted
    exact value_issued owned

theorem table_read_issued {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store) (address : runtime.TableAddr) (index : U32)
    (issued : address.store = store.id → address.index.val < store.tables.length) :
    runtime.store.Store.table_get memory store address index ⦃ result => ExecutableInv view code store ∧
      ∀ value, result = .Ok value → Store.IssuedValue store value ⦄ := by
  apply WP.spec_mono (table_read memory view code store held address index issued)
  rintro result ⟨fresh, rejected | ⟨owner,rejected | ⟨value,returned,owned⟩⟩⟩
  · exact ⟨fresh, by simp [rejected.2]⟩
  · exact ⟨fresh, by simp [rejected]⟩
  · refine ⟨fresh, ?_⟩
    intro actual accepted
    cases returned.symm.trans accepted
    exact value_issued owned
end Exec.Theorems.ExecutableInv
