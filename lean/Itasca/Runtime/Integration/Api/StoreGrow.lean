import Itasca.Runtime.Integration.Api.StoreCreate

/-! Public growth preserves executable certificates and records its exact raw effect. -/

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std Store

/-- Memory growth preserves executable stores, including the failure sentinel. -/
@[step] theorem _root_.Itasca.runtime.store.Store.grow_memory_with.spec {M : Type}
    (memory : runtime.platform.MemoryBuffer M) (view : M → Slice U8)
    (laws : Platform.MemoryLaws memory view) (code : CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (address : runtime.MemoryAddr) (delta : U32)
    (issued : ExternalIssued store (.Memory address)) :
    runtime.store.Store.grow_memory_with memory store address delta ⦃ (result, after) =>
      ExecutableInv view code after ∧ CumulativeStoreMutation view code store after ∧
      match result with
      | .Err error => error = .WrongStore ∧ address.store ≠ store.id ∧ after = store
      | .Ok pages => address.store = store.id ∧
          MemoryGrowth view code store address.index delta (pages, after) ⦄ := by
  unfold runtime.store.Store.grow_memory_with
  step with runtime.store.Store.check.spec memory store address.store as ⟨checkedStore, checkedStoreEq⟩
  rw [checkedStoreEq]
  by_cases owner : address.store = store.id
  · simp only [if_pos owner, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    have inside := issued owner
    step with memory_grow_effect memory view laws code store address.index delta inside
      (fun object member => (held.shape.memories object member).length_bound)
      (fun object member => (held.shape.memories object member).1)
      as ⟨pages, after, effect⟩
    have extension := effect.extends view code store held.shape held.storeSyntax
      address.index delta inside (pages, after)
    have mutation := memory_growth_cumulative_mutation_of_shape held.shape held.storeSyntax
      held.segmentBounds inside effect extension
    exact ⟨held.update mutation, mutation, owner, effect⟩
  · simp only [if_neg owner, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
    exact ⟨held, .refl_of_shape held.shape held.storeSyntax held.segmentBounds, rfl, owner, rfl⟩

/-- Table growth checks ownership and reference type before extending the table. -/
@[step] theorem _root_.Itasca.runtime.store.Store.grow_table_with.spec {M A : Type}
    (memory : runtime.platform.MemoryBuffer M) (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (address : runtime.TableAddr) (delta : U32) (value : runtime.Value)
    (issued : ExternalIssued store (.Table address)) (valueIssued : IssuedValue store value) :
    runtime.store.Store.grow_table_with memory allocator store address delta value ⦃ (result, after) =>
      ExecutableInv view code after ∧ CumulativeStoreMutation view code store after ∧
      match result with
      | .Err error => after = store ∧ (error = .WrongStore ∨ error = .BadArguments)
      | .Ok size => address.store = store.id ∧ ∃ words : U64 × U64,
          runtime.value.encode value = .ok words ∧
          TableGrowth store address.index delta words.1 (size, after) ⦄ := by
  classical
  unfold runtime.store.Store.grow_table_with
  step with runtime.store.Store.check.spec memory store address.store as ⟨checkedStore, checkedStoreEq⟩
  rw [checkedStoreEq]
  by_cases owner : address.store = store.id
  · simp only [if_pos owner, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with Interp.check_value_eq memory store value as ⟨checked, checkedEq⟩
    rw [checkedEq]
    by_cases valueOwner : Interp.OwnedBy store.id value
    · simp only [Interp.checkOwner, if_pos valueOwner,
        core.result.Result.Insts.CoreOpsTry.branch, bind_ok, value_type_exact]
      have inside := issued owner
      step as ⟨table, tableEq⟩
      simp only [element_value_type_exact, Interp.value_type_ne_eq, bind_ok]
      by_cases matching : Interp.rawType value = elementValueType table.ty
      · simp only [if_pos matching, Bool.false_eq_true, ite_false]
        obtain ⟨words, encoded, reference⟩ := WP.spec_imp_exists
          (encode_reference_shape store value table.ty matching.symm (valueIssued.in_store valueOwner))
        cases words with
        | mk lo hi =>
          change ReferenceShape store table.ty lo at reference
          rw [encoded, bind_ok]
          step with table_grow_effect memory allocator law store address.index delta lo inside
            (fun object member => (held.shape.tables object member).1)
            as ⟨size, after, effect⟩
          have owned : ReferenceShape store (store.tables.val[address.index.val]).ty lo := by
            simpa only [tableEq] using reference
          have extension := effect.extends view code store held.shape held.storeSyntax
            address.index delta lo inside owned (size, after)
          have mutation := table_growth_cumulative_mutation_of_shape held.shape held.storeSyntax
            held.segmentBounds inside owned effect extension
          exact ⟨held.update mutation, mutation, owner, effect⟩
      · simp only [if_neg matching, ite_true, WP.spec_ok]
        exact ⟨held, .refl_of_shape held.shape held.storeSyntax held.segmentBounds,
          rfl, Or.inr rfl⟩
    · simp only [Interp.checkOwner, if_neg valueOwner,
        core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
      exact ⟨held, .refl_of_shape held.shape held.storeSyntax held.segmentBounds,
        rfl, Or.inl rfl⟩
  · simp only [if_neg owner, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
    exact ⟨held, .refl_of_shape held.shape held.storeSyntax held.segmentBounds,
      rfl, Or.inl rfl⟩

end Itasca.Runtime.Integration
