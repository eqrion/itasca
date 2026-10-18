import Exec.Theorems.Api.ExecutableInvDefinitions
import Exec.Theorems.Api.ExecutableInvHost
import Exec.Store.Invariant.IssuedValues
namespace Exec.Theorems.ExecutableInv
open Aeneas Aeneas.Std

/-- A successful definition returns an issued handle in the preserved public invariant. -/
theorem define_extern_result {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store) (identity : U64) :
    runtime.store.Store.define_extern_with memory allocator store identity ⦃ result =>
      ExecutableInv view code result.2 ∧
      ∀ address, result.1 = .Ok address → address.store = result.2.id ∧
        address.index.val < result.2.externs.length ⦄ := by
  have bound : Store.objectCount store ≤ Usize.max := by
    have h := held.shape.object_count_bound
    scalar_tac
  obtain ⟨result, returned, fresh, rest⟩ := WP.spec_imp_exists
    (define_extern_certified memory allocator allocation view code store held identity)
  have effect := Store.define_extern_effect memory allocator allocation store identity bound
  rw [returned, WP.spec_ok] at effect ⊢
  refine ⟨fresh, ?_⟩
  rcases effect with ⟨error, same⟩ | ⟨externs, values, room, same⟩
  · simp [same]
  · intro address accepted
    rw [same] at accepted ⊢
    cases accepted
    simp [values, alloc.vec.Vec.length]

/-- A successful definition returns an issued handle in the preserved public invariant. -/
theorem define_memory_result {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store) (ty : Itasca.types.MemType) (buffer : M) :
    runtime.store.Store.define_memory_with memory allocator store ty buffer ⦃ result =>
      ExecutableInv view code result.2 ∧
      ∀ address, result.1 = .Ok address → address.store = result.2.id ∧
        address.index.val < result.2.memories.length ⦄ := by
  have bound : Store.objectCount store ≤ Usize.max := by
    have h := held.shape.object_count_bound
    scalar_tac
  obtain ⟨result, returned, fresh, rest⟩ := WP.spec_imp_exists
    (define_memory_certified memory allocator allocation view laws code store held ty buffer)
  have effect := Store.define_memory_effect memory allocator allocation view laws store ty buffer bound
  rw [returned, WP.spec_ok] at effect ⊢
  refine ⟨fresh, ?_⟩
  rcases effect with ⟨error, same⟩ | ⟨memories, count, values, limits, size, room, total, limit, same⟩
  · simp [same]
  · intro address accepted
    rw [same] at accepted ⊢
    cases accepted
    simp [values, alloc.vec.Vec.length]

/-- A successful definition returns an issued handle in the preserved public invariant. -/
theorem define_table_result {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store) (ty : Itasca.types.TableType) :
    runtime.store.Store.define_table_with memory allocator store ty ⦃ result =>
      ExecutableInv view code result.2 ∧
      ∀ address, result.1 = .Ok address → address.store = result.2.id ∧
        address.index.val < result.2.tables.length ⦄ := by
  have bound : Store.objectCount store ≤ Usize.max := by
    have h := held.shape.object_count_bound
    scalar_tac
  obtain ⟨result, returned, fresh, rest⟩ := WP.spec_imp_exists
    (define_table_certified memory allocator allocation view code store held ty)
  have effect := Store.define_table_effect memory allocator allocation store ty bound
  rw [returned, WP.spec_ok] at effect ⊢
  refine ⟨fresh, ?_⟩
  rcases effect with ⟨error, same⟩ | ⟨tables, elements, count, contents, values, limits, room, total, limit, same⟩
  · simp [same]
  · intro address accepted
    rw [same] at accepted ⊢
    cases accepted
    simp [values, alloc.vec.Vec.length]

/-- A successful definition returns an issued handle in the preserved public invariant. -/
theorem define_global_result {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store) (ty : Itasca.types.GlobalType) (value : runtime.Value)
    (typed : ty.valtype = Interp.rawType value) (owned : Store.ValueInStore store value) :
    runtime.store.Store.define_global_with memory allocator store ty value ⦃ result =>
      ExecutableInv view code result.2 ∧
      ∀ address, result.1 = .Ok address → address.store = result.2.id ∧
        address.index.val < result.2.globals.length ⦄ := by
  have bound : Store.objectCount store ≤ Usize.max := by
    have h := held.shape.object_count_bound
    scalar_tac
  obtain ⟨result, returned, fresh, rest⟩ := WP.spec_imp_exists
    (define_global_certified memory allocator allocation view code store held ty value typed owned)
  have effect := Store.define_global_effect memory allocator allocation store ty value bound typed owned
  rw [returned, WP.spec_ok] at effect ⊢
  refine ⟨fresh, ?_⟩
  rcases effect with ⟨error, same⟩ | ⟨globals, words, encoded, values, room, same⟩
  · simp [same]
  · intro address accepted
    rw [same] at accepted ⊢
    cases accepted
    simp [values, alloc.vec.Vec.length]

private theorem host_result {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (store : runtime.store.Store M) (shape : Store.Shape view store)
    (ty : Itasca.types.FuncType) (identity : U64) :
    runtime.store.Store.define_host_with memory allocator store ty identity ⦃ result =>
      ∀ address, result.1 = .Ok address → address.store = result.2.id ∧
        address.index.val < result.2.funcs.length ⦄ := by
  unfold runtime.store.Store.define_host_with
  step with Store.intern_type_preserves_shape memory allocator allocation view store shape ty
    as ⟨answer, interned, fresh, lookup⟩
  cases answer with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok signature =>
    simp [core.result.Result.Insts.CoreOpsTry.branch]
    have bound : Store.objectCount interned ≤ Usize.max := by
      have h := fresh.object_count_bound
      scalar_tac
    step with Store.room_spec memory interned bound as ⟨room, roomEq⟩
    rw [roomEq]
    by_cases space : Store.objectCount interned < interned.limits.max_objects.val
    · simp only [if_pos space]
      simp [core.result.Result.Insts.CoreOpsTry.branch]
      obtain ⟨answer, reserved⟩ := Store.reserve_wrapper_eq allocator allocation interned.funcs 1#usize
      rw [reserved]
      cases answer
      · simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      · simp
        have maximum : interned.funcs.length < Usize.max := by
          unfold Store.objectCount at space
          scalar_tac
        step as ⟨functions, values⟩
        simp [values, alloc.vec.Vec.length]
    · simp [space, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- Interning a host signature and defining a function returns a valid issued handle. -/
theorem define_host_result {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (ty : Itasca.types.FuncType) (identity : U64) :
    runtime.store.Store.define_host_with memory allocator store ty identity ⦃ result =>
      ExecutableInv view code result.2 ∧
      ∀ address, result.1 = .Ok address → address.store = result.2.id ∧
        address.index.val < result.2.funcs.length ⦄ := by
  obtain ⟨result, returned, fresh, rest⟩ := WP.spec_imp_exists
    (define_host_certified memory allocator allocation view code store held ty identity)
  have issued := host_result memory allocator allocation view store held.shape ty identity
  rw [returned, WP.spec_ok] at issued ⊢
  exact ⟨fresh, issued⟩

/-- Issued foreign initializers and wrong initializer types are normal errors;
any successful global definition returns an issued handle. -/
theorem define_global_issued_result {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (ty : Itasca.types.GlobalType) (value : runtime.Value) (issued : Store.IssuedValue store value) :
    runtime.store.Store.define_global_with memory allocator store ty value ⦃ result =>
      ExecutableInv view code result.2 ∧
      ∀ address, result.1 = .Ok address → address.store = result.2.id ∧
        address.index.val < result.2.globals.length ⦄ := by
  have bound : Store.objectCount store ≤ Usize.max := by
    have h := held.shape.object_count_bound
    scalar_tac
  rcases Store.issued_value_owned_or_foreign store value issued with owned | foreign
  · by_cases typed : ty.valtype = Interp.rawType value
    · exact define_global_result memory allocator allocation view code store held ty value typed owned
    · unfold runtime.store.Store.define_global_with
      step with Store.room_spec memory store bound as ⟨room, roomEq⟩
      rw [roomEq]
      by_cases space : Store.objectCount store < store.limits.max_objects.val
      · simp only [if_pos space]
        simp [core.result.Result.Insts.CoreOpsTry.branch]
        rw [Store.check_value_owned memory store value owned.1]
        simp [typed, core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default, held]
      · simp [space, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, held]
  · apply WP.spec_mono (Store.define_global_foreign_value memory allocator store ty value bound foreign)
    rintro result ⟨error, same⟩
    simp [same, held]
end Exec.Theorems.ExecutableInv
