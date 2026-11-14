import Itasca.Generated.FunsInstantiate
import Itasca.Runtime.Store.Preparation.AllocationStorage
import Itasca.Runtime.Store.Initialization.ElementSourceStaging
import Itasca.Runtime.Store.Initialization.DataEffects
import Itasca.Runtime.Compiler.Local.Initializer

/-!
Sections, each formerly its own module: AllocationInitializers, PreparationErrorLoops.
-/

/-! ## AllocationInitializers -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem GlobalStageEffect.allocated {M : Type} {view : M → Slice U8} {store after : runtime.store.Store M}
    {index inst} (effect : GlobalStageEffect store index inst after) (shape : AllocationShape view store) :
    AllocationShape view after := by
  cases effect with
  | unchanged => exact shape
  | appended globals addresses global appended mapped canonical room =>
    constructor
    · exact shape.identity
    · exact shape.memories
    · simpa only [TableShape, ReferenceShape] using shape.tables
    · intro value member
      simp only [appended, List.mem_append, List.mem_singleton] at member
      rcases member with old | rfl
      · simpa only [GlobalShape, ReferenceShape] using shape.globals value old
      · simpa only [GlobalShape, ReferenceShape] using canonical
    · simpa only [ReferenceShape] using shape.elements
    · exact shape.canonicalTypes
    · simp only [objectCount, alloc.vec.Vec.length, appended, List.length_append, List.length_singleton]
      unfold objectCount at room
      simp only [alloc.vec.Vec.length] at room
      omega
    · exact shape.signatureAccounting
    · exact shape.signatureLimit
    · exact shape.memoryAccounting
    · exact shape.memoryLimit
    · exact shape.tableAccounting
    · exact shape.tableLimit

theorem ElementContentEffect.allocated {M : Type} {view : M → Slice U8} {store after : runtime.store.Store M}
    {index inst source status} (effect : ElementContentEffect store index inst source status after)
    (shape : AllocationShape view store) : AllocationShape view after := by
  cases effect with
  | failed error => exact shape
  | appended elements addresses values appended mapped canonical =>
    constructor
    · exact shape.identity
    · exact shape.memories
    · simpa only [TableShape, ReferenceShape] using shape.tables
    · simpa only [GlobalShape, ReferenceShape] using shape.globals
    · intro element member word contained
      simp only [appended, List.mem_append, List.mem_singleton] at member
      rcases member with old | rfl
      · simpa only [ReferenceShape] using shape.elements element old word contained
      · simpa only [ReferenceShape] using canonical word contained
    · exact shape.canonicalTypes
    · exact shape.objectLimit
    · exact shape.signatureAccounting
    · exact shape.signatureLimit
    · exact shape.memoryAccounting
    · exact shape.memoryLimit
    · exact shape.tableAccounting
    · exact shape.tableLimit

theorem DataStageEffect.allocated {M : Type} {view : M → Slice U8} {store after : runtime.store.Store M}
    {index inst} (effect : DataStageEffect store index inst after) (shape : AllocationShape view store) :
    AllocationShape view after := by
  cases effect with
  | unchanged => exact shape
  | appended datas addresses data appended mapped =>
    cases shape
    constructor <;> assumption

end Itasca.Runtime.Store

end

/-! ## PreparationErrorLoops -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

/-- Actual type staging preserves the resource-only error class. This is a
normal-return statement, so it does not assume any unchecked index is valid. -/
theorem type_staging_errors {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (index : Usize)
    (status : core.result.Result Unit runtime.ExecError) (allowed : ErrorAllowed ResourceError status)
    {out} (run : runtime.store.instantiate.Store.prepare_instance_loop3 memory allocator store status index inst = .ok out) :
    ErrorAllowed ResourceError out.2.1 := by
  generalize size : Usize.max - index.val = count
  induction count using Nat.strong_induction_on generalizing store inst index status with
  | h count ih =>
    unfold runtime.store.instantiate.Store.prepare_instance_loop3 at run
    rw [loop] at run
    simp only [runtime.store.instantiate.Store.prepare_instance_loop3.body,
      runtime.compiler.ExecutableModule.env.eq, Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.types, bind_ok] at run
    split at run
    · cases status with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, Result.ok.injEq] at run
        subst out
        exact allowed
      | Ok unit =>
        cases unit
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte, Std.bind_assoc] at run
        obtain ⟨⟨nextStatus, nextStore, nextInst⟩, called, tail⟩ := normal_bind_exists _ _ _ run
        simp only [uncurry_apply_pair, Std.bind_assoc, bind_ok] at tail
        obtain ⟨nextIndex, increment, tail⟩ := normal_bind_exists _ _ _ tail
        have arithmetic := UScalar.add_equiv index 1#usize
        rw [increment] at arithmetic
        have progress : nextIndex.val = index.val + 1 := by simpa using arithmetic.2.1
        have nextMax := nextIndex.hmax
        have smaller : Usize.max - nextIndex.val < count := by scalar_tac
        have nextAllowed := add_type_errors memory allocator law store inst index _ called
        have nextRun : runtime.store.instantiate.Store.prepare_instance_loop3 memory allocator nextStore nextStatus nextIndex nextInst = .ok out := by
          simpa only [uncurry_apply_pair, bind_ok, runtime.store.instantiate.Store.prepare_instance_loop3, runtime.store.instantiate.Store.prepare_instance_loop3.body,
            runtime.compiler.ExecutableModule.env.eq, Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.types, core.result.Result.is_ok] using tail
        exact ih _ smaller nextStore nextInst nextIndex nextStatus nextAllowed nextRun rfl
    · simp only [bind_ok, Result.ok.injEq] at run
      subst out
      exact allowed

theorem function_staging_errors {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (instanceIndex index : Usize)
    (status : core.result.Result Unit runtime.ExecError) (allowed : ErrorAllowed ResourceError status)
    {out} (run : runtime.store.instantiate.Store.prepare_instance_loop4 memory allocator store status index inst instanceIndex = .ok out) :
    ErrorAllowed ResourceError out.2.1 := by
  generalize size : Usize.max - index.val = count
  induction count using Nat.strong_induction_on generalizing store inst index status with
  | h count ih =>
    unfold runtime.store.instantiate.Store.prepare_instance_loop4 at run
    rw [loop] at run
    simp only [runtime.store.instantiate.Store.prepare_instance_loop4.body,
      runtime.compiler.ExecutableModule.env.eq, Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.func_type_indices, bind_ok] at run
    split at run
    · cases status with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, Result.ok.injEq] at run
        subst out
        exact allowed
      | Ok unit =>
        cases unit
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte, Std.bind_assoc] at run
        obtain ⟨⟨nextStatus, nextStore, nextInst⟩, called, tail⟩ := normal_bind_exists _ _ _ run
        simp only [uncurry_apply_pair, Std.bind_assoc, bind_ok] at tail
        obtain ⟨nextIndex, increment, tail⟩ := normal_bind_exists _ _ _ tail
        have arithmetic := UScalar.add_equiv index 1#usize
        rw [increment] at arithmetic
        have progress : nextIndex.val = index.val + 1 := by simpa using arithmetic.2.1
        have nextMax := nextIndex.hmax
        have smaller : Usize.max - nextIndex.val < count := by scalar_tac
        have nextAllowed := add_function_errors memory allocator law store inst instanceIndex index _ called
        have nextRun : runtime.store.instantiate.Store.prepare_instance_loop4 memory allocator nextStore nextStatus nextIndex nextInst instanceIndex = .ok out := by
          simpa only [uncurry_apply_pair, bind_ok, runtime.store.instantiate.Store.prepare_instance_loop4, runtime.store.instantiate.Store.prepare_instance_loop4.body,
            runtime.compiler.ExecutableModule.env.eq, Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.func_type_indices, core.result.Result.is_ok] using tail
        exact ih _ smaller nextStore nextInst nextIndex nextStatus nextAllowed nextRun rfl
    · simp only [bind_ok, Result.ok.injEq] at run
      subst out
      exact allowed
end Itasca.Runtime.Store

end
