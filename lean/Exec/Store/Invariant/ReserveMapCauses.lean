import Exec.Store.Invariant.InvalidWrite
import Exec.Store.Preparation.AllocationCauses

namespace Exec.Store
open Aeneas Aeneas.Std

/-- Reserving a provisional instance's element map preserves the exact vector,
including the mutable-index writeback, on either allocator decision. -/
theorem reserve_element_map_cause {A : Type} (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (instances : alloc.vec.Vec runtime.store.ModuleInst)
    (index additional : Usize) (bound : index.val < instances.val.length) :
    (do
      let (inst, back) ← alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice runtime.store.ModuleInst) instances index
      let (status, values) ← runtime.reserve allocator inst.elems additional
      pure (status, back {inst with elems := values}))
      ⦃ out => out.2 = instances ∧ ∀ error, out.1 = .Err error →
        error = .Exhausted .Allocation ∧ ∃ inst,
          instances.val[index.val]? = some inst ∧
          allocator.reserve inst.elems additional = .ok (false,inst.elems) ⦄ := by
  step as ⟨inst, back, found, writeback⟩
  have eta : {inst with elems := inst.elems} = inst := by cases inst; rfl
  have same : back {inst with elems := inst.elems} = instances := by
    rw [eta, writeback, found]
    exact vec_set_current instances index bound
  obtain ⟨answer, reserved, refusal⟩ := reserve_with_cause allocator law inst.elems additional
  rw [reserved]
  cases answer
  · simp only [Bool.false_eq_true, ↓reduceIte, bind_ok, WP.spec_ok]
    refine ⟨same, ?_⟩
    intro error rejected
    cases rejected
    refine ⟨rfl, inst, ?_, refusal⟩
    rw [found]
    exact List.getElem?_eq_getElem bound
  · simp only [↓reduceIte, bind_ok, WP.spec_ok]
    exact ⟨same, by simp⟩

/-- The same exact preservation applies to the passive-data index map. -/
theorem reserve_data_map_cause {A : Type} (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (instances : alloc.vec.Vec runtime.store.ModuleInst)
    (index additional : Usize) (bound : index.val < instances.val.length) :
    (do
      let (inst, back) ← alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice runtime.store.ModuleInst) instances index
      let (status, values) ← runtime.reserve allocator inst.datas additional
      pure (status, back {inst with datas := values}))
      ⦃ out => out.2 = instances ∧ ∀ error, out.1 = .Err error →
        error = .Exhausted .Allocation ∧ ∃ inst,
          instances.val[index.val]? = some inst ∧
          allocator.reserve inst.datas additional = .ok (false,inst.datas) ⦄ := by
  step as ⟨inst, back, found, writeback⟩
  have eta : {inst with datas := inst.datas} = inst := by cases inst; rfl
  have same : back {inst with datas := inst.datas} = instances := by
    rw [eta, writeback, found]
    exact vec_set_current instances index bound
  obtain ⟨answer, reserved, refusal⟩ := reserve_with_cause allocator law inst.datas additional
  rw [reserved]
  cases answer
  · simp only [Bool.false_eq_true, ↓reduceIte, bind_ok, WP.spec_ok]
    refine ⟨same, ?_⟩
    intro error rejected
    cases rejected
    refine ⟨rfl, inst, ?_, refusal⟩
    rw [found]
    exact List.getElem?_eq_getElem bound
  · simp only [↓reduceIte, bind_ok, WP.spec_ok]
    exact ⟨same, by simp⟩

end Exec.Store
