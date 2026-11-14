import Itasca.Runtime.Platform.Laws

/-! The extracted vector memory implementation satisfies the platform memory
contract. The dictionary follows the native `MemoryBuffer for VecMemory` impl
by inspection, with its allocator made explicit; native allocation itself is
covered by the supplied `AllocCorrect` premise. -/

namespace Itasca.Runtime.Platform
open Aeneas Aeneas.Std

/-- Allocator-parametric version of the native vector-memory dictionary. -/
def vecMemory {A : Type} (allocator : runtime.platform.Alloc A) :
    runtime.platform.MemoryBuffer runtime.platform.VecMemory where
  new_zeroed n := runtime.platform.VecMemory.new_zeroed_with allocator n
  bytes m := runtime.platform.VecMemory.as_bytes m
  bytes_mut m := runtime.platform.VecMemory.as_bytes_mut m
  grow m n := runtime.platform.VecMemory.grow_with allocator m n

/-- The visible bytes are exactly the stored vector's slice. -/
def vecMemoryView (memory : runtime.platform.VecMemory) : Slice U8 := memory.data.slice

@[step] theorem vec_memory_grow_loop (before : alloc.vec.Vec U8) (size : Usize)
    (bounded : before.length ≤ size.val) :
    runtime.platform.VecMemory.grow_with_loop before size ⦃ after =>
      after.val = before.val ++ List.replicate (size.val - before.length) 0#u8 ⦄ := by
  unfold runtime.platform.VecMemory.grow_with_loop
  apply loop.spec_decr_nat (fun items => size.val - items.length)
    (fun items => items.length ≤ size.val ∧
      items.val ++ List.replicate (size.val - items.length) 0#u8 =
        before.val ++ List.replicate (size.val - before.length) 0#u8)
  · intro items invariant
    obtain ⟨lengthBound, bytes⟩ := invariant
    unfold runtime.platform.VecMemory.grow_with_loop.body
    by_cases more : items.len < size
    · simp only [if_pos more]
      have room : items.length < Usize.max := by scalar_tac
      step as ⟨after, appended⟩
      have lengthAfter : after.length = items.length + 1 := by
        simp only [alloc.vec.Vec.length, appended, List.length_append, List.length_cons, List.length_nil, Nat.add_zero]
      refine ⟨?_, ?_, ?_⟩
      · scalar_tac
      · rw [appended, List.append_assoc]
        have remaining : size.val - items.length = (size.val - after.length) + 1 := by scalar_tac
        rw [remaining] at bytes
        simpa only [List.replicate_succ, List.singleton_append] using bytes
      · scalar_tac
    · simp only [if_neg more, WP.spec_ok]
      have full : items.length = size.val := by scalar_tac
      simpa only [full, Nat.sub_self, List.replicate_zero, List.append_nil] using bytes
  · exact ⟨bounded, rfl⟩

@[step] theorem vec_memory_grow {A : Type} (allocator : runtime.platform.Alloc A)
    (law : AllocCorrect allocator) (memory : runtime.platform.VecMemory) (size : Usize) :
    runtime.platform.VecMemory.grow_with allocator memory size ⦃ (accepted, after) =>
      if accepted then memory.data.length ≤ size.val ∧
        after.data.val = memory.data.val ++ List.replicate (size.val - memory.data.length) 0#u8
      else after = memory ⦄ := by
  unfold runtime.platform.VecMemory.grow_with
  by_cases smaller : size < memory.data.len
  · simp only [if_pos smaller, WP.spec_ok, uncurry_apply_pair, Bool.false_eq_true, if_false]
  · simp only [if_neg smaller]
    have bounded : memory.data.length ≤ size.val := by scalar_tac
    step as ⟨additional, difference⟩
    obtain ⟨accepted, reserved⟩ := law.reserve_eq memory.data additional
    cases accepted with
    | false => simp only [reserved, bind_ok, Bool.false_eq_true, if_false, WP.spec_ok, uncurry_apply_pair]
    | true =>
      simp only [reserved, bind_ok, ↓reduceIte]
      change WP.spec (do
        let vector ← runtime.platform.VecMemory.grow_with_loop memory.data size
        Result.ok (true, runtime.platform.VecMemory.mk vector)) _
      step with vec_memory_grow_loop memory.data size bounded as ⟨after, appended⟩
      exact ⟨bounded, appended⟩

/-- Correct allocators make the actual extracted vector-memory operations obey
all four memory laws, without assuming allocation requests are granted. -/
theorem vecMemory_laws {A : Type} (allocator : runtime.platform.Alloc A)
    (law : AllocCorrect allocator) : MemoryLaws (vecMemory allocator) vecMemoryView := by
  constructor
  · intro memory
    simp only [vecMemory, runtime.platform.VecMemory.as_bytes, vecMemoryView, alloc.vec.Vec.deref,
      alloc.vec.Vec.val, Slice.val_from]
  · intro memory
    refine ⟨fun bytes => ⟨{slice := bytes}⟩, ?_, ?_⟩
    · simp only [vecMemory, runtime.platform.VecMemory.as_bytes_mut, alloc.vec.Vec.deref_mut,
        lift, bind_ok, vecMemoryView]
      rfl
    · intro bytes sameLength
      rfl
  · intro size
    unfold vecMemory runtime.platform.VecMemory.new_zeroed_with
    step with vec_memory_grow allocator law ⟨alloc.vec.Vec.new U8⟩ size as ⟨accepted, memory, growth⟩
    cases accepted with
    | false => simp only [Bool.false_eq_true, if_false, WP.spec_ok, reduceCtorEq, false_implies, implies_true]
    | true =>
      simp only [Bool.true_eq, ite_true, WP.spec_ok]
      intro actual equal
      cases equal
      change memory.data.val = List.replicate size.val 0#u8
      simpa only [alloc.vec.Vec.new, alloc.vec.Vec.from_val, alloc.vec.Vec.length,
        List.length_nil, Nat.sub_zero, List.nil_append] using growth.2
  · intro memory size
    apply WP.spec_mono (vec_memory_grow allocator law memory size)
    rintro ⟨accepted, after⟩ growth
    cases accepted with
    | false =>
      change after = memory at growth
      subst after
      rfl
    | true =>
      change memory.data.length ≤ size.val ∧ after.data.val = memory.data.val ++ List.replicate (size.val - memory.data.length) 0#u8 at growth
      simpa only [vecMemory, vecMemoryView, alloc.vec.Vec.length, alloc.vec.Vec.val, Slice.length, ↓reduceIte] using growth

end Itasca.Runtime.Platform
