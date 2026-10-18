import Exec.Platform.Alloc
import Exec.Generated.Funs

namespace Exec.Platform
open Aeneas Aeneas.Std

/-- Laws for the actual extracted memory dictionary, relative to the bytes used
by the store decoder. No promise of successful allocation or growth is made. -/
structure MemoryLaws {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) : Prop where
  read : ∀ m, ops.bytes m = .ok (view m)
  write : ∀ m, ∃ back, ops.bytes_mut m = .ok (view m, back) ∧
    ∀ bytes, bytes.length = (view m).length → view (back bytes) = bytes
  create : ∀ n, ops.new_zeroed n ⦃ result =>
    ∀ m, result = some m → (view m).val = List.replicate n.val 0#u8 ⦄
  grow : ∀ m n, ops.grow m n ⦃ result =>
    if result.1 then (view m).length ≤ n.val ∧
      (view result.2).val = (view m).val ++
        List.replicate (n.val - (view m).length) 0#u8
    else view result.2 = view m ⦄

/-- Successful growth has exactly the requested length. -/
theorem MemoryLaws.grow_length {M : Type} {ops : runtime.platform.MemoryBuffer M}
    {view : M → Slice U8} (h : MemoryLaws ops view) (m after : M) (n : Usize)
    (hr : ops.grow m n = .ok (true, after)) : (view after).length = n.val := by
  have hp := h.grow m n
  rw [hr] at hp
  simp only [WP.spec_ok, ite_true] at hp
  have hlen := congrArg List.length hp.2
  simp only [List.length_append, List.length_replicate] at hlen
  change (view after).length = (view m).length + (n.val - (view m).length) at hlen
  omega

/-- Allocation produces exactly the requested number of bytes. -/
theorem MemoryLaws.create_length {M : Type} {ops : runtime.platform.MemoryBuffer M}
    {view : M → Slice U8} (h : MemoryLaws ops view) (n : Usize) (m : M)
    (hr : ops.new_zeroed n = .ok (some m)) : (view m).length = n.val := by
  have hp := h.create n
  rw [hr] at hp
  simp only [WP.spec_ok] at hp
  have hlen := congrArg List.length (hp m rfl)
  simpa only [List.length_replicate] using hlen

def vecView (m : runtime.platform.VecMemory) : Slice U8 := m.data.slice

def vecMemoryOps {A : Type} (ops : runtime.platform.Alloc A) :
    runtime.platform.MemoryBuffer runtime.platform.VecMemory where
  new_zeroed := runtime.platform.VecMemory.new_zeroed_with ops
  bytes := runtime.platform.VecMemory.as_bytes
  bytes_mut := runtime.platform.VecMemory.as_bytes_mut
  grow := runtime.platform.VecMemory.grow_with ops

theorem vec_read (m : runtime.platform.VecMemory) :
    runtime.platform.VecMemory.as_bytes m = .ok (vecView m) := by
  simp [runtime.platform.VecMemory.as_bytes, vecView, alloc.vec.Vec.deref,
    alloc.vec.Vec.val]

theorem vec_write (m : runtime.platform.VecMemory) :
    ∃ back, runtime.platform.VecMemory.as_bytes_mut m = .ok (vecView m, back) ∧
      ∀ bytes : Slice U8, bytes.length = (vecView m).length →
        vecView (back bytes) = bytes := by
  refine ⟨fun bytes => ⟨⟨bytes⟩⟩, ?_, ?_⟩
  · simp [runtime.platform.VecMemory.as_bytes_mut, alloc.vec.Vec.deref_mut, vecView, lift]
  · intros; rfl

@[step] theorem vec_grow_loop (before : alloc.vec.Vec U8) (n : Usize)
    (hsize : before.length ≤ n.val) :
    runtime.platform.VecMemory.grow_with_loop before n ⦃ after =>
      after.val = before.val ++ List.replicate (n.val - before.length) 0#u8 ⦄ := by
  unfold runtime.platform.VecMemory.grow_with_loop
  apply loop.spec_decr_nat (fun v => n.val - v.length)
    (fun v => v.length ≤ n.val ∧ v.val ++ List.replicate (n.val - v.length) 0#u8 =
      before.val ++ List.replicate (n.val - before.length) 0#u8)
  · intro v ⟨hlen, hbytes⟩
    unfold runtime.platform.VecMemory.grow_with_loop.body
    dsimp only
    split
    · rename_i hmore
      have hlt : v.length < n.val := by scalar_tac
      have hmax : v.length < Usize.max := by scalar_tac
      step as ⟨after, hafter⟩
      have hlen' : after.length = v.length + 1 := by simp [hafter]
      refine ⟨by omega, ?_, by omega⟩
      rw [hafter, List.append_assoc]
      have heq : n.val - v.length = (n.val - after.length) + 1 := by omega
      rw [heq] at hbytes
      simpa [List.replicate_succ] using hbytes
    · rename_i hstop
      have heq : v.length = n.val := by scalar_tac
      simpa [WP.spec_ok, heq] using hbytes
  · exact ⟨hsize, rfl⟩

@[step] theorem vec_grow {A : Type} (ops : runtime.platform.Alloc A)
    (ha : AllocCorrect ops) (m : runtime.platform.VecMemory) (n : Usize) :
    runtime.platform.VecMemory.grow_with ops m n ⦃ result =>
      if result.1 then (vecView m).length ≤ n.val ∧
        (vecView result.2).val = (vecView m).val ++
          List.replicate (n.val - (vecView m).length) 0#u8
      else vecView result.2 = vecView m ⦄ := by
  unfold runtime.platform.VecMemory.grow_with
  dsimp only
  split
  · simp
  · rename_i hge
    have hsize : m.data.length ≤ n.val := by scalar_tac
    step as ⟨additional, hadd⟩
    obtain ⟨answer, hr⟩ := ha.reserve_eq m.data additional
    rw [hr]
    cases answer with
    | false => simp
    | true =>
      obtain ⟨after, hrun, hafter⟩ := WP.spec_imp_exists (vec_grow_loop m.data n hsize)
      simp [hrun, vecView]
      exact ⟨hsize, hafter⟩

@[step] theorem vec_create {A : Type} (ops : runtime.platform.Alloc A)
    (ha : AllocCorrect ops) (n : Usize) :
    runtime.platform.VecMemory.new_zeroed_with ops n ⦃ result =>
      ∀ m, result = some m → (vecView m).val = List.replicate n.val 0#u8 ⦄ := by
  unfold runtime.platform.VecMemory.new_zeroed_with
  step with vec_grow ops ha ⟨alloc.vec.Vec.new U8⟩ n as ⟨answer, memory, hresult⟩
  cases answer <;> simp_all [vecView, alloc.vec.Vec.new, alloc.vec.Vec.from]

/-- The reviewed native implementation delegates to these extracted helpers. -/
theorem vecMemory_laws {A : Type} (ops : runtime.platform.Alloc A)
    (ha : AllocCorrect ops) : MemoryLaws (vecMemoryOps ops) vecView where
  read := vec_read
  write := vec_write
  create := vec_create ops ha
  grow := vec_grow ops ha

end Exec.Platform
