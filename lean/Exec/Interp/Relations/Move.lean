import Exec.Interp.Relations.Regions

namespace Exec.Interp
open Aeneas Aeneas.Std

/-- The actual scalar/vector transfer emitted for a local copies exactly the
value's width and preserves every non-slot execution field, store and platform. -/
theorem dispatch_move_effect {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index inst function base : Usize) (ty : valtype) (dst src : U32)
    (source : base.val + src.val + Code.width ty ≤ exec.slots.length)
    (destination : base.val + dst.val + Code.width ty ≤ exec.slots.length) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform index inst function base
      (Code.move ty dst src) ⦃ out =>
        out.1 = .Ok () ∧ SlotsEffect exec out.2.1
          (copyWords exec.slots.val (base.val + dst.val) (base.val + src.val) (Code.width ty)) ∧
        out.2.2.1 = store ∧ out.2.2.2 = platform ⦄ := by
  by_cases vector : Code.width ty = 2
  · have hs : base.val + src.val + 2 ≤ exec.slots.length := by omega
    have hd : base.val + dst.val + 2 ≤ exec.slots.length := by omega
    simp only [Code.move, if_pos vector, runtime.interp.dispatch]
    obtain ⟨out, result, success, slots⟩ := WP.spec_imp_exists
      (copy2_effect exec base dst src hs hd)
    rw [result, bind_ok]
    rcases out with ⟨answer, next⟩
    with_unfolding_all apply WP.spec.ret
    exact ⟨success, by simpa only [vector] using slots, rfl, rfl⟩
  · have scalar : Code.width ty = 1 := by cases ty <;> simp_all [Code.width]
    have hs : base.val + src.val < exec.slots.length := by omega
    have hd : base.val + dst.val < exec.slots.length := by omega
    simp only [Code.move, if_neg vector, runtime.interp.dispatch]
    obtain ⟨out, result, success, slots⟩ := WP.spec_imp_exists
      (copy_effect exec base dst src hs hd)
    rw [result, bind_ok]
    rcases out with ⟨answer, next⟩
    with_unfolding_all apply WP.spec.ret
    exact ⟨success, by simpa only [scalar, copyWords] using slots, rfl, rfl⟩

end Exec.Interp
