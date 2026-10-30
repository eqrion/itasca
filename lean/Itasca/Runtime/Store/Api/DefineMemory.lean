import Itasca.Runtime.Store.Api.Define

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

def LimitsFit (limits : Itasca.wasm_types.Limits) (maximum : U32) : Prop :=
  limits.min.val ≤ maximum.val ∧
  match limits.max with
  | none => True
  | some high => limits.min.val ≤ high.val ∧ high.val ≤ maximum.val

instance (limits : Itasca.wasm_types.Limits) (maximum : U32) : Decidable (LimitsFit limits maximum) := by
  unfold LimitsFit
  cases limits.max <;> infer_instance

@[step] theorem check_limits_spec (limits : Itasca.wasm_types.Limits) (maximum : U32) :
    runtime.store.check_limits limits maximum ⦃ result => result =
      if LimitsFit limits maximum then .Ok () else .Err .BadArguments ⦄ := by
  rcases limits with ⟨minimum, maximumOption⟩
  cases maximumOption <;> simp [runtime.store.check_limits, LimitsFit, core.option.Option.unwrap_or, lift]
  all_goals repeat' split
  all_goals simp_all
  all_goals scalar_tac

/-- Defining a memory retains exactly the supplied buffer when its view has the
requested initial size; every rejected definition leaves the store unchanged. -/
theorem define_memory_effect {M A : Type} (ops : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (ha : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws ops view)
    (s : runtime.store.Store M) (ty : Itasca.wasm_types.MemType) (buffer : M)
    (hbound : objectCount s ≤ Usize.max) :
    runtime.store.Store.define_memory_with ops allocator s ty buffer ⦃ result =>
      (∃ error, result = (.Err error, s)) ∨
      ∃ memories : alloc.vec.Vec (runtime.store.MemInst M), ∃ count : Usize,
        memories.val = s.memories.val ++ [{buf := buffer, maximum := ty.limits.max}] ∧
        LimitsFit ty.limits 65536#u32 ∧
        (view buffer).length = ty.limits.min.val * 65536 ∧
        objectCount s < s.limits.max_objects.val ∧
        count.val = s.memory_bytes.val + (view buffer).length ∧
        count.val ≤ s.limits.max_memory_bytes.val ∧
        result = (.Ok ⟨s.id, alloc.vec.Vec.len s.memories⟩,
          {s with memories, memory_bytes := count}) ⦄ := by
  unfold runtime.store.Store.define_memory_with
  step with room_spec ops s hbound as ⟨room, hroom⟩
  rw [hroom]
  split
  · rename_i hroom
    simp [core.result.Result.Insts.CoreOpsTry.branch]
    step with check_limits_spec ty.limits 65536#u32 as ⟨limits, hlimits⟩
    rw [hlimits]
    by_cases hfit : LimitsFit ty.limits 65536#u32
    · simp only [if_pos hfit]
      simp [core.result.Result.Insts.CoreOpsTry.branch, lift]
      step as ⟨size, hsize⟩
      rw [laws.read]
      simp [lift]
      by_cases hlength : (view buffer).length = size.val
      · simp only [hlength, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        have hbytes : (view buffer).length = ty.limits.min.val * 65536 := by scalar_tac
        step with within_spec s.memory_bytes (Slice.len (view buffer)) s.limits.max_memory_bytes as ⟨fits, hfits⟩
        rw [hfits]
        split
        · rename_i htotal
          have htotal' : s.memory_bytes.val + (view buffer).length ≤ s.limits.max_memory_bytes.val := by simpa using htotal
          obtain ⟨answer, hr⟩ := reserve_wrapper_eq allocator ha s.memories 1#usize
          rw [hr]
          cases answer
          · simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          · simp
            have hmax : s.memories.length < Usize.max := by unfold objectCount at hroom; scalar_tac
            step as ⟨memories, hmemories⟩
            have hsizeBound : size.val ≤ Usize.max := by scalar_tac
            have hcast := cast_usize_exact size hsizeBound
            step as ⟨count, hcount⟩
            right
            exact ⟨memories, hmemories, hfit, by scalar_tac, hroom, count,
              by scalar_tac, by scalar_tac, rfl⟩
        · simp
      · simp [hlength]
    · simp [hfit, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  · simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

end Itasca.Runtime.Store
