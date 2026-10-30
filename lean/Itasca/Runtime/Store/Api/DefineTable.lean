import Itasca.Runtime.Store.Api.DefineMemory

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

@[step] theorem define_table_loop (count : U32) (before : alloc.vec.Vec U64) (position : U32)
    (hposition : position.val = before.length) (hbound : position.val ≤ count.val) :
    runtime.store.Store.define_table_with_loop count before position ⦃ after =>
      after.val = before.val ++ List.replicate (count.val - before.length) 0#u64 ⦄ := by
  unfold runtime.store.Store.define_table_with_loop
  apply loop.spec_decr_nat (fun pair => count.val - pair.2.val)
    (fun pair => pair.2.val = pair.1.length ∧ pair.2.val ≤ count.val ∧
      pair.1.val ++ List.replicate (count.val - pair.1.length) 0#u64 =
        before.val ++ List.replicate (count.val - before.length) 0#u64)
  · intro pair hinv
    rcases pair with ⟨items, pos⟩
    rcases hinv with ⟨hpos, hlen, hbytes⟩
    unfold runtime.store.Store.define_table_with_loop.body
    dsimp only at hpos hlen hbytes ⊢
    split
    · rename_i hmore
      have hlt : items.length < count.val := by scalar_tac
      have hpush : items.length < Usize.max := by scalar_tac
      step as ⟨after, hafter⟩
      step as ⟨next, hnext⟩
      have hlen' : after.length = items.length + 1 := by simp [hafter]
      simp only [alloc.vec.Vec.length] at *
      refine ⟨by omega, by omega, ?_, by omega⟩
      rw [hafter, List.append_assoc]
      have heq : count.val - items.val.length = (count.val - after.val.length) + 1 := by omega
      rw [heq] at hbytes
      simpa [List.replicate_succ, hlen'] using hbytes
    · rename_i hstop
      have heq : items.length = count.val := by scalar_tac
      simpa [WP.spec_ok, heq] using hbytes
  · exact ⟨hposition, hbound, rfl⟩

/-- A defined table contains exactly its requested number of null references.
All validation, resource, and allocator failures retain the original store. -/
theorem define_table_effect {M A : Type} (ops : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (ha : Platform.AllocCorrect allocator)
    (s : runtime.store.Store M) (ty : Itasca.wasm_types.TableType)
    (hbound : objectCount s ≤ Usize.max) :
    runtime.store.Store.define_table_with ops allocator s ty ⦃ result =>
      (∃ error, result = (.Err error, s)) ∨
      ∃ tables : alloc.vec.Vec runtime.store.TableInst, ∃ elements : alloc.vec.Vec U64,
      ∃ count : Usize,
        elements.val = List.replicate ty.limits.min.val 0#u64 ∧
        tables.val = s.tables.val ++ [{elements, ty := ty.elem, maximum := ty.limits.max}] ∧
        LimitsFit ty.limits core.num.U32.MAX ∧
        objectCount s < s.limits.max_objects.val ∧
        count.val = s.table_elements.val + ty.limits.min.val ∧
        count.val ≤ s.limits.max_table_elements.val ∧
        result = (.Ok ⟨s.id, alloc.vec.Vec.len s.tables⟩,
          {s with tables, table_elements := count}) ⦄ := by
  unfold runtime.store.Store.define_table_with
  step with room_spec ops s hbound as ⟨room, hroom⟩
  rw [hroom]
  split
  · rename_i hroom
    simp [core.result.Result.Insts.CoreOpsTry.branch]
    step with check_limits_spec ty.limits core.num.U32.MAX as ⟨limits, hlimits⟩
    rw [hlimits]
    by_cases hfit : LimitsFit ty.limits core.num.U32.MAX
    · simp [hfit, core.result.Result.Insts.CoreOpsTry.branch, lift]
      step with within_spec s.table_elements (UScalar.cast .Usize ty.limits.min)
        s.limits.max_table_elements as ⟨fits, hfits⟩
      rw [hfits]
      split
      · rename_i htotal
        have htotal' : s.table_elements.val + ty.limits.min.val ≤ s.limits.max_table_elements.val := by scalar_tac
        obtain ⟨answer, hr⟩ := reserve_wrapper_eq allocator ha (alloc.vec.Vec.new U64) (UScalar.cast .Usize ty.limits.min)
        rw [hr]
        cases answer
        · simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        · simp
          step with define_table_loop ty.limits.min (alloc.vec.Vec.new U64) 0#u32 (by simp) (by scalar_tac) as ⟨elements, helements⟩
          simp [alloc.vec.Vec.new] at helements
          obtain ⟨answer, hr⟩ := reserve_wrapper_eq allocator ha s.tables 1#usize
          rw [hr]
          cases answer
          · simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          · simp
            have hmax : s.tables.length < Usize.max := by unfold objectCount at hroom; scalar_tac
            step as ⟨tables, htables⟩
            step as ⟨count, hcount⟩
            right
            exact ⟨tables, elements, helements, htables, hroom, count,
              by scalar_tac, by scalar_tac, rfl⟩
      · simp
    · simp [hfit, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  · simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

end Itasca.Runtime.Store
