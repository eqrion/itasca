import Exec.Interp.Relations.Execute
import Exec.Platform.Alloc

/-! Slot storage growth returns normally under the allocator law. Its only
rejections are the requested value limit and an actual allocator rejection. -/
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

@[step] theorem ensure_loop_effect (before : alloc.vec.Vec U64) (bound : Usize)
    (fits : before.length ≤ bound.val) :
    runtime.interp.Execution.ensure_loop before bound ⦃ after =>
      after.val = before.val ++ List.replicate (bound.val - before.length) 0#u64 ⦄ := by
  unfold runtime.interp.Execution.ensure_loop
  apply loop.spec_decr_nat (fun current => bound.val - current.length)
    (fun current => current.length ≤ bound.val ∧
      current.val ++ List.replicate (bound.val - current.length) 0#u64 =
        before.val ++ List.replicate (bound.val - before.length) 0#u64)
  · intro current hinv
    obtain ⟨hlen, hwords⟩ := hinv
    unfold runtime.interp.Execution.ensure_loop.body
    dsimp only
    split
    · have hlt : current.length < bound.val := by scalar_tac
      have hpush : current.length < Usize.max := by scalar_tac
      step as ⟨after, happend⟩
      have hlength : after.length = current.length + 1 := by simp [happend]
      refine ⟨?_, ?_, ?_⟩
      · omega
      · rw [happend, List.append_assoc]
        have hremaining : bound.val - current.length = (bound.val - after.length) + 1 := by omega
        rw [hremaining] at hwords
        simpa [List.replicate_succ] using hwords
      · omega
    · have heq : current.length = bound.val := by scalar_tac
      simpa [heq] using hwords
  · exact ⟨fits, rfl⟩

def EnsureEffect {A : Type} (allocator : runtime.platform.Alloc A)
    (before : runtime.interp.Execution) (bound limit : Usize)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution) : Prop :=
  match out.1 with
  | .Ok _ => bound.val ≤ limit.val ∧ SlotsEffect before out.2
      (before.slots.val ++ List.replicate (bound.val - before.slots.length) 0#u64)
  | .Err (.Exhausted .Values) => limit.val < bound.val ∧ out.2 = before
  | .Err (.Exhausted .Allocation) =>
      bound.val ≤ limit.val ∧ before.slots.length < bound.val ∧ out.2 = before ∧
      ∃ n : Usize, n.val = bound.val - before.slots.length ∧
        allocator.reserve before.slots n = .ok (false, before.slots)
  | .Err _ => False

@[step] theorem ensure_effect {A : Type} (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (before : runtime.interp.Execution)
    (bound limit : Usize) :
    runtime.interp.Execution.ensure allocator before bound limit
      ⦃ out => EnsureEffect allocator before bound limit out ⦄ := by
  unfold runtime.interp.Execution.ensure
  split
  · simp only [WP.spec_ok, EnsureEffect]
    exact ⟨by scalar_tac, trivial⟩
  · rename_i within
    dsimp only
    split
    · rename_i grow
      step as ⟨n, hn⟩
      obtain ⟨answer, hreserve⟩ := law.reserve_eq before.slots n
      unfold runtime.reserve
      rw [hreserve, bind_ok]
      cases answer with
      | false =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          EnsureEffect]
        exact ⟨by scalar_tac, by scalar_tac, n, hn, hreserve⟩
      | true =>
        simp [core.result.Result.Insts.CoreOpsTry.branch]
        step with ensure_loop_effect before.slots bound (by scalar_tac) as ⟨after, hafter⟩
        exact ⟨by scalar_tac, hafter, rfl⟩
    · have hbound : bound.val ≤ before.slots.length := by scalar_tac
      simp [EnsureEffect, SlotsEffect, Nat.sub_eq_zero_of_le hbound]
      scalar_tac

end Itasca.Runtime.Interp
