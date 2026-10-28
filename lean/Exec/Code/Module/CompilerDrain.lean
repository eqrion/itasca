import Exec.Code.Module.CompilerProvenance
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std
open Itasca Itasca.ResultFacts

/-- The final drain only removes completed workers. All captured code and the
validated tail remain exactly as delivered before retirement. -/
theorem compiler_drain_frame {A : Type} (allocator : runtime.platform.Alloc A)
    (id : U64) (before after : runtime.compiler.CompileScheduler A)
    (pending remaining : alloc.vec.Vec Usize)
    (accepted : stream.retire_all_code_batches
      (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor allocator)
      id before pending = .ok (.Ok (), after, remaining)) :
    after = {before with completed := after.completed} := by
  generalize measure : pending.val.length = n
  induction n using Nat.strong_induction_on generalizing before pending with
  | h n ih =>
    unfold stream.retire_all_code_batches stream.retire_all_code_batches_loop at accepted
    rw [loop] at accepted
    simp only [stream.retire_all_code_batches_loop.body, alloc.vec.Vec.is_empty, bind_ok] at accepted
    by_cases empty : pending.val = []
    · simp [empty] at accepted
      obtain ⟨rfl, rfl⟩ := accepted
      rfl
    · have nonempty : pending.val.isEmpty = false := by simpa using empty
      simp only [nonempty, Bool.false_eq_true, ↓reduceIte, Std.bind_assoc] at accepted
      obtain ⟨⟨result, middle, rest⟩, retired, tail⟩ := bind_ok_inv _ _ _ accepted
      cases result with
      | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at tail
      | Ok unit =>
        cases unit
        obtain ⟨batch, polled, _, _, perm⟩ := stream.retire_code_batch.accepted
          (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor allocator)
          id before middle pending rest retired
        have length := perm.length_eq
        simp only [List.length_cons] at length
        have smaller : rest.val.length < n := by omega
        have tail' : stream.retire_all_code_batches
            (runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor allocator)
            id middle rest = .ok (.Ok (), after, remaining) := by
          simpa [stream.retire_all_code_batches, stream.retire_all_code_batches_loop,
            stream.retire_all_code_batches_loop.body, alloc.vec.Vec.is_empty,
            core.result.Result.Insts.CoreOpsTry.branch] using tail
        have afterEq := ih rest.val.length smaller middle rest tail' rfl
        have middleEq := (compiler_poll_accepted allocator before middle batch polled).2
        rw [afterEq, middleEq]
end Itasca.Runtime.Code
