import Itasca.Stream.Retirement

namespace Itasca.StreamRetirement
open Aeneas Aeneas.Std

/-- Returning polls are required only at scheduler states satisfying the
internal invariant; successful polls preserve that invariant. -/
def PollTotalOn {V : Type} (visitor : stream.StreamingVisitor V) (invariant : V → Prop) : Prop :=
  ∀ state, invariant state → visitor.poll_code_batch state ⦃ out =>
    ∀ batch, out.1 = .Ok batch → invariant out.2 ⦄

end Itasca.StreamRetirement
namespace Itasca
open Aeneas Aeneas.Std

theorem stream.retire_code_batch.spec_on {V : Type} (visitor : stream.StreamingVisitor V)
    (invariant : V → Prop) (moduleId : U64) (state : V) (pending : alloc.vec.Vec Usize)
    (poll : StreamRetirement.PollTotalOn visitor invariant) (held : invariant state) :
    stream.retire_code_batch visitor moduleId state pending ⦃ out =>
      StreamRetirement.Retired visitor moduleId state pending out ∧
      (out.1 = .Ok () → invariant out.2.1) ⦄ := by
  obtain ⟨reply, returned, preserved⟩ := WP.spec_imp_exists (poll state held)
  apply WP.spec_mono (stream.retire_code_batch.spec visitor moduleId state pending ⟨reply, returned⟩)
  rintro ⟨status,after,remaining⟩ retired
  refine ⟨retired, ?_⟩
  intro success
  dsimp only at success ⊢
  subst status
  obtain ⟨batch, found, _, _, _⟩ := retired
  have same := Result.ok_injective (returned.symm.trans found)
  subst reply
  exact preserved batch rfl

/-- Draining needs a returning callback only on reachable invariant states. -/
theorem stream.retire_all_code_batches.spec_on {V : Type} (visitor : stream.StreamingVisitor V)
    (invariant : V → Prop) (moduleId : U64) (state : V) (pending : alloc.vec.Vec Usize)
    (poll : StreamRetirement.PollTotalOn visitor invariant) (held : invariant state) :
    stream.retire_all_code_batches visitor moduleId state pending ⦃ out =>
      out.1 = .Ok () → out.2.2.val = [] ∧ invariant out.2.1 ⦄ := by
  unfold stream.retire_all_code_batches stream.retire_all_code_batches_loop
  apply loop.spec_decr_nat (fun s => s.2.length) (fun s => invariant s.1)
  · rintro ⟨state, pending⟩ held
    simp only [stream.retire_all_code_batches_loop.body, alloc.vec.Vec.is_empty, bind_ok]
    by_cases empty : pending.val = []
    · simp [empty,held]
    · have nonempty : pending.val.isEmpty = false := by simpa using empty
      simp only [nonempty, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨⟨status,after,remaining⟩,returned,retired,preserved⟩ := WP.spec_imp_exists
        (stream.retire_code_batch.spec_on visitor invariant moduleId state pending poll held)
      rw [returned]
      cases status with
      | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok result =>
        cases result
        simp [core.result.Result.Insts.CoreOpsTry.branch]
        obtain ⟨batch, _, _, _, permutation⟩ := retired
        have length := permutation.length_eq
        simp only [List.length_cons] at length
        exact ⟨preserved rfl,by omega⟩
  · exact held
end Itasca
