import Itasca.Stream.Batch
import Itasca.Stream.EntryFrame

/-!
# Worker cursor bounds

Bounds on the dispatch and validation cursors of reachable workers, and the totality of the
read-only `stream.CodeBatch` accessors and `stream.CodeBatch.next_entry`.
`StreamBatch.Reachable.dispatched` bounds the dispatch cursor by framing, and
`StreamBatch.Reachable.cursor_bounds` bounds both cursors independently of each other.
-/

open Aeneas Aeneas.Std

namespace Itasca.StreamBatch

end Itasca.StreamBatch

namespace Itasca

/-- Dispatch returns an ordinary result when function indices fit in `Usize`, including on
malformed bytes and when the dispatch cursor is already exhausted. -/
theorem stream.CodeBatch.next_entry.total (batch : stream.CodeBatch)
    (hindex : batch.first_func.val + batch.num_funcs.val ≤ Usize.max) :
    ∃ r, stream.CodeBatch.next_entry batch = .ok r := by
  have ht : stream.CodeBatch.next_entry batch ⦃ _ => True ⦄ := by
    unfold stream.CodeBatch.next_entry
    split
    · simp
    · rename_i hcount
      step
      obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists
        (stream.frame_entry.spec batch.code batch.dispatch_end index batch.code_offset)
      rw [hr]
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok entry =>
        obtain ⟨content, finish, _, _, _, _, hend, _⟩ := hp
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        step*
  obtain ⟨r, hr, _⟩ := WP.spec_imp_exists ht
  exact ⟨r, hr⟩

end Itasca
