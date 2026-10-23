import Itasca.Stream.BatchComplete
import Itasca.Stream.Scheduler
import Itasca.Contracts

/-!
# Accepting schedulers

Consequences of `StreamAcceptingScheduler.Accepts`, the scheduler policy under which completeness
holds, and of `StreamAcceptingScheduler.Valid`, the independent premises of an issued batch. Both
are defined in `Itasca/Contracts`. `StreamAcceptingScheduler.retire_complete` and
`StreamAcceptingScheduler.drain_complete` show that valid queued work retires and drains
successfully.
-/

open Aeneas Aeneas.Std

namespace Itasca.StreamAcceptingScheduler

variable {validationProfile : ValidationProfile}

/-- Running `validate_all` on the seed of a `Valid` batch gives a worker with the issued identity
that `stream.CodeBatch.finish` accepts. -/
theorem Valid.finished {issued : StreamBatch.Issued} (h : Valid issued validationProfile)
    {after : stream.CodeBatch} (hr : stream.CodeBatch.validate_all issued.seed = .ok after) :
    StreamBatch.Identity issued after ∧ stream.CodeBatch.finish after = .ok (.Ok ()) := by
  obtain ⟨entries, hn, ht, hb⟩ := h.entries
  obtain ⟨result, hrun, hreachable, hfinish⟩ := stream.CodeBatch.validate_all.complete_at_seed
    issued entries h.bounded hn ht h.profile h.limits h.entry_bounds hb h.validation_profile
  have he : result = after := by simpa using hrun.symm.trans hr
  subst result
  exact ⟨hreachable.validation.1, hfinish⟩

end Itasca.StreamAcceptingScheduler

namespace Itasca

/-- A polled batch of the right module, whose ID is pending and whose finish check succeeds, is
retired successfully by `stream.retire_code_batch`. -/
theorem stream.retire_code_batch.complete {V : Type} (visitor : stream.StreamingVisitor V)
    (id : U64) (v v' : V) (pending : alloc.vec.Vec Usize) (batch : stream.CodeBatch)
    (hpoll : visitor.poll_code_batch v = .ok (.Ok batch, v'))
    (hmodule : batch.module_id = id) (hmem : batch.batch_id ∈ pending.val)
    (hfinish : stream.CodeBatch.finish batch = .ok (.Ok ())) :
    ∃ remaining, stream.retire_code_batch visitor id v pending = .ok (.Ok (), v', remaining) ∧
      (batch.batch_id :: remaining.val).Perm pending.val := by
  obtain ⟨found, hfind, hf⟩ := WP.spec_imp_exists
    (stream.retire_code_batch_loop.spec pending batch.batch_id 0#usize (by simp))
  have hlt : found.val < pending.length := by
    by_contra hnot
    have hend : found.val = pending.length := by have := hf.2.1; omega
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hmem
    exact hf.2.2.1 i hi (by simp) (by simpa [hend] using hi) he
  have hmatch := hf.2.2.2 hlt
  have hne : found ≠ alloc.vec.Vec.len pending := by scalar_tac
  have hs : stream.retire_code_batch visitor id v pending ⦃ r =>
      r.1 = .Ok () ∧ r.2.1 = v' ∧ (batch.batch_id :: r.2.2.val).Perm pending.val ⦄ := by
    simp [stream.retire_code_batch, hpoll, core.result.Result.Insts.CoreOpsTry.branch,
      hmodule, hfind, hne]
    step
    step
    step
    simp only [alloc.vec.Vec.pop, bind_ok, hfinish]
    refine ⟨rfl, rfl, ?_⟩
    have hlast : last.val = pending.val.length - 1 := by scalar_tac
    simpa only [index_mut_back_post, i3_post, hlast, alloc.vec.Vec.set_val_eq,
      alloc.vec.Vec.from_val, hmatch] using
      (StreamRetirement.swap_pop_perm pending.val found.val hlt)
  obtain ⟨⟨r, state, remaining⟩, hr, hsuccess, hstate, hperm⟩ := WP.spec_imp_exists hs
  dsimp only at hsuccess hstate hperm
  subst r
  subst state
  exact ⟨remaining, hr, hperm⟩

end Itasca

namespace Itasca.StreamAcceptingScheduler

variable {validationProfile : ValidationProfile}

/-- Valid pending work retires in any scheduler-selected order. Successful finish follows from the
actual worker execution on independently typed encodings. -/
theorem retire_complete {V : Type} (visitor : stream.StreamingVisitor V)
    (config : stream.Config) (Queued : U64 → List StreamBatch.Issued → V → Prop)
    (hp : Accepts visitor config Queued validationProfile) (id : U64)
    (queue : List StreamBatch.Issued) (v : V) (pending : alloc.vec.Vec Usize)
    (hv : Queued id queue v) (hvalid : ValidQueue id queue validationProfile)
    (hids : pending.val.Perm (queue.map StreamBatch.Issued.batch_id))
    (hnonempty : pending.val ≠ []) :
    ∃ v' remaining rest,
      stream.retire_code_batch visitor id v pending = .ok (.Ok (), v', remaining) ∧
      Queued id rest v' ∧ ValidQueue id rest validationProfile ∧
      remaining.val.Perm (rest.map StreamBatch.Issued.batch_id) ∧
      remaining.length + 1 = pending.length := by
  have hqueue : queue ≠ [] := by
    intro he
    have := hids.length_eq
    simp [he] at this
    exact hnonempty this
  obtain ⟨issued, rest, after, v', hperm, hpoll, hrun, hv'⟩ := hp.poll id queue v hv hvalid hqueue
  have hm : issued ∈ queue := hperm.mem_iff.mp (by simp)
  obtain ⟨hmodule, hissued⟩ := hvalid issued hm
  obtain ⟨hid, hfinish⟩ := hissued.finished hrun
  have hids' : (issued.batch_id :: rest.map StreamBatch.Issued.batch_id).Perm pending.val := by
    exact (hperm.map StreamBatch.Issued.batch_id).trans hids.symm
  obtain ⟨remaining, hr, hremoved⟩ := stream.retire_code_batch.complete visitor id v v'
    pending after hpoll (hid.1.trans hmodule)
    (by rw [hid.2.1]; exact hids'.mem_iff.mp (by simp)) hfinish
  refine ⟨v', remaining, rest, hr, hv', ?_, ?_, ?_⟩
  · intro entry he
    exact hvalid entry (hperm.mem_iff.mp (by simp [he]))
  · rw [hid.2.1] at hremoved
    exact List.Perm.cons_inv (hremoved.trans hids'.symm)
  · have := hremoved.length_eq
    simp only [List.length_cons] at this
    exact this

/-- Draining a valid queue terminates successfully and leaves no queued work. -/
theorem drain_complete {V : Type} (visitor : stream.StreamingVisitor V)
    (config : stream.Config) (Queued : U64 → List StreamBatch.Issued → V → Prop)
    (hp : Accepts visitor config Queued validationProfile) (id : U64)
    (queue : List StreamBatch.Issued) (v : V) (pending : alloc.vec.Vec Usize)
    (hv : Queued id queue v) (hvalid : ValidQueue id queue validationProfile)
    (hids : pending.val.Perm (queue.map StreamBatch.Issued.batch_id)) :
    ∃ v' remaining,
      stream.retire_all_code_batches visitor id v pending = .ok (.Ok (), v', remaining) ∧
      remaining.val = [] ∧ Queued id [] v' := by
  generalize hn : pending.val.length = n
  induction n using Nat.strong_induction_on generalizing queue v pending with
  | h n ih =>
    by_cases hempty : pending.val = []
    · have hqueue : queue = [] := by
        have hl := hids.length_eq
        simp [hempty] at hl
        exact hl
      refine ⟨v, pending, ?_, hempty, by simpa [hqueue] using hv⟩
      rw [stream.retire_all_code_batches, stream.retire_all_code_batches_loop, loop]
      simp [stream.retire_all_code_batches_loop.body, alloc.vec.Vec.is_empty, hempty]
    · obtain ⟨v1, remaining, rest, hr, hv1, hrest, hids1, hlen⟩ :=
        retire_complete visitor config Queued hp id queue v pending hv hvalid hids hempty
      change remaining.val.length + 1 = pending.val.length at hlen
      obtain ⟨v', final, hrun, hnil, hv'⟩ := ih remaining.val.length (by omega)
        rest v1 remaining hv1 hrest hids1 rfl
      refine ⟨v', final, ?_, hnil, hv'⟩
      rw [stream.retire_all_code_batches, stream.retire_all_code_batches_loop, loop]
      have hnon : pending.val.isEmpty = false := by simpa using hempty
      simpa [stream.retire_all_code_batches_loop.body, alloc.vec.Vec.is_empty, hnon, hr,
        core.result.Result.Insts.CoreOpsTry.branch, stream.retire_all_code_batches,
        stream.retire_all_code_batches_loop] using hrun

end Itasca.StreamAcceptingScheduler
