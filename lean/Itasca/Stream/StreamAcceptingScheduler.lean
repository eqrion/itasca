import Itasca.Stream.StreamBatchComplete
import Itasca.Stream.StreamScheduler

open Aeneas Aeneas.Std

namespace Itasca.StreamAcceptingScheduler

/-- Independent byte, typing, and size premises for an issued batch. -/
structure Valid (issued : StreamBatch.Issued) : Prop where
  bounded : issued.Bounded
  entry_bounds : CodeEntry.Bounds issued.env
  profile : Wasm1.Environment issued.env
  entries : ∃ entries, entries.length = issued.num_funcs.val ∧
    ModuleCode.EntriesTyped issued.env issued.first_func.val entries ∧
    ModuleBinary.Rep ModuleBinary.CodeEncodingWithinLimits entries issued.code.val

def ValidQueue (id : U64) (queue : List StreamBatch.Issued) : Prop :=
  ∀ issued ∈ queue, issued.module_id = id ∧ Valid issued

/-- One accepting worker policy: each returned worker is the actual result of
`validate_all` on an issued seed. The policy permits arbitrary return order and
any positive batching configuration; successful finish is derived from `Valid`,
not required of polling. It does not characterize every possible worker strategy. -/
structure Accepts {V : Type} (visitor : stream.StreamingVisitor V)
    (config : stream.Config) (Queued : U64 → List StreamBatch.Issued → V → Prop) : Prop where
  batch_positive : 0 < config.batch_bytes.val
  capacity_positive : 0 < config.max_batches.val
  custom_accepts : ModuleTail.HooksAccept visitor.moduleModuleVisitorInst
  custom_preserves : ∀ id queue, ModuleTail.PreservesInvariant
    visitor.moduleModuleVisitorInst (Queued id queue)
  region : ∀ id queue v region, Queued id queue v →
    ∃ v', visitor.custom_region v region = .ok v' ∧ Queued id queue v'
  environment : ∀ id queue v env, Queued id queue v →
    ∃ v', visitor.environment_ready v env = .ok (.Ok config, v') ∧ Queued id queue v'
  submit : ∀ id queue issued v, Queued id queue v → Valid issued →
    issued.module_id = id → queue.length < config.max_batches.val →
    ∃ v', visitor.submit_code_batch v issued.seed = .ok (.Ok (), v') ∧
      Queued id (queue ++ [issued]) v'
  poll : ∀ id queue v, Queued id queue v → ValidQueue id queue → queue ≠ [] →
    ∃ issued rest after v', (issued :: rest).Perm queue ∧
      visitor.poll_code_batch v = .ok (.Ok after, v') ∧
      stream.CodeBatch.validate_all issued.seed = .ok after ∧ Queued id rest v'
  code_end : ∀ id queue v, Queued id queue v →
    ∃ v', visitor.code_end v = .ok (.Ok (), v') ∧ Queued id queue v'
  tail_ready : ∀ id queue v tail, Queued id queue v →
    ∃ v', visitor.tail_ready v tail = .ok (.Ok (), v') ∧ Queued id queue v'

theorem Valid.finished {issued : StreamBatch.Issued} (h : Valid issued)
    {after : stream.CodeBatch} (hr : stream.CodeBatch.validate_all issued.seed = .ok after) :
    StreamBatch.Identity issued after ∧ stream.CodeBatch.finish after = .ok (.Ok ()) := by
  obtain ⟨entries, hn, ht, hb⟩ := h.entries
  obtain ⟨result, hrun, hreachable, hfinish⟩ := stream.CodeBatch.validate_all.complete_seed
    issued entries h.bounded hn ht h.profile h.entry_bounds hb
  have he : result = after := by simpa using hrun.symm.trans hr
  subst result
  exact ⟨hreachable.validation.1, hfinish⟩

end Itasca.StreamAcceptingScheduler

namespace Itasca

/-- A known pending, correctly identified, finished result is accepted by the
actual search and swap/pop retirement implementation. -/
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

/-- Valid pending work retires in any scheduler-selected order. Successful
finish follows from actual worker execution on independent typed encodings. -/
theorem retire_complete {V : Type} (visitor : stream.StreamingVisitor V)
    (config : stream.Config) (Queued : U64 → List StreamBatch.Issued → V → Prop)
    (hp : Accepts visitor config Queued) (id : U64)
    (queue : List StreamBatch.Issued) (v : V) (pending : alloc.vec.Vec Usize)
    (hv : Queued id queue v) (hvalid : ValidQueue id queue)
    (hids : pending.val.Perm (queue.map StreamBatch.Issued.batch_id))
    (hnonempty : pending.val ≠ []) :
    ∃ v' remaining rest,
      stream.retire_code_batch visitor id v pending = .ok (.Ok (), v', remaining) ∧
      Queued id rest v' ∧ ValidQueue id rest ∧
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
    (hp : Accepts visitor config Queued) (id : U64)
    (queue : List StreamBatch.Issued) (v : V) (pending : alloc.vec.Vec Usize)
    (hv : Queued id queue v) (hvalid : ValidQueue id queue)
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
