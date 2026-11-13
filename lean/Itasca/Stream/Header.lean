import Itasca.Support.Result
import Itasca.Stream.Source
import Itasca.Contracts
import Itasca.Module.Custom.Trace
import Itasca.Module.Code.Framing
import Itasca.Generated.Funs

/-!
Sections, each formerly its own module: Retirement, Scheduler, EntryFrame, BatchBounds, DriverRun, Header.
-/

/-! ## Retirement -/

section

/-!
# Batch retirement

The loops that retire outstanding code batches: `stream.retire_code_batch` polls one worker through
`StreamingVisitor.poll_code_batch`, checks its module identity, removes its batch ID from the
pending vector by swap-and-pop, and requires `stream.CodeBatch.finish` to succeed.
`stream.retire_code_batch.removes` describes the pending vector after a successful retirement, and
`stream.retire_all_code_batches.spec` shows that draining terminates whenever polls return
(`StreamRetirement.PollTotal`), whatever records the scheduler supplies.
-/

open Aeneas Aeneas.Std

namespace Itasca.StreamRetirement

/-- The pending search finds the first matching entry or its vector's end. -/
def SearchPost (pending : alloc.vec.Vec Usize) (needle first found : Usize) : Prop :=
  first.val ≤ found.val ∧ found.val ≤ pending.length ∧
  (∀ (j : Nat) (hj : j < pending.length), first.val ≤ j → j < found.val →
    pending.val[j] ≠ needle) ∧
  (∀ h : found.val < pending.length, pending.val[found.val] = needle)

end Itasca.StreamRetirement

namespace Itasca

/-- The pending-ID search loop returns the first position from `first` holding `needle`, or the
end of the vector. -/
@[step]
theorem stream.retire_code_batch_loop.spec (pending : alloc.vec.Vec Usize)
    (needle first : Usize) (hfirst : first.val ≤ pending.length) :
    stream.retire_code_batch_loop pending needle first ⦃ StreamRetirement.SearchPost pending needle first ⦄ := by
  unfold stream.retire_code_batch_loop
  apply loop.spec_decr_nat (fun i => pending.length - i.val)
    (fun i => first.val ≤ i.val ∧ i.val ≤ pending.length ∧
      ∀ (j : Nat) (hj : j < pending.length), first.val ≤ j → j < i.val →
        pending.val[j] ≠ needle)
  · intro i hi
    obtain ⟨hlo, hhi, hprev⟩ := hi
    unfold stream.retire_code_batch_loop.body
    by_cases hin : i.val < pending.length
    · have hin' : i < alloc.vec.Vec.len pending := by scalar_tac
      simp only [hin', ↓reduceIte]
      step
      split
      · rename_i hne
        step
        refine ⟨by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
        intro j hj hstart hjnext
        by_cases hji : j < i.val
        · exact hprev j hj hstart hji
        · have heq : j = i.val := by scalar_tac
          subst j
          scalar_tac
      · simp only [WP.spec_ok]
        refine ⟨hlo, hhi, hprev, ?_⟩
        intro h
        scalar_tac
    · have hout : ¬ i < alloc.vec.Vec.len pending := by scalar_tac
      simp only [hout, ↓reduceIte, WP.spec_ok]
      exact ⟨hlo, hhi, hprev, by omega⟩
  · exact ⟨by omega, hfirst, by omega⟩

end Itasca

namespace Itasca.StreamRetirement

/-- Swap with the last ID and pop removes exactly the indexed occurrence,
without requiring the vector to be duplicate-free. -/
theorem swap_pop_perm {α : Type} (xs : List α) (i : Nat) (hi : i < xs.length) :
    (xs[i] :: (xs.set i (xs[xs.length - 1]'(by omega))).dropLast).Perm xs := by
  let last := xs[xs.length - 1]'(by omega)
  let ys := xs.set i last
  have hylen : ys.length = xs.length := by simp [ys]
  have hyne : ys ≠ [] := by intro h; have := congrArg List.length h; simp only [List.length_nil, hylen] at this; omega
  have hlast : ys.getLast hyne = last := by
    rw [List.getLast_eq_getElem]
    simp only [ys, List.length_set, List.getElem_set]
    split <;> rfl
  have hdecomp : ys.dropLast ++ [last] = ys := by
    simpa only [hlast] using List.dropLast_append_getLast hyne
  have hrotate : (last :: ys.dropLast).Perm ys := by
    have h : (last :: ys.dropLast).Perm (ys.dropLast ++ [last]) := by
      simpa only [List.singleton_append] using
        (List.perm_append_comm (l₁ := [last]) (l₂ := ys.dropLast))
    rw [hdecomp] at h
    exact h
  have hperm := hrotate.trans (List.set_perm_cons_eraseIdx hi last)
  exact (List.Perm.cons xs[i] (List.Perm.cons_inv hperm)).trans
    (List.getElem_cons_eraseIdx_perm hi)

end Itasca.StreamRetirement

namespace Itasca.StreamRetirement

/-- A successful retirement comes from an actual poll that returned a batch of the expected module
whose `stream.CodeBatch.finish` succeeded, and the batch ID was removed from the pending vector. -/
def Retired {V : Type} (visitor : stream.StreamingVisitor V) (moduleId : U64)
    (before : V) (pending : alloc.vec.Vec Usize) :
    (core.result.Result Unit error.Error × V × alloc.vec.Vec Usize) → Prop
  | (.Ok (), after, remaining) => ∃ batch,
      visitor.poll_code_batch before = .ok (.Ok batch, after) ∧
      batch.module_id = moduleId ∧ stream.CodeBatch.finish batch = .ok (.Ok ()) ∧
      (batch.batch_id :: remaining.val).Perm pending.val
  | (.Err _, _, _) => True

private theorem finish_returns (batch : stream.CodeBatch) :
    ∃ r, stream.CodeBatch.finish batch = .ok r := by
  unfold stream.CodeBatch.finish
  cases batch.error <;> simp only
  · split
    · split <;> exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

end Itasca.StreamRetirement

namespace Itasca

/-- `stream.retire_code_batch` satisfies `StreamRetirement.Retired` when the reached poll
returns. -/
@[step]
theorem stream.retire_code_batch.spec {V : Type} (visitor : stream.StreamingVisitor V)
    (moduleId : U64) (state : V) (pending : alloc.vec.Vec Usize)
    (hreturn : ∃ r, visitor.poll_code_batch state = .ok r) :
    stream.retire_code_batch visitor moduleId state pending ⦃
      StreamRetirement.Retired visitor moduleId state pending ⦄ := by
  obtain ⟨⟨r, state'⟩, hpoll⟩ := hreturn
  unfold stream.retire_code_batch
  rw [hpoll]
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      StreamRetirement.Retired]
  | Ok batch =>
    simp [core.result.Result.Insts.CoreOpsTry.branch]
    split
    · rename_i hmodule
      obtain ⟨found, hfind, hf⟩ := WP.spec_imp_exists
        (stream.retire_code_batch_loop.spec pending batch.batch_id 0#usize (by simp))
      rw [hfind]
      simp only [bind_ok]
      split
      · simp [StreamRetirement.Retired]
      · rename_i hfound
        have hlt : found.val < pending.length := by have := hf.2.1; scalar_tac
        have hmatch : pending.val[found.val] = batch.batch_id := hf.2.2.2 hlt
        step
        step
        step
        simp only [alloc.vec.Vec.pop, bind_ok]
        obtain ⟨result, hfinish⟩ := StreamRetirement.finish_returns batch
        rw [hfinish]
        simp only [bind_ok]
        cases result with
        | Err e => simp [StreamRetirement.Retired]
        | Ok u =>
          cases u
          refine ⟨batch, hpoll, by scalar_tac, hfinish, ?_⟩
          have hlast : last.val = pending.val.length - 1 := by scalar_tac
          simpa only [index_mut_back_post, i3_post, hlast, alloc.vec.Vec.set_val_eq,
            alloc.vec.Vec.from_val, hmatch] using
            (StreamRetirement.swap_pop_perm pending.val found.val hlt)
    · simp [StreamRetirement.Retired]

end Itasca

namespace Itasca

theorem stream.retire_code_batch.total {V : Type} (visitor : stream.StreamingVisitor V)
    (moduleId : U64) (state : V) (pending : alloc.vec.Vec Usize)
    (hreturn : ∃ r, visitor.poll_code_batch state = .ok r) :
    ∃ r, stream.retire_code_batch visitor moduleId state pending = .ok r := by
  obtain ⟨r, hr, _⟩ := WP.spec_imp_exists
    (stream.retire_code_batch.spec visitor moduleId state pending hreturn)
  exact ⟨r, hr⟩

/-- Successful retirement exposes its actual poll and finish checks without
assuming that any callback returns on unexecuted paths. -/
theorem stream.retire_code_batch.accepted {V : Type} (visitor : stream.StreamingVisitor V)
    (moduleId : U64) (state state' : V) (pending remaining : alloc.vec.Vec Usize)
    (h : stream.retire_code_batch visitor moduleId state pending = .ok (.Ok (), state', remaining)) :
    ∃ batch, visitor.poll_code_batch state = .ok (.Ok batch, state') ∧
      batch.module_id = moduleId ∧ stream.CodeBatch.finish batch = .ok (.Ok ()) ∧
      (batch.batch_id :: remaining.val).Perm pending.val := by
  have hex : ∃ r, visitor.poll_code_batch state = .ok r := by
    unfold stream.retire_code_batch at h
    obtain ⟨r, hr, _⟩ := ResultFacts.bind_ok_inv _ _ _ h
    exact ⟨r, hr⟩
  have hs := stream.retire_code_batch.spec visitor moduleId state pending hex
  simpa [h, StreamRetirement.Retired] using hs

/-- Draining terminates under returning polls even when those polls supply foreign, unfinished or
fabricated records. An accepted drain leaves the pending vector empty. -/
@[step]
theorem stream.retire_all_code_batches.spec {V : Type} (visitor : stream.StreamingVisitor V)
    (moduleId : U64) (state : V) (pending : alloc.vec.Vec Usize)
    (htotal : StreamRetirement.PollTotal visitor) :
    stream.retire_all_code_batches visitor moduleId state pending ⦃ fun (r, _, remaining) =>
      r = .Ok () → remaining.val = [] ⦄ := by
  unfold stream.retire_all_code_batches stream.retire_all_code_batches_loop
  apply loop.spec_decr_nat (fun s => s.2.length) (fun _ => True)
  · rintro ⟨state, pending⟩ _
    simp only [stream.retire_all_code_batches_loop.body, alloc.vec.Vec.is_empty, bind_ok]
    by_cases hempty : pending.val = []
    · simp [hempty]
    · have hnonempty : pending.val.isEmpty = false := by simpa using hempty
      simp only [hnonempty, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨⟨r, state', remaining⟩, hr, hp⟩ := WP.spec_imp_exists
        (stream.retire_code_batch.spec visitor moduleId state pending (htotal state))
      rw [hr]
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok u =>
        cases u
        simp [core.result.Result.Insts.CoreOpsTry.branch]
        obtain ⟨batch, _, _, _, hperm⟩ := hp
        have hlen := hperm.length_eq
        simp only [List.length_cons] at hlen
        change remaining.val.length < pending.val.length
        omega
  · trivial

theorem stream.retire_all_code_batches.total {V : Type} (visitor : stream.StreamingVisitor V)
    (moduleId : U64) (state : V) (pending : alloc.vec.Vec Usize)
    (htotal : StreamRetirement.PollTotal visitor) :
    ∃ r, stream.retire_all_code_batches visitor moduleId state pending = .ok r := by
  obtain ⟨r, hr, _⟩ := WP.spec_imp_exists
    (stream.retire_all_code_batches.spec visitor moduleId state pending htotal)
  exact ⟨r, hr⟩

end Itasca

end

/-! ## Scheduler -/

section

/-!
# Scheduler soundness

Consequences of the scheduler premises `StreamScheduler.CallbacksTotal` and
`StreamScheduler.Provenance`, defined in `Itasca/Contracts`. `retire_sound`
and `drain_sound` show that successful retirement and draining produce `StreamScheduler.Completed`
certificates (exact byte coverage and typed entries) for every pending issued batch.
-/

open Aeneas Aeneas.Std

namespace Itasca.StreamScheduler
/-- A completed batch has exact byte coverage and ordered entry certificates. This is derived at
successful retirement and is never a premise on polls. -/
def Completed (issued : StreamBatch.Issued) : Prop :=
  ∃ entries, entries.length = issued.num_funcs.val ∧
    ModuleBinary.Rep (Profile.CodeEncoding) entries issued.code.val ∧
    ModuleCode.EntriesTyped issued.env issued.first_func.val entries

theorem Provenance.environment_preserves {V : Type} {visitor : stream.StreamingVisitor V}
    {Tracks : U64 → List StreamBatch.Issued → V → Prop} (hp : Provenance visitor Tracks)
    (id : U64) (history : List StreamBatch.Issued) (data : Slice U8)
    (v v' : V) (env : metadata.Env) (next : Usize)
    (h : metadata.validate_env_with visitor.metadataModuleVisitorInst data v = .ok (.Ok (env, next), v')) :
    Tracks id history v → Tracks id history v' :=
  metadata.validate_env_with.accepted_invariant _ _ (hp.custom id history) data v env next v' h

theorem Provenance.tail_preserves {V : Type} {visitor : stream.StreamingVisitor V}
    {Tracks : U64 → List StreamBatch.Issued → V → Prop} (hp : Provenance visitor Tracks)
    (id : U64) (history : List StreamBatch.Issued) (data : Slice U8) (pos : Usize)
    (v v' : V) (env : metadata.Env) (tail : metadata.Tail)
    (h : metadata.validate_tail_with visitor.metadataModuleVisitorInst data pos env v = .ok (.Ok tail, v')) :
    Tracks id history v → Tracks id history v' :=
  metadata.validate_tail_with.accepted_invariant _ _ (hp.custom id history) data pos env v tail v' h

/-- After a successful retirement, every historical issued batch matching the removed pending ID
is completed, and provenance is preserved. Polls need not be replay-free. -/
theorem retire_sound {V : Type} (visitor : stream.StreamingVisitor V)
    (Tracks : U64 → List StreamBatch.Issued → V → Prop) (hp : Provenance visitor Tracks)
    (id : U64) (history : List StreamBatch.Issued) (v v' : V)
    (pending remaining : alloc.vec.Vec Usize) (hv : Tracks id history v)
    (henv : ∀ issued ∈ history, CodeEntry.Bounds issued.env)

    (h : stream.retire_code_batch visitor id v pending = .ok (.Ok (), v', remaining)) :
    Tracks id history v' ∧ ∃ batchId,
      (batchId :: remaining.val).Perm pending.val ∧
      ∀ issued ∈ history, issued.module_id = id → issued.batch_id = batchId → Completed issued := by
  obtain ⟨batch, hpolled, hmodule, hfinish, hperm⟩ :=
    stream.retire_code_batch.accepted visitor id v v' pending remaining h
  obtain ⟨hv', hr⟩ := hp.poll id history v batch v' hv hpolled
  refine ⟨hv', batch.batch_id, hperm, ?_⟩
  intro issued hm hid hbatch
  exact (hr issued hm (hid.trans hmodule.symm) hbatch).finished (henv issued hm) hfinish

end Itasca.StreamScheduler

open Aeneas Aeneas.Std

namespace Itasca.StreamScheduler
/-- An accepted drain empties the pending vector and completes every historical issued batch
whose ID was pending, while provenance is preserved across every poll. -/
theorem drain_sound {V : Type} (visitor : stream.StreamingVisitor V)
    (Tracks : U64 → List StreamBatch.Issued → V → Prop) (hp : Provenance visitor Tracks)
    (id : U64) (history : List StreamBatch.Issued) (v v' : V)
    (pending remaining : alloc.vec.Vec Usize) (hv : Tracks id history v)
    (henv : ∀ issued ∈ history, CodeEntry.Bounds issued.env)

    (h : stream.retire_all_code_batches visitor id v pending = .ok (.Ok (), v', remaining)) :
    Tracks id history v' ∧ remaining.val = [] ∧
      ∀ issued ∈ history, issued.module_id = id → issued.batch_id ∈ pending.val → Completed issued := by
  generalize hn : pending.val.length = n
  induction n using Nat.strong_induction_on generalizing v pending with
  | h n ih =>
    unfold stream.retire_all_code_batches stream.retire_all_code_batches_loop at h
    rw [loop] at h
    simp only [stream.retire_all_code_batches_loop.body, alloc.vec.Vec.is_empty, bind_ok] at h
    by_cases hempty : pending.val = []
    · simp [hempty] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hv, hempty, by simp [hempty]⟩
    · have hnonempty : pending.val.isEmpty = false := by simpa using hempty
      simp only [hnonempty, Bool.false_eq_true, ↓reduceIte, Std.bind_assoc] at h
      obtain ⟨⟨r, next, rest⟩, hretire, hrest⟩ := ResultFacts.bind_ok_inv _ _ _ h
      cases r with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at hrest
      | Ok u =>
        cases u
        obtain ⟨hvNext, batchId, hperm, hcomplete⟩ :=
          retire_sound visitor Tracks hp id history v next pending rest hv henv hretire
        have hlen := hperm.length_eq
        simp only [List.length_cons] at hlen
        have hlt : rest.val.length < n := by omega
        have hrecursive : stream.retire_all_code_batches visitor id next rest =
            .ok (.Ok (), v', remaining) := by
          simpa [stream.retire_all_code_batches, stream.retire_all_code_batches_loop, stream.retire_all_code_batches_loop.body,
            alloc.vec.Vec.is_empty, core.result.Result.Insts.CoreOpsTry.branch] using hrest
        obtain ⟨hvFinal, hnil, hcompleted⟩ := ih rest.val.length hlt next rest hvNext hrecursive rfl
        refine ⟨hvFinal, hnil, ?_⟩
        intro issued hm hmid hpend
        have hmem := hperm.mem_iff.mpr hpend
        rcases List.mem_cons.mp hmem with hid | hrestmem
        · exact hcomplete issued hm hmid hid
        · exact hcompleted issued hm hmid hrestmem

end Itasca.StreamScheduler

end

/-! ## EntryFrame -/

section

/-!
# Code entry frames

`StreamFraming.EntryFrame` describes the `stream.CodeEntry` returned by `stream.frame_entry`: its
declared byte extent (`ModuleCode.Extent`) shifted by the batch offset into absolute coordinates.
`stream.frame_entry.sound` and `.complete` relate the function to this predicate. Completeness
needs only that the shifted end stays within the module cap.
-/

open Aeneas Aeneas.Std

namespace Itasca.StreamFraming

/-- A frame records the entry's declared byte extent and the corresponding
absolute offsets. It does not certify local declarations or instructions. -/
def EntryFrame (data : Slice U8) (pos index offset : Usize)
    (entry : stream.CodeEntry) : Prop :=
  ∃ content finish, ModuleCode.Extent data pos content finish ∧
    entry.index = index ∧ entry.start.val = offset.val + pos.val ∧
    entry.contents.val = offset.val + content.val ∧
    entry.end.val = offset.val + finish.val ∧
    entry.end.val ≤ limits.MAX_MODULE_BYTES.val

end Itasca.StreamFraming

namespace Itasca

@[step]
theorem stream.frame_entry.spec (data : Slice U8) (pos index offset : Usize) :
    stream.frame_entry data pos index offset ⦃ r => match r with
      | .Ok entry => StreamFraming.EntryFrame data pos index offset entry
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (metadata.code_entry_extent.spec data pos)
  rw [stream.frame_entry, hr]
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
    obtain ⟨content, finish⟩ := pair
    simp [core.result.Result.Insts.CoreOpsTry.branch]
    obtain ⟨r, hs, hsp⟩ := WP.spec_imp_exists (limits.add_offset.spec offset pos)
    rw [hs]
    cases r with
    | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok start =>
      simp
      obtain ⟨r, hc, hcp⟩ := WP.spec_imp_exists (limits.add_offset.spec offset content)
      rw [hc]
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok contents =>
        simp
        obtain ⟨r, hf, hfp⟩ := WP.spec_imp_exists (limits.add_offset.spec offset finish)
        rw [hf]
        cases r with
        | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok last =>
          simp only [bind_ok, WP.spec_ok]
          exact ⟨content, finish, hp, rfl, hsp.1, hcp.1, hfp.1, hfp.2⟩

/-- A declared extent within the module offset cap can always be framed. -/
theorem stream.frame_entry.complete (data : Slice U8) (pos index offset content finish : Usize)
    (hext : ModuleCode.Extent data pos content finish)
    (hbound : offset.val + finish.val ≤ limits.MAX_MODULE_BYTES.val) :
    ∃ entry, stream.frame_entry data pos index offset = .ok (.Ok entry) ∧
      StreamFraming.EntryFrame data pos index offset entry := by
  have hp := hext.span
  obtain ⟨start, hs, hsp⟩ := limits.add_offset.complete offset pos (by omega)
  obtain ⟨contents, hc, hcp⟩ := limits.add_offset.complete offset content (by omega)
  obtain ⟨last, hf, hfp⟩ := limits.add_offset.complete offset finish hbound
  refine ⟨⟨index, start, contents, last⟩, ?_,
    content, finish, hext, rfl, hsp, hcp, hfp, by change last.val ≤ _; omega⟩
  simp [stream.frame_entry, metadata.code_entry_extent.complete data pos content finish hext,
    hs, hc, hf, core.result.Result.Insts.CoreOpsTry.branch]

end Itasca

end

/-! ## BatchBounds -/

section

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

end

/-! ## DriverRun -/

section

/-!
# Accepted driver runs

Unpacks an accepted run of the extracted driver into witnesses for each phase.
`stream.validate_streaming.accepted` and `stream.validate_remaining.accepted` show that an
`Ok` result of `stream.validate_streaming` and of its post-environment phases yields the
`StreamRun.Accepted` and `StreamRun.Remaining` records: the environment read and decode, the code
header, the configuration, the batch submission, the tail read and decode, and the final drain.
The records describe executions of the extracted driver and make no claim about the source or
scheduler.
-/

open Aeneas Aeneas.Std

namespace Itasca.StreamRun

/-- Witnesses of the phases of `stream.validate_remaining` after the environment is decoded,
including the tail handoff. They describe executions of the extracted driver, not an alternate
validator. -/
structure Remaining {S V : Type} (source : stream.Source S)
    (visitor : stream.StreamingVisitor V) (id : U64) (state : S)
    (env : metadata.Env) (environmentLength : Usize) (before after : V)
     where
  codeLength : Usize
  codeEnd : Usize
  entries : Usize
  config : stream.Config
  configured : V
  pending : alloc.vec.Vec Usize
  submitted : V
  ended : V
  tailBytes : Slice U8
  moduleEnd : Usize
  region : V
  tail : metadata.Tail
  decodedTail : V
  ready : V
  remaining : alloc.vec.Vec Usize
  length_call : source.code_len state = .ok codeLength
  code_bound : limits.add_offset environmentLength codeLength = .ok (.Ok codeEnd)
  header_call : stream.read_code_header source state codeLength env = .ok (.Ok entries)
  configured_call : visitor.environment_ready before env = .ok (.Ok config, configured)
  batch_bytes_positive : config.batch_bytes ≠ 0#usize
  max_batches_positive : config.max_batches ≠ 0#usize
  submit_call : stream.submit_code_batches source visitor id state env codeLength entries config configured =
    .ok (.Ok pending, submitted)
  end_call : visitor.code_end submitted = .ok (.Ok (), ended)
  tail_call : source.tail state = .ok (.Ok tailBytes)
  module_bound : limits.add_offset codeEnd (Slice.len tailBytes) = .ok (.Ok moduleEnd)
  region_call : visitor.custom_region ended .Tail = .ok region
  decode_tail : metadata.validate_tail_with visitor.metadataModuleVisitorInst tailBytes 0#usize env region =
    .ok (.Ok tail, decodedTail)
  ready_call : visitor.tail_ready decodedTail tail = .ok (.Ok (), ready)
  drain_call : stream.retire_all_code_batches visitor id ready pending = .ok (.Ok (), after, remaining)

/-- Witnesses of an accepted `stream.validate_streaming`: the environment read, its size bound, the
custom-section region callback, the environment decode, and the `Remaining` phases. -/
structure Accepted {S V : Type} (source : stream.Source S)
    (visitor : stream.StreamingVisitor V) (id : U64) (state : S)
    (before after : V) (env : metadata.Env)
     where
  environment : Slice U8
  environmentLength : Usize
  region : V
  decoded : V
  environment_call : source.environment state = .ok (.Ok environment)
  environment_bound : limits.add_offset 0#usize (Slice.len environment) = .ok (.Ok environmentLength)
  region_call : visitor.custom_region before .Environment = .ok region
  decode_environment : metadata.validate_env_with visitor.metadataModuleVisitorInst environment region =
    .ok (.Ok (env, environmentLength), decoded)
  remaining : Remaining source visitor id state env environmentLength decoded after

end Itasca.StreamRun

namespace Itasca

/-- An accepted `stream.validate_remaining` yields witnesses for each of its phases. -/
theorem stream.validate_remaining.accepted {S V : Type} (source : stream.Source S)
    (visitor : stream.StreamingVisitor V) (id : U64) (state : S)
    (env : metadata.Env) (envLen : Usize) (v v' : V)
    (h : stream.validate_remaining source visitor id state env envLen v = .ok (.Ok (), v')) :
    Nonempty (StreamRun.Remaining source visitor id state env envLen v v' ) := by
  unfold stream.validate_remaining at h
  obtain ⟨codeLen, hlen, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
  obtain ⟨r, hbound, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
  | Ok codeEnd =>
    simp [core.result.Result.Insts.CoreOpsTry.branch] at h
    obtain ⟨r, hheader, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
    cases r with
    | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
    | Ok entries =>
      simp at h
      obtain ⟨⟨r, configured⟩, hconfig, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
      | Ok config =>
        simp at h
        split at h
        · simp at h
        · rename_i hbytes
          split at h
          · simp at h
          · rename_i hbatches
            obtain ⟨⟨r, submitted⟩, hsubmit, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
            cases r with
            | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
            | Ok pending =>
              simp at h
              obtain ⟨⟨r, ended⟩, hend, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
              cases r with
              | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
              | Ok u =>
                cases u
                simp at h
                obtain ⟨r, htail, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
                cases r with
                | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
                | Ok tailBytes =>
                  simp at h
                  obtain ⟨r, hmodule, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
                  cases r with
                  | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
                  | Ok moduleEnd =>
                    simp at h
                    obtain ⟨region, hregion, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
                    obtain ⟨⟨r, decoded⟩, hdecoded, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
                    cases r with
                    | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
                    | Ok tail =>
                      simp at h
                      obtain ⟨⟨r, ready⟩, hready, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
                      cases r with
                      | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
                      | Ok u =>
                        cases u
                        simp at h
                        obtain ⟨⟨r, after, remaining⟩, hdrain, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
                        simp at h
                        obtain ⟨rfl, rfl⟩ := h
                        exact ⟨⟨codeLen, codeEnd, entries, config, configured, pending, submitted, ended,
                          tailBytes, moduleEnd, region, tail, decoded, ready, remaining, hlen, hbound,
                          hheader, hconfig, hbytes, hbatches, hsubmit, hend, htail, hmodule, hregion,
                          hdecoded, hready, hdrain⟩⟩

set_option maxHeartbeats 600000 in
/-- An accepted generic driver exposes its decoded environment and the tail delivery it actually
performed. No assumption is made that the visitor state keeps any metadata. -/
theorem stream.validate_streaming.accepted {S V : Type} (source : stream.Source S)
    (visitor : stream.StreamingVisitor V) (id : U64) (state : S)
    (v v' : V) (initial env : metadata.Env)
    (h : stream.validate_streaming source visitor id state v initial = .ok (.Ok (), v', env)) :
    Nonempty (StreamRun.Accepted source visitor id state v v' env ) := by
  unfold stream.validate_streaming at h
  obtain ⟨r, henv, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
  | Ok environment =>
    simp [core.result.Result.Insts.CoreOpsTry.branch] at h
    obtain ⟨r, hbound, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
    cases r with
    | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
    | Ok envLen =>
      simp at h
      obtain ⟨region, hregion, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
      obtain ⟨⟨r, decoded⟩, hdecode, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
      | Ok pair =>
        obtain ⟨actualEnv, envEnd⟩ := pair
        simp at h
        split at h
        · rename_i heq
          have he : envEnd = envLen := by apply UScalar.eq_of_val_eq; simpa using heq
          subst envEnd
          obtain ⟨⟨r, after⟩, hremaining, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
          simp at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          obtain ⟨remaining⟩ := stream.validate_remaining.accepted source visitor id state actualEnv envLen decoded after hremaining
          exact ⟨⟨environment, envLen, region, decoded, henv, hbound, hregion, hdecode, remaining⟩⟩
        · simp at h

end Itasca

end

/-! ## Header -/

section

/-!
# Code section header

Soundness and termination for `stream.read_code_header`, which reads at most the first 11 bytes of
the code region and checks the section ID, the section size and the function count against the
environment. `StreamFraming.HeaderChecked` describes what the driver observed through the source,
and `StreamFraming.HeaderAt` is the resulting fact about the coherent code region, with an absent
region and a present zero-entry section as separate cases. Completeness is in
`Stream/HeaderComplete`.
-/

open Aeneas Aeneas.Std

namespace Itasca

namespace StreamFraming

/-- The driver observes either an absent code region or an exact bounded
header view. Counts and section size are independent of entry validation. -/
def HeaderChecked {S : Type} (source : stream.Source S) (state : S)
    (codeLen : Usize) (env : metadata.Env) (entries : Usize) : Prop :=
  (codeLen = 0#usize ∧ entries = 0#usize ∧ env.func_type_indices.val = []) ∨
  ∃ header content size count,
    stream.read_exact source state 0#usize (core.cmp.impls.OrdUsize.min codeLen 11#usize) =
      .ok (.Ok header) ∧
    ModuleBinary.At ModuleBinary.ByteEncoding header 0#usize 10#u8 1#usize ∧
    Leb128.Decoded header 1#usize size content ∧
    codeLen.val = content.val + size.val ∧
    Leb128.Decoded header content count entries ∧
    entries.val ≤ codeLen.val ∧ count.val = env.func_type_indices.val.length

theorem header_limit : limits.MAX_CODE_HEADER_BYTES = .ok 11#usize := by
  have hs : limits.MAX_CODE_HEADER_BYTES ⦃ x => x = 11#usize ⦄ := by
    unfold limits.MAX_CODE_HEADER_BYTES limits.MAX_LEB_BYTES
    step*
  obtain ⟨x, hx, rfl⟩ := WP.spec_imp_exists hs
  exact hx

theorem min_val (a b : Usize) :
    (core.cmp.impls.OrdUsize.min a b).val = Nat.min a.val b.val := by
  simp only [core.cmp.impls.OrdUsize.min]
  split <;> simp_all [Nat.min_def]

end StreamFraming

/-- `stream.read_code_header` either errors or returns the entry count of a checked header,
provided the reached code read returns. -/
theorem stream.read_code_header.spec {S : Type} (source : stream.Source S) (state : S)
    (codeLen : Usize) (env : metadata.Env)
    (hreturn : codeLen ≠ 0#usize → ∃ r, source.code state 0#usize
      (core.cmp.impls.OrdUsize.min codeLen 11#usize) = .ok r) :
    stream.read_code_header source state codeLen env ⦃ r => match r with
      | .Ok entries => StreamFraming.HeaderChecked source state codeLen env entries
      | .Err _ => True ⦄ := by
  unfold stream.read_code_header
  dsimp only
  split
  · rename_i hzero
    simp [alloc.vec.Vec.is_empty]
    split
    · rename_i hempty
      simp only [WP.spec_ok]
      exact .inl ⟨hzero, rfl, by simpa using hempty⟩
    · simp
  · rename_i hnonzero
    rw [StreamFraming.header_limit]
    simp only [bind_ok, lift]
    obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (stream.read_exact.spec source state
      0#usize (core.cmp.impls.OrdUsize.min codeLen 11#usize) (by simp) (hreturn hnonzero))
    rw [hr]
    cases r with
    | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok header =>
      have hlen : header.length = Nat.min codeLen.val 11 := by
        simpa [StreamFraming.min_val] using hp.2
      have hpositive : 0 < header.length := by
        have hn : codeLen.val ≠ 0 := by intro he; apply hnonzero; exact UScalar.eq_of_val_eq he
        rw [hlen]
        exact Nat.lt_min.mpr ⟨by omega, by decide⟩
      obtain ⟨id, hid, hidval⟩ := WP.spec_imp_exists (Slice.index_usize_spec header 0#usize hpositive)
      simp [core.result.Result.Insts.CoreOpsTry.branch, hid]
      split
      · rename_i hiscode
        have hidcode : id = 10#u8 := by
          apply UScalar.eq_of_val_eq
          simpa [metadata.SECTION_CODE] using hiscode
        have hbyte : ModuleBinary.At ModuleBinary.ByteEncoding header 0#usize 10#u8 1#usize :=
          ⟨[10#u8], rfl, Wasm1.BytesAt.byte header 0#usize 1#usize 10#u8 hpositive
            (by simpa [hidcode] using hidval.symm) (by simp)⟩
        obtain ⟨r, hs, hsp⟩ := WP.spec_imp_exists (stream.read_len.spec header 1#usize)
        rw [hs]
        cases r with
        | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok pair =>
          obtain ⟨len, content⟩ := pair
          obtain ⟨size, hsizeval, hsize⟩ := hsp
          simp
          obtain ⟨r, he, hep⟩ := WP.spec_imp_exists (limits.add_offset.spec content len)
          rw [he]
          cases r with
          | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          | Ok finish =>
            simp
            split
            · simp
            · rename_i hnotover
              split
              · simp
              · rename_i hnotunder
                have hend : codeLen.val = content.val + size.val := by omega
                obtain ⟨r, hc, hcp⟩ := WP.spec_imp_exists (stream.read_len.spec header content)
                rw [hc]
                cases r with
                | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
                | Ok pair =>
                  obtain ⟨countLen, entries⟩ := pair
                  obtain ⟨count, hcountval, hcount⟩ := hcp
                  simp
                  split
                  · simp
                  · rename_i hentries
                    split
                    · rename_i hcountlen
                      simp only [WP.spec_ok]
                      change ¬ entries.val > finish.val at hentries
                      change countLen.val = env.func_type_indices.val.length at hcountlen
                      exact .inr ⟨header, content, size, count, hr, hbyte, hsize, hend,
                        hcount, by omega, by omega⟩
                    · simp
      · simp

/-- Acceptance itself supplies the reached source callback. No premise is
imposed on unrelated or unexecuted source calls. -/
theorem stream.read_code_header.checked {S : Type} (source : stream.Source S) (state : S)
    (codeLen : Usize) (env : metadata.Env) (entries : Usize)
    (h : stream.read_code_header source state codeLen env = .ok (.Ok entries)) :
    StreamFraming.HeaderChecked source state codeLen env entries := by
  have hreturn : codeLen ≠ 0#usize → ∃ r, source.code state 0#usize
      (core.cmp.impls.OrdUsize.min codeLen 11#usize) = .ok r := by
    intro hnonzero
    unfold stream.read_code_header at h
    rw [if_neg hnonzero, StreamFraming.header_limit] at h
    simp only [bind_ok, lift] at h
    obtain ⟨r, hr, hrest⟩ := ResultFacts.bind_ok_inv _ _ _ h
    cases r with
    | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at hrest
    | Ok header =>
      exact ⟨.Ok header, (stream.read_exact.accepted source state _ _ header (by simp) hr).1⟩
  have hs := stream.read_code_header.spec source state codeLen env hreturn
  simpa [h] using hs

namespace StreamFraming

/-- The code region is either empty with no declared functions, or a code section whose size
covers the whole region. A present zero-entry section is distinct from an absent one. -/
def HeaderAt (data : Slice U8) (env : metadata.Env) (entries : Usize) : Prop :=
  (data.val = [] ∧ entries = 0#usize ∧ env.func_type_indices.val = []) ∨
    ∃ count, ModuleCode.Section data 0#usize env ⟨count, entries, Slice.len data⟩ ∧
      entries.val ≤ data.length

theorem HeaderChecked.sound {S : Type} {source : stream.Source S} {state : S}
    {codeLen : Usize} {env : metadata.Env} {entries : Usize} {data : Slice U8}
    {environment tail : List U8}
    (h : HeaderChecked source state codeLen env entries)
    (hcoherent : StreamSource.Coherent source state environment data.val tail)
    (hsize : codeLen.val = data.length) : HeaderAt data env entries := by
  rcases h with ⟨hlen, hentries, hempty⟩ |
    ⟨header, content, size, count, hread, hbyte, hlength, hend, hcount, hbound, hcountval⟩
  · refine .inl ⟨?_, hentries, hempty⟩
    simpa [hlen, Slice.length] using hsize.symm
  · have hviewbound : (core.cmp.impls.OrdUsize.min codeLen 11#usize).val ≤ data.length := by
      rw [min_val, hsize]
      exact Nat.min_le_left _ _
    have hview := (stream.read_exact.sound source state environment data.val tail hcoherent
      0#usize (core.cmp.impls.OrdUsize.min codeLen 11#usize) header (by simp) hviewbound hread).1
    have hspan := Wasm1.BytesAt.of_slice_view (by simp) hviewbound hview
    have hid : ModuleBinary.At ModuleBinary.ByteEncoding data 0#usize 10#u8 1#usize := by
      obtain ⟨bs, hb, hs⟩ := hbyte
      exact ⟨bs, hb, hspan.transport hs (by simp) (by simp)⟩
    have hlength' := hlength.of_slice_view (by simp) hviewbound hview
      (pos' := 1#usize) (next' := content) (by simp) (by simp)
    have hcount' := hcount.of_slice_view (by simp) hviewbound hview
      (pos' := content) (next' := entries) (by simp) (by simp)
    refine .inr ⟨count, ⟨content, ?_, hcount', hcountval⟩, by omega⟩
    exact ⟨1#usize, size, hid, hlength', by simpa [hsize] using hend, by simp⟩

end StreamFraming

/-- Over a coherent source, a successful `stream.read_code_header` returns the entry count of a
code section that spans the whole code region. -/
theorem stream.read_code_header.sound {S : Type} (source : stream.Source S) (state : S)
    (codeLen : Usize) (env : metadata.Env) (entries : Usize) (data : Slice U8)
    (environment tail : List U8)
    (hcoherent : StreamSource.Coherent source state environment data.val tail)
    (hsize : codeLen.val = data.length)
    (h : stream.read_code_header source state codeLen env = .ok (.Ok entries)) :
    StreamFraming.HeaderAt data env entries :=
  (stream.read_code_header.checked source state codeLen env entries h).sound hcoherent hsize

end Itasca

end
