import Itasca.Stream.Definitions
import Itasca.Results.Definitions.Streaming
import Itasca.Support.Translation
import Itasca.Stream.WorkersAndSource
import Itasca.Module.CustomTrace
import Itasca.Module.Code.Framing
import ItascaRust.Funs
import Itasca.Module.Code.FuncTyping

/-!
Proofs for Stream.

This module collects RetirementAndFraming, Totality.
Each section documents its contracts and consumers.
-/

/-! ## RetirementAndFraming -/

section

/-!
# Worker retirement and code framing

Polling and retirement preserve scheduler provenance while checking pending identities and
finishing. Entry framing and code-header acceptance supply the bounds consumed by
submission and complete driver proofs.
-/

/-! ## Retirement -/

section

/-!
# Batch retirement

`stream.retire_code_batch` polls a worker, checks its module identity, removes
its batch ID by swap-and-pop and requires `stream.StreamingBatch.finish` to succeed.
Its `spec` and `accepted` contracts record the pending-vector effect and actual
finished worker. Draining returns whenever polls return (`PollTotal`), including
when the scheduler supplies records that cause rejection.
-/

open Aeneas Aeneas.Std

namespace Itasca.Stream.Retirement

/-- The pending search finds the first matching entry or its vector's end. -/
def SearchPost (pending : alloc.vec.Vec Usize) (needle first found : Usize) : Prop :=
  first.val ≤ found.val ∧ found.val ≤ pending.length ∧
  (∀ (j : Nat) (hj : j < pending.length), first.val ≤ j → j < found.val →
    pending.val[j] ≠ needle) ∧
  (∀ h : found.val < pending.length, pending.val[found.val] = needle)

end Itasca.Stream.Retirement

namespace Itasca

/-- The pending-ID search loop returns the first position from `first` holding `needle`, or the
end of the vector. -/
@[step]
theorem stream.retire_code_batch_loop.spec (pending : alloc.vec.Vec Usize)
    (needle first : Usize) (hfirst : first.val ≤ pending.length) :
    stream.retire_code_batch_loop pending needle first ⦃ Stream.Retirement.SearchPost pending needle first ⦄ := by
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

namespace Itasca.Stream.Retirement

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

end Itasca.Stream.Retirement

namespace Itasca.Stream.Retirement

/-- A successful retirement comes from an actual poll that returned a batch of the expected module
whose `stream.StreamingBatch.finish` succeeded, and the batch ID was removed from the pending vector. -/
def Retired {V : Type} (visitor : stream.StreamingVisitor V) (moduleId : U64)
    (before : V) (pending : alloc.vec.Vec Usize) :
    (core.result.Result Unit error.Error × V × alloc.vec.Vec Usize) → Prop
  | (.Ok (), after, remaining) => ∃ batch,
      visitor.poll_code_batch before = .ok (.Ok batch, after) ∧
      batch.module_id = moduleId ∧ stream.StreamingBatch.finish batch = .ok (.Ok ()) ∧
      (batch.batch_id :: remaining.val).Perm pending.val
  | (.Err _, _, _) => True

private theorem finish_returns (batch : stream.StreamingBatch) :
    ∃ r, stream.StreamingBatch.finish batch = .ok r := by
  unfold stream.StreamingBatch.finish
  cases batch.error <;> simp only
  · split
    · split <;> exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

end Itasca.Stream.Retirement

namespace Itasca

/-- `stream.retire_code_batch` satisfies `Stream.Retirement.Retired` when the reached poll
returns. -/
@[step]
theorem stream.retire_code_batch.spec {V : Type} (visitor : stream.StreamingVisitor V)
    (moduleId : U64) (state : V) (pending : alloc.vec.Vec Usize)
    (hreturn : ∃ r, visitor.poll_code_batch state = .ok r) :
    stream.retire_code_batch visitor moduleId state pending ⦃
      Stream.Retirement.Retired visitor moduleId state pending ⦄ := by
  obtain ⟨⟨r, state'⟩, hpoll⟩ := hreturn
  unfold stream.retire_code_batch
  rw [hpoll]
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      Stream.Retirement.Retired]
  | Ok batch =>
    simp [core.result.Result.Insts.CoreOpsTry.branch]
    split
    · rename_i hmodule
      obtain ⟨found, hfind, hf⟩ := WP.spec_imp_exists
        (stream.retire_code_batch_loop.spec pending batch.batch_id 0#usize (by simp))
      rw [hfind]
      simp only [bind_ok]
      split
      · simp [Stream.Retirement.Retired]
      · rename_i hfound
        have hlt : found.val < pending.length := by have := hf.2.1; scalar_tac
        have hmatch : pending.val[found.val] = batch.batch_id := hf.2.2.2 hlt
        step
        step
        step
        simp only [alloc.vec.Vec.pop, bind_ok]
        obtain ⟨result, hfinish⟩ := Stream.Retirement.finish_returns batch
        rw [hfinish]
        simp only [bind_ok]
        cases result with
        | Err e => simp [Stream.Retirement.Retired]
        | Ok u =>
          cases u
          refine ⟨batch, hpoll, by scalar_tac, hfinish, ?_⟩
          have hlast : last.val = pending.val.length - 1 := by scalar_tac
          simpa only [index_mut_back_post, i3_post, hlast, alloc.vec.Vec.set_val_eq,
            alloc.vec.Vec.from_val, hmatch] using
            (Stream.Retirement.swap_pop_perm pending.val found.val hlt)
    · simp [Stream.Retirement.Retired]

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
      batch.module_id = moduleId ∧ stream.StreamingBatch.finish batch = .ok (.Ok ()) ∧
      (batch.batch_id :: remaining.val).Perm pending.val := by
  have hex : ∃ r, visitor.poll_code_batch state = .ok r := by
    unfold stream.retire_code_batch at h
    obtain ⟨r, hr, _⟩ := Computation.bind_ok_inv _ _ _ h
    exact ⟨r, hr⟩
  have hs := stream.retire_code_batch.spec visitor moduleId state pending hex
  simpa [h, Stream.Retirement.Retired] using hs

/-- Draining terminates under returning polls even when those polls supply foreign, unfinished or
fabricated records. An accepted drain leaves the pending vector empty. -/
@[step]
theorem stream.retire_all_code_batches.spec {V : Type} (visitor : stream.StreamingVisitor V)
    (moduleId : U64) (state : V) (pending : alloc.vec.Vec Usize)
    (htotal : Stream.Retirement.PollTotal visitor) :
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
    (htotal : Stream.Retirement.PollTotal visitor) :
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

Consequences of the scheduler premises `Stream.Scheduler.CallbacksTotal` and
`Stream.Scheduler.Provenance`, defined in `Itasca/Results/Definitions/Streaming`. `retire_sound`
and `drain_sound` show that successful retirement and draining produce `Stream.Scheduler.Completed`
certificates (exact byte coverage and typed entries) for every pending issued batch.
-/

open Aeneas Aeneas.Std

namespace Itasca.Stream.Scheduler
/-- A completed batch has exact byte coverage and ordered entry certificates. This is derived at
successful retirement and is never a premise on polls. -/
def Completed (issued : Stream.Batch.Issued) : Prop :=
  ∃ entries, entries.length = issued.num_funcs.val ∧
    Binary.Rep (CodeEntry.CodeEncoding) entries issued.code.val ∧
    Module.Code.EntriesTyped issued.env issued.first_func.val entries

theorem Provenance.environment_preserves {V : Type} {visitor : stream.StreamingVisitor V}
    {Tracks : U64 → List Stream.Batch.Issued → V → Prop} (hp : Provenance visitor Tracks)
    (id : U64) (history : List Stream.Batch.Issued) (data : Slice U8)
    (v v' : V) (env : metadata.ModuleMetadata metadata.CodeMetadata) (next : Usize)
    (h : metadata.validate_env_with visitor.metadataModuleVisitorInst data v = .ok (.Ok (env, next), v')) :
    Tracks id history v → Tracks id history v' :=
  metadata.validate_env_with.accepted_invariant _ _ (hp.custom id history) data v env next v' h

theorem Provenance.tail_preserves {V : Type} {visitor : stream.StreamingVisitor V}
    {Tracks : U64 → List Stream.Batch.Issued → V → Prop} (hp : Provenance visitor Tracks)
    (id : U64) (history : List Stream.Batch.Issued) (data : Slice U8) (pos : Usize)
    (v v' : V) (env : metadata.CodeMetadata) (tail : (alloc.vec.Vec metadata.Data))
    (h : metadata.validate_tail_with visitor.metadataModuleVisitorInst data pos env v = .ok (.Ok tail, v')) :
    Tracks id history v → Tracks id history v' :=
  metadata.validate_tail_with.accepted_invariant _ _ (hp.custom id history) data pos env v tail v' h

/-- After a successful retirement, every historical issued batch matching the removed pending ID
is completed, and provenance is preserved. Polls need not be replay-free. -/
theorem retire_sound {V : Type} (visitor : stream.StreamingVisitor V)
    (Tracks : U64 → List Stream.Batch.Issued → V → Prop) (hp : Provenance visitor Tracks)
    (id : U64) (history : List Stream.Batch.Issued) (v v' : V)
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

end Itasca.Stream.Scheduler

open Aeneas Aeneas.Std

namespace Itasca.Stream.Scheduler
/-- An accepted drain empties the pending vector and completes every historical issued batch
whose ID was pending, while provenance is preserved across every poll. -/
theorem drain_sound {V : Type} (visitor : stream.StreamingVisitor V)
    (Tracks : U64 → List Stream.Batch.Issued → V → Prop) (hp : Provenance visitor Tracks)
    (id : U64) (history : List Stream.Batch.Issued) (v v' : V)
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
      obtain ⟨⟨r, next, rest⟩, hretire, hrest⟩ := Computation.bind_ok_inv _ _ _ h
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

end Itasca.Stream.Scheduler

end

/-! ## EntryFrame -/

section

/-!
# Code entry frames

`Stream.Framing.EntryFrame` describes the `stream.StreamingEntry` returned by `stream.frame_entry`: its
declared byte extent (`Module.Code.Extent`) shifted by the batch offset into absolute coordinates.
`stream.frame_entry.sound` and `.complete` relate the function to this predicate. Completeness
needs only that the shifted end stays within the module cap.
-/

open Aeneas Aeneas.Std

namespace Itasca.Stream.Framing

/-- A frame records the entry's declared byte extent and the corresponding
absolute offsets. It does not certify local declarations or instructions. -/
def EntryFrame (data : Slice U8) (pos index offset : Usize)
    (entry : stream.StreamingEntry) : Prop :=
  ∃ content finish, Module.Code.Extent data pos content finish ∧
    entry.index = index ∧ entry.start.val = offset.val + pos.val ∧
    entry.contents.val = offset.val + content.val ∧
    entry.end.val = offset.val + finish.val ∧
    entry.end.val ≤ limits.MAX_MODULE_BYTES.val

end Itasca.Stream.Framing

namespace Itasca

@[step]
theorem stream.frame_entry.spec (data : Slice U8) (pos index offset : Usize) :
    stream.frame_entry data pos index offset ⦃ r => match r with
      | .Ok entry => Stream.Framing.EntryFrame data pos index offset entry
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


end Itasca

end

/-! ## DriverRun -/

section

/-!
# Accepted driver runs

An accepted call to `stream.validate_streaming` yields a `Stream.Run.Accepted` witness.
It records the decoded prefix and the calls that read the code header, configure the visitor,
submit batches, decode data segments and drain outstanding work. Its publication equality
identifies the returned module with the shared prefix updated with those segments.
-/

open Aeneas Aeneas.Std

namespace Itasca

set_option maxHeartbeats 1000000 in
/-- Recover the source reads, worker calls and published metadata from a successful driver run. -/
theorem stream.validate_streaming.accepted {S V : Type} (source : stream.StreamingSource S)
    (visitor : stream.StreamingVisitor V) (id : U64) (state : S)
    (v v' : V) (published : metadata.ModuleMetadata metadata.CodeMetadata)
    (h : stream.validate_streaming source visitor id state v = .ok (.Ok published, v')) :
    Nonempty (Stream.Run.Accepted source visitor id state v v' published) := by
  unfold stream.validate_streaming at h
  obtain ⟨r, henv, h⟩ := Computation.bind_ok_inv _ _ _ h
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
  | Ok environment =>
    simp [core.result.Result.Insts.CoreOpsTry.branch] at h
    obtain ⟨r, hbound, h⟩ := Computation.bind_ok_inv _ _ _ h
    cases r with
    | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
    | Ok envLen =>
      simp [core.result.Result.Insts.CoreOpsTry.branch] at h
      obtain ⟨region, hregion, h⟩ := Computation.bind_ok_inv _ _ _ h
      obtain ⟨⟨r, decoded⟩, hdecode, h⟩ := Computation.bind_ok_inv _ _ _ h
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
      | Ok pair =>
        obtain ⟨prefixEnv, envEnd⟩ := pair
        simp at h
        split at h
        swap
        · simp at h
        · rename_i heq
          have same : envEnd = envLen := by apply UScalar.eq_of_val_eq; simpa using heq
          subst envEnd
          have sharing : metadata.ModuleMetadataCodeMetadata.share prefixEnv = .ok prefixEnv := by
              obtain ⟨x, hx, same⟩ := WP.spec_imp_exists (metadata.ModuleMetadataCodeMetadata.share.spec prefixEnv)
              simpa [same] using hx
          simp only [sharing, bind_ok, alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref] at h
          obtain ⟨codeLen, hlen, h⟩ := Computation.bind_ok_inv _ _ _ h
          obtain ⟨r, hcodeBound, h⟩ := Computation.bind_ok_inv _ _ _ h
          cases r with
          | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
          | Ok codeEnd =>
            simp [core.result.Result.Insts.CoreOpsTry.branch] at h
            obtain ⟨r, hheader, h⟩ := Computation.bind_ok_inv _ _ _ h
            cases r with
            | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
            | Ok entries =>
              simp [core.result.Result.Insts.CoreOpsTry.branch] at h
              obtain ⟨⟨r, configured⟩, hconfig, h⟩ := Computation.bind_ok_inv _ _ _ h
              cases r with
              | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
              | Ok config =>
                simp [core.result.Result.Insts.CoreOpsTry.branch] at h
                split at h
                · simp at h
                · rename_i hbytes
                  split at h
                  · simp at h
                  · rename_i hbatches
                    obtain ⟨⟨r, submitted⟩, hsubmit, h⟩ := Computation.bind_ok_inv _ _ _ h
                    cases r with
                    | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
                        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
                    | Ok pending =>
                      simp [core.result.Result.Insts.CoreOpsTry.branch] at h
                      obtain ⟨⟨r, ended⟩, hend, h⟩ := Computation.bind_ok_inv _ _ _ h
                      cases r with
                      | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
                          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
                      | Ok u =>
                        simp [core.result.Result.Insts.CoreOpsTry.branch] at h
                        cases u
                        obtain ⟨r, htail, h⟩ := Computation.bind_ok_inv _ _ _ h
                        cases r with
                        | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
                            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
                        | Ok tailBytes =>
                          simp [core.result.Result.Insts.CoreOpsTry.branch] at h
                          obtain ⟨r, hmodule, h⟩ := Computation.bind_ok_inv _ _ _ h
                          cases r with
                          | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
                              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
                          | Ok moduleEnd =>
                            simp [core.result.Result.Insts.CoreOpsTry.branch] at h
                            obtain ⟨tailRegion, htailRegion, h⟩ := Computation.bind_ok_inv _ _ _ h
                            obtain ⟨⟨r, decodedTail⟩, hsegments, h⟩ := Computation.bind_ok_inv _ _ _ h
                            cases r with
                            | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
                                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
                            | Ok segments =>
                              simp [core.result.Result.Insts.CoreOpsTry.branch] at h
                              obtain ⟨⟨r, after, remaining⟩, hdrain, h⟩ := Computation.bind_ok_inv _ _ _ h
                              cases r with
                              | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
                                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
                              | Ok u =>
                                simp [core.result.Result.Insts.CoreOpsTry.branch] at h
                                cases u
                                obtain ⟨rfl, rfl⟩ := h
                                exact ⟨⟨environment, envLen, prefixEnv, region, decoded, henv, hbound, hregion, hdecode,
                                  ⟨codeLen, codeEnd, entries, config, configured, pending, submitted, ended, tailBytes,
                                   moduleEnd, tailRegion, segments, decodedTail, remaining, hlen, hcodeBound, hheader,
                                   hconfig, hbytes, hbatches, hsubmit, hend, htail, hmodule, htailRegion, hsegments, hdrain⟩, rfl⟩⟩

end Itasca

end

/-! ## Header -/

section

/-!
# Code section header

Soundness and termination for `stream.read_code_header`, which reads at most the first 11 bytes of
the code region and checks the section ID, the section size and the function count against the
environment. `Stream.Framing.HeaderChecked` describes what the driver observed through the source,
and `Stream.Framing.HeaderAt` is the resulting fact about the coherent code region, with an absent
region and a present zero-entry section as separate cases. Completeness is in
`Stream/DriverRegions`.
-/

open Aeneas Aeneas.Std

namespace Itasca

namespace Stream.Framing

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

end Stream.Framing

/-- `stream.read_code_header` either errors or returns the entry count of a checked header,
provided the reached code read returns. -/
theorem stream.read_code_header.spec {S : Type} (source : stream.StreamingSource S) (state : S)
    (codeLen : Usize) (env : metadata.CodeMetadata)
    (imports : env.num_imported_funcs.val ≤ env.funcs.val.length)
    (hreturn : codeLen ≠ 0#usize → ∃ r, source.code state 0#usize
      (core.cmp.impls.OrdUsize.min codeLen 11#usize) = .ok r) :
    stream.read_code_header source state codeLen env ⦃ r => match r with
      | .Ok entries => Stream.Framing.HeaderChecked source state codeLen env entries
      | .Err _ => True ⦄ := by
  obtain ⟨num, call, countEq⟩ := WP.spec_imp_exists (metadata.CodeMetadata.num_func_defs.spec env imports)
  have numEq : (Translation.Environment.definedTypeIndices env).length = num.val := by
    simp [Translation.Environment.definedTypeIndices, countEq]
  unfold stream.read_code_header
  split
  · rename_i hzero
    simp only [call, bind_ok]
    split
    · simp
    · rename_i empty
      simp only [WP.spec_ok]
      exact .inl ⟨hzero, rfl, List.length_eq_zero_iff.mp (by scalar_tac)⟩
  · rename_i hnonzero
    rw [Stream.Framing.header_limit]
    simp only [bind_ok, lift]
    obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (stream.read_exact.spec source state
      0#usize (core.cmp.impls.OrdUsize.min codeLen 11#usize) (by simp) (hreturn hnonzero))
    rw [hr]
    cases r with
    | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok header =>
      have hlen : header.length = Nat.min codeLen.val 11 := by
        simpa [Stream.Framing.min_val] using hp.2
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
        have hbyte : Binary.At Binary.ByteEncoding header 0#usize 10#u8 1#usize :=
          ⟨[10#u8], rfl, Body.Scalar.BytesAt.byte header 0#usize 1#usize 10#u8 hpositive
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
                  simp [call]
                  split
                  · simp
                  · rename_i hentries
                    split
                    · rename_i hcountlen
                      simp only [WP.spec_ok]
                      change ¬ entries.val > finish.val at hentries
                      change countLen.val = num.val at hcountlen
                      exact .inr ⟨header, content, size, count, hr, hbyte, hsize, hend,
                        hcount, by omega, by omega⟩
                    · simp
      · simp

/-- Acceptance itself supplies the reached source callback. No premise is
imposed on unrelated or unexecuted source calls. -/
theorem stream.read_code_header.checked {S : Type} (source : stream.StreamingSource S) (state : S)
    (codeLen : Usize) (env : metadata.CodeMetadata) (entries : Usize)
    (imports : env.num_imported_funcs.val ≤ env.funcs.val.length)
    (h : stream.read_code_header source state codeLen env = .ok (.Ok entries)) :
    Stream.Framing.HeaderChecked source state codeLen env entries := by
  have hreturn : codeLen ≠ 0#usize → ∃ r, source.code state 0#usize
      (core.cmp.impls.OrdUsize.min codeLen 11#usize) = .ok r := by
    intro hnonzero
    unfold stream.read_code_header at h
    rw [if_neg hnonzero, Stream.Framing.header_limit] at h
    simp only [bind_ok, lift] at h
    obtain ⟨r, hr, hrest⟩ := Computation.bind_ok_inv _ _ _ h
    cases r with
    | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at hrest
    | Ok header =>
      exact ⟨.Ok header, (stream.read_exact.accepted source state _ _ header (by simp) hr).1⟩
  have hs := stream.read_code_header.spec source state codeLen env imports hreturn
  simpa [h] using hs

namespace Stream.Framing

theorem HeaderChecked.sound {S : Type} {source : stream.StreamingSource S} {state : S}
    {codeLen : Usize} {env : metadata.CodeMetadata} {entries : Usize} {data : Slice U8}
    {environment tail : List U8}
    (h : HeaderChecked source state codeLen env entries)
    (hcoherent : Stream.Source.Coherent source state environment data.val tail)
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
    have hspan := Body.Scalar.BytesAt.of_slice_view (by simp) hviewbound hview
    have hid : Binary.At Binary.ByteEncoding data 0#usize 10#u8 1#usize := by
      obtain ⟨bs, hb, hs⟩ := hbyte
      exact ⟨bs, hb, hspan.transport hs (by simp) (by simp)⟩
    have hlength' := hlength.of_slice_view (by simp) hviewbound hview
      (pos' := 1#usize) (next' := content) (by simp) (by simp)
    have hcount' := hcount.of_slice_view (by simp) hviewbound hview
      (pos' := content) (next' := entries) (by simp) (by simp)
    refine .inr ⟨count, ⟨content, ?_, hcount', hcountval⟩, by omega⟩
    exact ⟨1#usize, size, hid, hlength', by simpa [hsize] using hend, by simp⟩

end Stream.Framing

/-- Over a coherent source, a successful `stream.read_code_header` returns the entry count of a
code section that spans the whole code region. -/
theorem stream.read_code_header.sound {S : Type} (source : stream.StreamingSource S) (state : S)
    (codeLen : Usize) (env : metadata.CodeMetadata) (entries : Usize) (data : Slice U8)
    (environment tail : List U8)
    (hcoherent : Stream.Source.Coherent source state environment data.val tail)
    (hsize : codeLen.val = data.length)
    (imports : env.num_imported_funcs.val ≤ env.funcs.val.length)
    (h : stream.read_code_header source state codeLen env = .ok (.Ok entries)) :
    Stream.Framing.HeaderAt data env entries :=
  (stream.read_code_header.checked source state codeLen env entries imports h).sound hcoherent hsize

end Itasca

end


/-! ## Totality -/

section

/-!
# Normal return of streaming orchestration

Batch framing, submission, remaining-region validation and code-region scanning return
under their callback premises. Malformed bytes, Rust errors and arbitrary returned worker
records remain permitted.
-/

/-! ## FramingTotal -/

section

/-!
# Batch framing termination

Termination of `stream.get_next_batch` and its loop `stream.get_next_batch_loop`, which frame code
entries until the byte threshold is reached or the entries run out. `Stream.Framing.BatchInvariant`
holds along the loop and `Stream.Framing.BatchPost` states what a successful framing returns: a
nonempty range of entries ending within the code region. Termination needs the source callbacks to
return (`Stream.Source.CallbacksTotal`) and the code region to respect the module cap.
-/

open Aeneas Aeneas.Std

namespace Itasca.Stream.Framing

/-- Arithmetic facts maintained by the actual batch-framing loop. The byte
budget counts declared entry contents, including locals, but not size prefixes. -/
def BatchInvariant (codeLen start first num threshold : Usize)
    (pos func bytes : Usize) (done : Bool) : Prop :=
  start.val ≤ pos.val ∧ pos.val ≤ codeLen.val ∧
  first.val ≤ func.val ∧ func.val ≤ num.val ∧ bytes.val ≤ pos.val - start.val ∧
  (func = first → pos = start ∧ bytes = 0#usize ∧ done = false) ∧
  (done = false → func ≠ first → bytes.val < threshold.val)

/-- A successful framing returns the end offset of a nonempty batch and the index after its last
entry. Errors are unconstrained. -/
def BatchPost (codeLen start first num : Usize) :
    core.result.Result (Usize × Usize) error.Error → Prop
  | .Ok (finish, next) => start.val < finish.val ∧ finish.val ≤ codeLen.val ∧
      first.val < next.val ∧ next.val ≤ num.val
  | .Err _ => True

private theorem advance {codeLen start first num threshold q i b finish j new : Usize}
    {prefixLen len : Nat}
    (hstart : start.val ≤ q.val) (hfirst : first.val ≤ i.val)
    (himore : i.val < num.val) (hb : b.val ≤ q.val - start.val)
    (hprefix : 0 < prefixLen) (hend : finish.val = q.val + prefixLen + len)
    (hbound : finish.val ≤ codeLen.val) (hcount : j.val = i.val + 1)
    (hbytes : new.val = b.val + len) :
    (BatchInvariant codeLen start first num threshold finish j new (decide (new ≥ threshold)) ∧
      (first.val < j.val → start.val < finish.val)) ∧
      (2 * (num.val - j.val) + if decide (new ≥ threshold) then 0 else 1) <
        2 * (num.val - i.val) + 1 := by
  have hj : first.val < j.val := by omega
  have hne : j ≠ first := by intro he; have := congrArg UScalar.val he; omega
  refine ⟨⟨⟨by omega, hbound, by omega, by omega, by omega, ?_, ?_⟩, ?_⟩, ?_⟩
  · intro he; exact False.elim (hne he)
  · intro hz _
    have : ¬ new.val ≥ threshold.val := by simpa using hz
    omega
  · intro _; omega
  · split <;> omega

end Itasca.Stream.Framing

namespace Itasca

/-- The framing loop returns, and its result satisfies `Stream.Framing.BatchPost`, from any state
satisfying `Stream.Framing.BatchInvariant`. -/
theorem stream.get_next_batch_loop.total_spec {S : Type} (source : stream.StreamingSource S) (state : S)
    (codeLen start first num threshold pos func bytes : Usize) (done : Bool)
    (htotal : Stream.Source.CallbacksTotal source state)
    (hcap : codeLen.val ≤ limits.MAX_MODULE_BYTES.val)
    (hmore : first.val < num.val)
    (hinv : Stream.Framing.BatchInvariant codeLen start first num threshold pos func bytes done)
    (hprogress : first.val < func.val → start.val < pos.val) :
    stream.get_next_batch_loop source state codeLen first num threshold pos func bytes done
      ⦃ Stream.Framing.BatchPost codeLen start first num ⦄ := by
  unfold stream.get_next_batch_loop
  apply loop.spec_decr_nat
    (fun s => 2 * (num.val - s.2.1.val) + if s.2.2.2 then 0 else 1)
    (fun s => Stream.Framing.BatchInvariant codeLen start first num threshold s.1 s.2.1 s.2.2.1 s.2.2.2 ∧
      (first.val < s.2.1.val → start.val < s.1.val))
  · rintro ⟨q, i, b, stopped⟩ ⟨hq, hprogress⟩
    obtain ⟨hstart, hq, hfirst, hi, hb, hinitial, hbudget⟩ := hq
    dsimp only at hstart hq hfirst hi hb hinitial hbudget hprogress
    unfold stream.get_next_batch_loop.body
    dsimp only
    split
    · rename_i himore
      split
      · rename_i hstop
        have hne : i ≠ first := by intro he; have := (hinitial he).2.2; simp_all
        have hlt : first.val < i.val := by
          have : first.val ≠ i.val := by intro he; apply hne; exact UScalar.eq_of_val_eq he.symm
          omega
        simpa [Stream.Framing.BatchPost] using ⟨hprogress hlt, hq, hlt, hi⟩
      · rename_i hnotstop
        have hfalse : stopped = false := by cases stopped <;> simp_all
        have hiroom : i.val + 1 ≤ Usize.max := by scalar_tac
        have hroom : q.val + limits.MAX_LEB_BYTES.val ≤ Usize.max := by
          have := Module.Code.module_room
          simp only [limits.MAX_LEB_BYTES]
          scalar_tac
        obtain ⟨need, hneed, hneedval⟩ := WP.spec_imp_exists
          (UScalar.add_spec (x := q) (y := limits.MAX_LEB_BYTES) (by scalar_tac))
        rw [hneed]
        simp only [bind_ok, lift]
        have hviewend : (core.cmp.impls.OrdUsize.min codeLen need).val =
            Nat.min codeLen.val (q.val + 5) := by
          rw [Stream.Framing.min_val, hneedval]
          simp [limits.MAX_LEB_BYTES]
        have horder : q.val ≤ (core.cmp.impls.OrdUsize.min codeLen need).val := by
          rw [hviewend]
          exact Nat.le_min.mpr ⟨hq, by omega⟩
        obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (stream.read_exact.spec source state q
          (core.cmp.impls.OrdUsize.min codeLen need) horder (htotal.code_returns _ _))
        rw [hr]
        cases r with
        | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, Stream.Framing.BatchPost]
        | Ok view =>
          simp [core.result.Result.Insts.CoreOpsTry.branch]
          obtain ⟨r, hl, hlp⟩ := WP.spec_imp_exists (stream.read_len.spec view 0#usize)
          rw [hl]
          cases r with
          | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, Stream.Framing.BatchPost]
          | Ok pair =>
            obtain ⟨len, prefixLen⟩ := pair
            obtain ⟨size, hlen, hdecoded⟩ := hlp
            have hprefix := hdecoded.span
            have hprefixpos : 0 < prefixLen.val := by simpa using hprefix.1
            simp
            split
            · rename_i hequal
              have heqi : i = first := UScalar.eq_of_val_eq hequal
              have hbzero : b = 0#usize := (hinitial heqi).2.1
              obtain ⟨r, hc, hcp⟩ := WP.spec_imp_exists (limits.add_offset.spec q prefixLen)
              rw [hc]
              cases r with
              | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, Stream.Framing.BatchPost]
              | Ok content =>
                simp
                obtain ⟨r, hf, hfp⟩ := WP.spec_imp_exists (limits.add_offset.spec content len)
                rw [hf]
                cases r with
                | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, Stream.Framing.BatchPost]
                | Ok finish =>
                  simp
                  split
                  · simp [Stream.Framing.BatchPost]
                  · rename_i hfinish
                    have hfbound : finish.val ≤ codeLen.val := by scalar_tac
                    have hbroom : b.val + len.val ≤ Usize.max := by
                      simp only [hbzero]
                      scalar_tac
                    step
                    step
                    have ha := Stream.Framing.advance (num := num) (threshold := threshold)
                      (j := func1) (new := batch_bytes1) (len := len.val)
                      hstart hfirst (by exact himore) hb hprefixpos
                      (by have := hcp.1; have := hfp.1; omega) hfbound
                      func1_post batch_bytes1_post
                    simpa [and_assoc] using ha
            · rename_i hnotequal
              have hne : i ≠ first := by intro he; simp [he] at hnotequal
              have hbbound := hbudget hfalse hne
              step
              split
              · simp only [WP.spec_ok, Stream.Framing.BatchInvariant]
                refine ⟨⟨hstart, hq, hfirst, hi, hb, ?_, ?_⟩, hprogress, ?_⟩
                · intro he; exact False.elim (hne he)
                · intro he; cases he
                · simp
              · obtain ⟨r, hc, hcp⟩ := WP.spec_imp_exists (limits.add_offset.spec q prefixLen)
                rw [hc]
                cases r with
                | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, Stream.Framing.BatchPost]
                | Ok content =>
                  simp
                  obtain ⟨r, hf, hfp⟩ := WP.spec_imp_exists (limits.add_offset.spec content len)
                  rw [hf]
                  cases r with
                  | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, Stream.Framing.BatchPost]
                  | Ok finish =>
                    simp
                    split
                    · simp [Stream.Framing.BatchPost]
                    · rename_i hfinish
                      have hfbound : finish.val ≤ codeLen.val := by scalar_tac
                      have hbroom : b.val + len.val ≤ Usize.max := by
                        have hfmax := hfp.2
                        have := Module.Code.module_room
                        scalar_tac
                      step
                      step
                      have ha := Stream.Framing.advance (num := num) (threshold := threshold)
                        (j := func1) (new := batch_bytes1) (len := len.val)
                        hstart hfirst (by exact himore) hb hprefixpos
                        (by have := hcp.1; have := hfp.1; omega) hfbound
                        func1_post batch_bytes1_post
                      simpa [and_assoc] using ha
    · rename_i hstop
      have hdone : i.val = num.val := by scalar_tac
      simpa [Stream.Framing.BatchPost] using ⟨hprogress (by omega), hq, (by omega : first.val < i.val), hi⟩
  · exact ⟨hinv, hprogress⟩

/-- `stream.get_next_batch` returns and satisfies `Stream.Framing.BatchPost` when the source
callbacks return and the code region respects the module cap. -/
theorem stream.get_next_batch.spec {S : Type} (source : stream.StreamingSource S) (state : S)
    (codeLen start first num threshold : Usize)
    (htotal : Stream.Source.CallbacksTotal source state)
    (hcap : codeLen.val ≤ limits.MAX_MODULE_BYTES.val)
    (hstart : start.val ≤ codeLen.val) (hmore : first.val < num.val) :
    stream.get_next_batch source state codeLen start first num threshold
      ⦃ Stream.Framing.BatchPost codeLen start first num ⦄ := by
  apply stream.get_next_batch_loop.total_spec source state codeLen start first num threshold
    start first 0#usize false htotal hcap hmore
  · simp [Stream.Framing.BatchInvariant, hstart]
    omega
  · omega

end Itasca

end

/-! ## SubmissionTotal -/

section

/-!
# Submission termination

Termination of `stream.submit_code_batches` and its loop, which frame code batches, issue them to
the scheduler through `submit_code_batch`, and retire a batch whenever the pending vector is full.
`Stream.Submission.Invariant` bounds the cursors and the pending vector, and every iteration
advances the function cursor. Termination needs the source and scheduler callbacks to return
(`Stream.Source.CallbacksTotal`, `Stream.Scheduler.CallbacksTotal`).
-/

open Aeneas Aeneas.Std

namespace Itasca.Stream.Submission
/-- Both outstanding IDs and issued batch IDs are bounded by the function
cursor; every successful submission advances that cursor. -/
def Invariant (codeLen num max : Usize) (pending : alloc.vec.Vec Usize)
    (pos func batchId : Usize) : Prop :=
  pos.val ≤ codeLen.val ∧ func.val ≤ num.val ∧ batchId.val ≤ func.val ∧
    pending.length ≤ batchId.val ∧ pending.length ≤ max.val

/-- A returned pending vector stays within the configured maximum. Errors are unconstrained. -/
def Post (max : Usize) : (core.result.Result (alloc.vec.Vec Usize) error.Error × V) → Prop
  | (.Ok remaining, _) => remaining.length ≤ max.val
  | (.Err _, _) => True

/-- The loop continuation after its optional retirement, written as the extracted subexpression
so that both generated branches share one proof. -/
private theorem resume {S V : Type} (source : stream.StreamingSource S) (visitor : stream.StreamingVisitor V)
    (state : S) (moduleId : U64) (env : metadata.CodeMetadata) (codeLen : Usize) (config : stream.StreamingConfig)
    (v : V) (pending : alloc.vec.Vec Usize) (pos func batchId num : Usize)
    (hs : Stream.Source.CallbacksTotal source state) (hv : Stream.Scheduler.CallbacksTotal visitor )
    (henv : CodeEntry.Bounds env) (hnum : num.val = (Translation.Environment.definedTypeIndices env).length)
    (hcap : codeLen.val ≤ limits.MAX_MODULE_BYTES.val)
    (hpos : pos.val ≤ codeLen.val) (hfunc : func.val < num.val)
    (hbatch : batchId.val ≤ func.val) (hpending : pending.length ≤ batchId.val)
    (hroom : pending.length < config.max_batches.val) :
    (do
      let r ← stream.get_next_batch source state codeLen pos func num config.batch_bytes
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val =>
        let (finish, next) := val
        let r1 ← stream.read_exact source state pos finish
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue bytes =>
          let pending1 ← alloc.vec.Vec.push pending batchId
          let count ← next - func
          let (r2, v') ← visitor.submit_code_batch v
            { module_id := moduleId, batch_id := batchId, env := env, code := bytes,
              code_offset := pos, first_func := func, num_funcs := count,
              num_dispatched := 0#usize, dispatch_end := 0#usize,
              num_validated := 0#usize, validated_end := 0#usize, error := none }
          let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
          match cf2 with
          | core.ops.control_flow.ControlFlow.Continue _ =>
            let nextId ← batchId + 1#usize
            Result.ok (ControlFlow.cont (v', pending1, finish, next, nextId))
          | core.ops.control_flow.ControlFlow.Break residual =>
            let r3 ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              (alloc.vec.Vec Usize) (core.convert.FromSame error.Error) residual
            Result.ok (ControlFlow.done (r3, v'))
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r2 ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            (alloc.vec.Vec Usize) (core.convert.FromSame error.Error) residual
          Result.ok (ControlFlow.done (r2, v))
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r1 ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          (alloc.vec.Vec Usize) (core.convert.FromSame error.Error) residual
        Result.ok (ControlFlow.done (r1, v))) ⦃ out => match out with
      | .done result => Post config.max_batches result
      | .cont (_, pending', pos', func', batchId') =>
        Invariant codeLen num config.max_batches pending' pos' func' batchId' ∧
          num.val - func'.val < num.val - func.val ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists
    (stream.get_next_batch.spec source state codeLen pos func num config.batch_bytes hs hcap hpos hfunc)
  rw [hr]
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, Post]
  | Ok pair =>
    obtain ⟨finish, next⟩ := pair
    obtain ⟨hposnext, hfinish, hnextmore, hnextbound⟩ := hp
    simp [core.result.Result.Insts.CoreOpsTry.branch]
    obtain ⟨r, hread, hreadp⟩ := WP.spec_imp_exists
      (stream.read_exact.spec source state pos finish (by omega) (hs.code_returns _ _))
    rw [hread]
    cases r with
    | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, Post]
    | Ok bytes =>
      have hlen := hreadp.2
      have hnumMax : num.val ≤ Usize.max := by scalar_tac
      simp
      step
      step
      let issued : Stream.Batch.Issued := ⟨moduleId, batchId, env, bytes, pos, func, count⟩
      have hb : issued.Bounded := by
        dsimp [issued, Stream.Batch.Issued.Bounded]
        scalar_tac
      obtain ⟨⟨reply, v'⟩, hsubmit⟩ := hv.submit v issued hb henv
      dsimp only [issued, Stream.Batch.Issued.seed] at hsubmit
      rw [hsubmit]
      cases reply with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, Post]
      | Ok u =>
        cases u
        simp
        step
        simp only [Invariant]
        scalar_tac

end Itasca.Stream.Submission

namespace Itasca
private theorem submit_body_total {S V : Type} (source : stream.StreamingSource S)
    (visitor : stream.StreamingVisitor V) (moduleId : U64) (state : S)
    (env : metadata.CodeMetadata) (codeLen : Usize) (config : stream.StreamingConfig) (num : Usize)
    (v : V) (pending : alloc.vec.Vec Usize) (pos func batchId : Usize)
    (hs : Stream.Source.CallbacksTotal source state) (hv : Stream.Scheduler.CallbacksTotal visitor )
    (henv : CodeEntry.Bounds env) (hnum : num.val = (Translation.Environment.definedTypeIndices env).length)
    (hcap : codeLen.val ≤ limits.MAX_MODULE_BYTES.val)
    (hinv : Stream.Submission.Invariant codeLen num config.max_batches pending pos func batchId) :
    stream.submit_code_batches_loop.body source visitor moduleId state env
      codeLen config num v pending pos func batchId ⦃ out => match out with
      | .done result => Stream.Submission.Post config.max_batches result
      | .cont (_, pending', pos', func', batchId') =>
        Stream.Submission.Invariant codeLen num config.max_batches pending' pos' func' batchId' ∧
          num.val - func'.val < num.val - func.val ⦄ := by
  obtain ⟨hpos, hfunc, hbatch, hpending, hmax⟩ := hinv
  unfold stream.submit_code_batches_loop.body
  by_cases hmore : func < num
  · rw [if_pos hmore]
    by_cases hfull : alloc.vec.Vec.len pending ≥ config.max_batches
    · rw [if_pos hfull]
      obtain ⟨⟨r, v', remaining⟩, hr, hp⟩ := WP.spec_imp_exists
        (stream.retire_code_batch.spec visitor moduleId v pending (hv.poll v))
      rw [hr]
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          Stream.Submission.Post]
      | Ok u =>
        cases u
        obtain ⟨batch, _, _, _, hperm⟩ := hp
        have hlen : remaining.length + 1 = pending.length := by
          simpa [alloc.vec.Vec.length] using hperm.length_eq
        have hresume :=
          (Stream.Submission.resume source visitor state moduleId env codeLen config v' remaining
            pos func batchId num hs hv henv hnum hcap hpos (by scalar_tac) hbatch
            (by omega) (by scalar_tac))
        simp [core.result.Result.Insts.CoreOpsTry.branch] at hresume ⊢
        simp only [stream.share_code, bind_ok]
        convert hresume using 1 <;> rfl
    · rw [if_neg hfull]
      simp only [stream.share_code, bind_ok]
      exact Stream.Submission.resume source visitor state moduleId env codeLen config v pending
        pos func batchId num hs hv henv hnum hcap hpos (by scalar_tac) hbatch hpending (by scalar_tac)
  · rw [if_neg hmore]
    split
    · simp [Stream.Submission.Post]
    · simpa [Stream.Submission.Post] using hmax

/-- Submission terminates because each framed batch contains at least one function. The pending
vector stays within the configured maximum. -/
theorem stream.submit_code_batches_loop.spec {S V : Type} (source : stream.StreamingSource S)
    (visitor : stream.StreamingVisitor V) (moduleId : U64) (state : S)
    (env : metadata.CodeMetadata) (codeLen : Usize) (config : stream.StreamingConfig) (v : V)
    (pending : alloc.vec.Vec Usize) (pos func batchId num : Usize)
    (hs : Stream.Source.CallbacksTotal source state) (hv : Stream.Scheduler.CallbacksTotal visitor )
    (henv : CodeEntry.Bounds env) (hnum : num.val = (Translation.Environment.definedTypeIndices env).length)
    (hcap : codeLen.val ≤ limits.MAX_MODULE_BYTES.val)
    (hinv : Stream.Submission.Invariant codeLen num config.max_batches pending pos func batchId) :
    stream.submit_code_batches_loop source visitor moduleId state env
      codeLen config v pending pos func batchId num ⦃ Stream.Submission.Post config.max_batches ⦄ := by
  unfold stream.submit_code_batches_loop
  apply loop.spec_decr_nat (fun s => num.val - s.2.2.2.1.val)
    (fun s => Stream.Submission.Invariant codeLen num config.max_batches s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2)
  · rintro ⟨v', pending', pos', func', batchId'⟩ h
    apply WP.spec_mono (submit_body_total source visitor moduleId state env codeLen config num
      v' pending' pos' func' batchId' hs hv henv hnum hcap h)
    intro out hout
    cases out with
    | done result => exact hout
    | cont next => rcases next with ⟨_, _, _, _, _⟩; exact hout
  · exact hinv

/-- `stream.submit_code_batches` returns and keeps its pending vector within the configured
maximum, when the source and scheduler callbacks return. -/
@[step]
theorem stream.submit_code_batches.spec {S V : Type} (source : stream.StreamingSource S)
    (visitor : stream.StreamingVisitor V) (moduleId : U64) (state : S)
    (env : metadata.CodeMetadata) (codeLen pos : Usize) (config : stream.StreamingConfig) (v : V)
    (hs : Stream.Source.CallbacksTotal source state) (hv : Stream.Scheduler.CallbacksTotal visitor )
    (henv : CodeEntry.Bounds env) (hcap : codeLen.val ≤ limits.MAX_MODULE_BYTES.val)
    (hpos : pos.val ≤ codeLen.val) :
    stream.submit_code_batches source visitor moduleId state env codeLen pos config v
      ⦃ Stream.Submission.Post config.max_batches ⦄ := by
  obtain ⟨num, call, hn⟩ := WP.spec_imp_exists (metadata.CodeMetadata.num_func_defs.spec env henv.1)
  simp only [stream.submit_code_batches, alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref, call, bind_ok]
  apply stream.submit_code_batches_loop.spec source visitor moduleId state env codeLen config v
    (alloc.vec.Vec.new Usize) pos 0#usize 0#usize num
    hs hv henv (by simp [Translation.Environment.definedTypeIndices, hn]) hcap
  exact ⟨hpos, by simp, by simp, by simp, by simp⟩

theorem stream.submit_code_batches.total {S V : Type} (source : stream.StreamingSource S)
    (visitor : stream.StreamingVisitor V) (moduleId : U64) (state : S)
    (env : metadata.CodeMetadata) (codeLen pos : Usize) (config : stream.StreamingConfig) (v : V)
    (hs : Stream.Source.CallbacksTotal source state) (hv : Stream.Scheduler.CallbacksTotal visitor )
    (henv : CodeEntry.Bounds env) (hcap : codeLen.val ≤ limits.MAX_MODULE_BYTES.val)
    (hpos : pos.val ≤ codeLen.val) :
    ∃ r, stream.submit_code_batches source visitor moduleId state env codeLen pos config v = .ok r := by
  obtain ⟨r, hr, _⟩ := WP.spec_imp_exists
    (stream.submit_code_batches.spec source visitor moduleId state env codeLen pos config v hs hv henv hcap hpos)
  exact ⟨r, hr⟩

end Itasca

end

/-! ## DriverTotal -/

section

/-!
# Streaming driver termination

`stream.validate_streaming.total_core`: on arbitrary bytes, `stream.validate_streaming`
returns success or an error whenever the source and scheduler callbacks return
(`Stream.Source.CallbacksTotal`, `Stream.Scheduler.CallbacksTotal`). Coherence, availability and
worker provenance are not premises. `Itasca/Results/Stream` states the public `total`.
-/

open Aeneas Aeneas.Std



namespace Itasca
/-- `stream.validate_streaming` returns success or an error on arbitrary bytes when the source and
scheduler callbacks return. Neither successful batches, source coherence nor scheduler provenance
is a termination premise. -/
theorem stream.validate_streaming.total_core {S V : Type} (source : stream.StreamingSource S)
    (visitor : stream.StreamingVisitor V) (moduleId : U64) (state : S)
    (v : V)
    (hs : Stream.Source.CallbacksTotal source state) (hv : Stream.Scheduler.CallbacksTotal visitor ) :
    ∃ r, stream.validate_streaming source visitor moduleId state v = .ok r := by
  have hspec : stream.validate_streaming source visitor moduleId state v ⦃ _ => True ⦄ := by
    unfold stream.validate_streaming
    obtain ⟨r, hread⟩ := hs.environment_returns
    rw [hread]
    cases r with
    | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok bytes =>
      simp [core.result.Result.Insts.CoreOpsTry.branch]
      obtain ⟨r, hlen, hlenp⟩ := WP.spec_imp_exists (limits.add_offset.spec 0#usize (Slice.len bytes))
      rw [hlen]
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok envLen =>
        have hsize : bytes.length ≤ limits.MAX_MODULE_BYTES.val := by scalar_tac
        simp
        obtain ⟨v1, hregion⟩ := hv.region v stream.StreamingRegion.Environment
        rw [hregion]
        simp only [bind_ok]
        obtain ⟨⟨r, v2⟩, hparsed, _⟩ := WP.spec_imp_exists
          (metadata.validate_env_with.spec visitor.metadataModuleVisitorInst hv.custom bytes v1)
        rw [hparsed]
        cases r with
        | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok pair =>
          obtain ⟨env, envEnd⟩ := pair
          have herase := metadata.validate_env_with.accepted_erase
            visitor.metadataModuleVisitorInst bytes v1 env envEnd v2 hparsed
          have henv := (Module.Environment.accepted_entry_conditions bytes env envEnd hsize herase).1
          simp
          split
          swap
          · simp
          · have sharing : metadata.ModuleMetadataCodeMetadata.share env = .ok env := by
              obtain ⟨x, hx, same⟩ := WP.spec_imp_exists (metadata.ModuleMetadataCodeMetadata.share.spec env)
              simpa [same] using hx
            simp only [sharing, bind_ok, alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref]
            obtain ⟨codeLen, hlen⟩ := hs.code_len_returns
            rw [hlen]
            simp only [bind_ok]
            obtain ⟨r, hsum, hsp⟩ := WP.spec_imp_exists (limits.add_offset.spec envLen codeLen)
            rw [hsum]
            cases r with
            | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
            | Ok beforeTail =>
              have hcap : codeLen.val ≤ limits.MAX_MODULE_BYTES.val := by omega
              simp [core.result.Result.Insts.CoreOpsTry.branch]
              obtain ⟨r, hheader, hhp⟩ := WP.spec_imp_exists
                (stream.read_code_header.spec source state codeLen env.code henv.1 (fun _ => hs.code_returns _ _))
              rw [hheader]
              cases r with
              | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
              | Ok entries =>
                simp
                obtain ⟨⟨r, v1⟩, hready⟩ := hv.environment v2 env
                rw [hready]
                cases r with
                | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
                | Ok config =>
                  simp
                  split
                  · simp
                  · split
                    · simp
                    · obtain ⟨r, hsubmit⟩ := stream.submit_code_batches.total source visitor moduleId state
                        env.code codeLen entries config v1 hs hv henv hcap hhp.entries_le
                      rw [hsubmit]
                      obtain ⟨r, v2⟩ := r
                      cases r with
                      | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
                      | Ok pending =>
                        simp
                        obtain ⟨⟨r, v3⟩, hcodeEnd⟩ := hv.code_end v2
                        rw [hcodeEnd]
                        cases r with
                        | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
                        | Ok u =>
                          cases u
                          simp
                          obtain ⟨r, htail⟩ := hs.tail_returns
                          rw [htail]
                          cases r with
                          | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
                          | Ok bytes =>
                            simp
                            obtain ⟨r, hadd⟩ := limits.add_offset.total beforeTail (Slice.len bytes)
                            rw [hadd]
                            cases r with
                            | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
                            | Ok whole =>
                              simp
                              obtain ⟨v4, hregion⟩ := hv.region v3 stream.StreamingRegion.Tail
                              rw [hregion]
                              simp only [bind_ok]
                              obtain ⟨⟨r, v5⟩, hparsed, _⟩ := WP.spec_imp_exists
                                (metadata.validate_tail_with.spec visitor.metadataModuleVisitorInst hv.custom
                                  bytes 0#usize env.code v4 (by simp) )
                              rw [hparsed]
                              cases r with
                              | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
                              | Ok tail =>
                                simp
                                obtain ⟨⟨r, after, remaining⟩, hdrain⟩ :=
                                  stream.retire_all_code_batches.total visitor moduleId v5 pending hv.poll
                                rw [hdrain]
                                cases r <;> simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  obtain ⟨r, hr, _⟩ := WP.spec_imp_exists hspec
  exact ⟨r, hr⟩

end Itasca

end

/-! ## SplitTotal -/

section

/-!
# Code region splitter termination

Termination and bounds of `stream.find_code_region`, which scans the section headers of a
contiguous module and returns the offsets that split it into environment, code and tail regions.
`stream.find_code_region.slices` shows that the three slices are safe and concatenate to the
whole input, whether or not it is a valid module. The canonical split is characterized in
`Stream/SplitComplete`.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- The splitter loop returns on every buffer, including short and malformed ones. Its output
describes three adjacent in-bounds regions. -/
theorem stream.find_code_region_loop.spec (bytes : Slice U8) (pos : Usize) :
    stream.find_code_region_loop bytes (Slice.len bytes) pos ⦃ result =>
      result.1.val ≤ result.2.val ∧ result.2.val ≤ bytes.length ⦄ := by
  unfold stream.find_code_region_loop
  apply loop.spec_decr_nat (fun pos => bytes.length - pos.val) (fun _ => True)
  · intro cursor _
    unfold stream.find_code_region_loop.body
    split
    · simp
    · rename_i hcursor
      have hcursor' : cursor.val < bytes.length := by scalar_tac
      step
      split
      · split
        · simp; scalar_tac
        · step
          obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (stream.read_len.spec bytes i)
          rw [hr]
          cases r with
          | Err e =>
            simp only [bind_ok]
            split <;> simp_all
          | Ok p =>
            obtain ⟨size, contents⟩ := p
            obtain ⟨_, _, hd⟩ := hp
            have hprogress := hd.span.1
            have hbound := hd.span.2.2
            simp only [bind_ok]
            step*
            scalar_tac
      · step
        obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (stream.read_len.spec bytes i)
        rw [hr]
        cases r with
        | Err e =>
          simp only [bind_ok]
          split <;> simp_all
          scalar_tac
        | Ok p =>
          obtain ⟨size, contents⟩ := p
          obtain ⟨_, _, hd⟩ := hp
          have hprogress := hd.span.1
          have hbound := hd.span.2.2
          simp only [bind_ok]
          step* <;> scalar_tac
  · trivial

/-- `stream.find_code_region` returns on every buffer with ordered in-bounds offsets. -/
@[step]
theorem stream.find_code_region.spec (bytes : Slice U8) :
    stream.find_code_region bytes ⦃ result =>
      result.1.val ≤ result.2.val ∧ result.2.val ≤ bytes.length ⦄ := by
  simpa [stream.find_code_region] using
    stream.find_code_region_loop.spec bytes 8#usize

theorem stream.find_code_region.bounds (bytes : Slice U8) (first last : Usize)
    (h : stream.find_code_region bytes = .ok (first, last)) :
    first.val ≤ last.val ∧ last.val ≤ bytes.length := by
  have hs := stream.find_code_region.spec bytes
  simpa [h] using hs

/-- The slice operations at the split boundaries are safe and the resulting regions concatenate to
the input, whether or not the input is a valid module. -/
theorem stream.find_code_region.slices (bytes : Slice U8) (first last : Usize)
    (h : stream.find_code_region bytes = .ok (first, last)) :
    ∃ environment code tail : Slice U8,
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        bytes ⟨0#usize, first⟩ = .ok environment ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        bytes ⟨first, last⟩ = .ok code ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        bytes ⟨last, Slice.len bytes⟩ = .ok tail ∧
      bytes.val = environment.val ++ code.val ++ tail.val := by
  obtain ⟨hfirst, hlast⟩ := stream.find_code_region.bounds bytes first last h
  have slice_spec (start finish : Usize) (hs : start.val ≤ finish.val)
      (hf : finish.val ≤ bytes.length) :
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        bytes ⟨start, finish⟩ ⦃ region =>
          Body.Scalar.BytesAt bytes start region.val finish ⦄ := by
    step
    apply Body.Scalar.BytesAt.of_slice_view hs hf
    assumption
  obtain ⟨environment, he, heSpan⟩ := WP.spec_imp_exists
    (slice_spec 0#usize first (by simp) (by omega))
  obtain ⟨code, hc, hcSpan⟩ := WP.spec_imp_exists (slice_spec first last hfirst hlast)
  obtain ⟨tail, ht, htSpan⟩ := WP.spec_imp_exists
    (slice_spec last (Slice.len bytes) (by simpa using hlast) (by simp))
  exact ⟨environment, code, tail, he, hc, ht,
    by simpa using ((heSpan.append hcSpan).append htSpan).suffix⟩

end Itasca

end

end
