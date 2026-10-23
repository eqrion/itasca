import Itasca.Stream.Scheduler
import Itasca.Stream.BatchComplete

/-!
# Synchronous worker

The private synchronous scheduler `stream.SyncVisitor` that `validate_module` supplies to the
driver. It has one `completed` slot: submission runs `stream.CodeBatch.validate_all` on the seed
immediately and stores the result, and polling takes it. `StreamSync.provenance` and
`StreamSync.callbacks_total` show that it meets the `StreamScheduler.Provenance` and
`StreamScheduler.CallbacksTotal` contracts for every profile, so no embedding obligation remains
for it. `StreamSync.retire_all_tail` shows that draining preserves the delivered tail.
-/

open Aeneas Aeneas.Std

namespace Itasca.StreamSync

local notation "sync" => stream.SyncVisitor.Insts.ItascaStreamStreamingVisitor

/-- The stored worker is reachable from every historical issued batch matching its identity. The
invariant does not assume that the worker has finished. -/
def Tracks (_id : U64) (history : List StreamBatch.Issued) (state : stream.SyncVisitor) : Prop :=
  ∀ batch, state.completed = some batch → ∀ issued ∈ history,
    issued.module_id = batch.module_id → issued.batch_id = batch.batch_id →
    StreamBatch.Reachable issued batch

theorem tracks_empty (id : U64) (state : stream.SyncVisitor) : Tracks id [] state := by
  simp [Tracks]

theorem tracks_cleared (id : U64) (history : List StreamBatch.Issued) (state : stream.SyncVisitor)
    (h : state.completed = none) : Tracks id history state := by
  simp [Tracks, h]

/-- Polling takes the stored worker out of the completed slot and keeps the tail. -/
theorem poll_some (state : stream.SyncVisitor) (batch : stream.CodeBatch)
    (h : state.completed = some batch) :
    (sync).poll_code_batch state = .ok (.Ok batch, { state with completed := none }) := by
  simp [stream.SyncVisitor.Insts.ItascaStreamStreamingVisitor.poll_code_batch,
    core.option.Option.take, h]

theorem poll_none (state : stream.SyncVisitor) (h : state.completed = none) :
    (sync).poll_code_batch state = .ok (.Err .Host, { state with completed := none }) := by
  simp [stream.SyncVisitor.Insts.ItascaStreamStreamingVisitor.poll_code_batch,
    core.option.Option.take, h]

theorem poll_accepted (state after : stream.SyncVisitor) (batch : stream.CodeBatch)
    (h : (sync).poll_code_batch state = .ok (.Ok batch, after)) :
    state.completed = some batch ∧ after = { state with completed := none } := by
  cases he : state.completed with
  | none => rw [poll_none state he] at h; simp at h
  | some current =>
    rw [poll_some state current he] at h
    have hh : current = batch ∧ { state with completed := none } = after := by simpa using h
    exact ⟨by simp [hh.1], hh.2.symm⟩

theorem poll_total : StreamRetirement.PollTotal sync := by
  intro state
  cases he : state.completed with
  | none => exact ⟨_, poll_none state he⟩
  | some batch => exact ⟨_, poll_some state batch he⟩

theorem poll_tail (state after : stream.SyncVisitor)
    (result : core.result.Result stream.CodeBatch error.Error)
    (h : (sync).poll_code_batch state = .ok (result, after)) : after.tail = state.tail := by
  cases he : state.completed with
  | none => rw [poll_none state he] at h; simp only [Result.ok.injEq, Prod.mk.injEq] at h; rw [← h.2]
  | some batch => rw [poll_some state batch he] at h; simp only [Result.ok.injEq, Prod.mk.injEq] at h; rw [← h.2]

theorem tail_ready (state : stream.SyncVisitor) (tail : module.Tail) :
    (sync).tail_ready state tail = .ok (.Ok (), { state with tail := some tail }) := rfl

theorem environment_ready (state : stream.SyncVisitor) (env : module.Env) :
    (sync).environment_ready state env =
      .ok (.Ok { batch_bytes := 25000#usize, max_batches := 1#usize }, state) := rfl

theorem custom_accepts : ModuleTail.HooksAccept (sync).moduleModuleVisitorInst := by
  intro state chunk
  exact ⟨state, rfl⟩

theorem custom_region (state : stream.SyncVisitor) (region : stream.Region) :
    (sync).custom_region state region = .ok state := rfl

theorem code_end (state : stream.SyncVisitor) :
    (sync).code_end state = .ok (.Ok (), state) := rfl

/-- Submission runs the extracted worker even on malformed bytes and stores its reachable result.
Submission succeeding does not mean that `stream.CodeBatch.finish` passes. -/
theorem submit {profile : ValidationProfile} (state : stream.SyncVisitor) (issued : StreamBatch.Issued)
    (hissued : issued.Bounded) (hbound : CodeEntry.Bounds issued.env)
    (hprofile : issued.profile = profile) :
    ∃ batch, (sync).submit_code_batch state issued.seed =
      .ok (.Ok (), { state with completed := some batch }) ∧
      StreamBatch.Reachable issued batch := by
  obtain ⟨batch, hr, hp⟩ := WP.spec_imp_exists
    (stream.CodeBatch.validate_all.reachable issued issued.seed hissued hbound .seed hprofile)
  exact ⟨batch, by simp [stream.SyncVisitor.Insts.ItascaStreamStreamingVisitor.submit_code_batch, hr], hp⟩

/-- The synchronous scheduler satisfies `StreamScheduler.Provenance` across every callback,
including custom regions and tail delivery. -/
theorem provenance {profile : ValidationProfile} : StreamScheduler.Provenance sync Tracks profile := by
  constructor
  · intro id history state chunk after hcall
    have he : state = after := by
      simpa [stream.SyncVisitor.Insts.ItascaModuleModuleVisitor,
        module.ModuleVisitor.on_custom_section.default] using hcall
    subst after
    exact fun h => h
  · intro id history state region after hs hcall
    have he : state = after := by
      simpa [stream.SyncVisitor.Insts.ItascaStreamStreamingVisitor.custom_region] using hcall
    exact he ▸ hs
  · intro id history state env config after hs hcall
    rw [environment_ready] at hcall
    simp only [Result.ok.injEq, Prod.mk.injEq] at hcall
    exact hcall.2 ▸ hs
  · intro id history issued state after _ _ hissued hbound hprofile hfresh hcall
    obtain ⟨batch, hr, hreach⟩ := submit state issued hissued hbound hprofile
    rw [hr] at hcall
    have he : { state with completed := some batch } = after := by simpa using hcall
    subst after
    intro actual hslot old hold _ hbatch
    have he : actual = batch := by simpa using hslot.symm
    subst actual
    rcases List.mem_append.mp hold with hold | hold
    · have hb := hreach.validation.1.2.1
      exact False.elim (hfresh old hold (hbatch.trans hb))
    · have he : old = issued := by simpa using hold
      exact he ▸ hreach
  · intro id history state batch after hs hcall
    obtain ⟨hslot, rfl⟩ := poll_accepted state after batch hcall
    exact ⟨tracks_cleared id history _ rfl, hs batch hslot⟩
  · intro id history state after hs hcall
    have he : state = after := by
      simpa [stream.SyncVisitor.Insts.ItascaStreamStreamingVisitor.code_end] using hcall
    exact he ▸ hs
  · intro id history state tail after hs hcall
    rw [tail_ready] at hcall
    have he : { state with tail := some tail } = after := by simpa using hcall
    subst after
    exact hs

/-- All callbacks of the synchronous scheduler return on seeds of bounded issued batches.
Submission needs neither valid bytes nor successful worker completion. -/
theorem callbacks_total {profile : ValidationProfile} : StreamScheduler.CallbacksTotal sync profile := by
  constructor
  · intro state chunk
    exact ⟨(.Ok (), state), rfl⟩
  · intro state region
    exact ⟨state, rfl⟩
  · intro state env
    exact ⟨_, environment_ready state env⟩
  · intro state issued hissued hbound hprofile
    obtain ⟨batch, hr, _⟩ := submit state issued hissued hbound hprofile
    exact ⟨_, hr⟩
  · exact poll_total
  · intro state
    exact ⟨(.Ok (), state), rfl⟩
  · intro state tail
    exact ⟨_, tail_ready state tail⟩

/-- Successful retirement preserves the stored tail, because its only visitor callback is polling,
which clears only the completed slot. -/
theorem retire_tail (id : U64) (state after : stream.SyncVisitor)
    (pending remaining : alloc.vec.Vec Usize)
    (h : stream.retire_code_batch sync id state pending = .ok (.Ok (), after, remaining)) :
    after.tail = state.tail := by
  obtain ⟨batch, hpoll, _, _, _⟩ := stream.retire_code_batch.accepted
    sync id state after pending remaining h
  exact poll_tail state after (.Ok batch) hpoll

private theorem retire_all_loop_tail (id : U64) (state after : stream.SyncVisitor)
    (pending remaining : alloc.vec.Vec Usize)
    (h : stream.retire_all_code_batches_loop sync id state pending = .ok (.Ok (), after, remaining)) :
    after.tail = state.tail := by
  generalize hn : pending.length = n
  induction n using Nat.strong_induction_on generalizing state pending with
  | h n ih =>
    unfold stream.retire_all_code_batches_loop at h
    rw [loop] at h
    simp only [stream.retire_all_code_batches_loop.body, alloc.vec.Vec.is_empty, bind_ok] at h
    by_cases hempty : pending.val = []
    · simp [hempty] at h
      exact congrArg stream.SyncVisitor.tail h.1.symm
    · have hnonempty : pending.val.isEmpty = false := by simpa using hempty
      simp only [hnonempty, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨⟨result, current, rest⟩, hretire⟩ := stream.retire_code_batch.total sync id state pending (poll_total state)
      rw [hretire] at h
      cases result with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
      | Ok u =>
        cases u
        obtain ⟨batch, _, _, _, hperm⟩ := stream.retire_code_batch.accepted
          sync id state current pending rest hretire
        have hlen : rest.length < n := by
          have he := hperm.length_eq
          simp only [List.length_cons] at he
          change rest.val.length < n
          change pending.val.length = n at hn
          omega
        have htail := retire_tail id state current pending rest hretire
        have hrest : stream.retire_all_code_batches_loop sync id current rest =
            .ok (.Ok (), after, remaining) := by
          simpa [stream.retire_all_code_batches_loop, stream.retire_all_code_batches_loop.body,
            alloc.vec.Vec.is_empty, core.result.Result.Insts.CoreOpsTry.branch] using h
        exact (ih rest.length hlen current rest hrest rfl).trans htail

/-- Draining preserves the tail delivered before retirement. -/
theorem retire_all_tail (id : U64) (state after : stream.SyncVisitor)
    (pending remaining : alloc.vec.Vec Usize)
    (h : stream.retire_all_code_batches sync id state pending = .ok (.Ok (), after, remaining)) :
    after.tail = state.tail :=
  retire_all_loop_tail id state after pending remaining h

end Itasca.StreamSync
