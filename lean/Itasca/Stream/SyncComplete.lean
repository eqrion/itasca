import Itasca.Stream.Sync
import Itasca.Stream.SchedulerComplete
import Itasca.Stream.DriverRun

/-!
# Synchronous worker completeness

`StreamSync.accepts` shows that the synchronous scheduler `stream.SyncVisitor` satisfies the
accepting policy `StreamAcceptingScheduler.Accepts`, with batch size 25000 bytes and capacity one,
so completeness for `validate_module` has no scheduler premise. `StreamSync.delivered_tail` shows
that the tail stored by the final state is the tail the driver delivered.
-/

open Aeneas Aeneas.Std

namespace Itasca.StreamSync

local notation "sync" => stream.SyncVisitor.Insts.ItascaStreamStreamingVisitor

/-- The synchronous worker has a single slot. A nonempty logical queue identifies that slot as the
result of `stream.CodeBatch.validate_all` on its seed. -/
def Queued (_id : U64) (queue : List StreamBatch.Issued) (state : stream.SyncVisitor) : Prop :=
  match queue with
  | [] => state.completed = none
  | [issued] => ∃ batch, state.completed = some batch ∧
      stream.CodeBatch.validate_all issued.seed = .ok batch
  | _ => False

/-- The synchronous scheduler satisfies the accepting scheduler policy. Capacity one prevents a
queued batch from being overwritten. -/
theorem accepts {profile : ValidationProfile} : StreamAcceptingScheduler.Accepts sync
    { batch_bytes := 25000#usize, max_batches := 1#usize } Queued profile := by
  constructor
  · decide
  · decide
  · exact custom_accepts
  · intro id queue state chunk after hcall hqueue
    have he : state = after := by
      simpa [stream.SyncVisitor.Insts.ItascaModuleModuleVisitor,
        module.ModuleVisitor.on_custom_section.default] using hcall
    exact he ▸ hqueue
  · intro id queue state region hqueue
    exact ⟨state, custom_region state region, hqueue⟩
  · intro id queue state env hqueue
    exact ⟨state, environment_ready state env, hqueue⟩
  · intro id queue issued state hqueue hvalid _ hroom
    have hnil : queue = [] := by simpa using hroom
    subst queue
    obtain ⟨entries, hn, ht, hb⟩ := hvalid.entries
    obtain ⟨after, hr, _, _⟩ := stream.CodeBatch.validate_all.complete_at_seed
      issued entries hvalid.bounded hn ht hvalid.profile hvalid.limits hvalid.entry_bounds hb hvalid.validation_profile
    refine ⟨{ state with completed := some after }, ?_, after, rfl, hr⟩
    simp [stream.SyncVisitor.Insts.ItascaStreamStreamingVisitor.submit_code_batch, hr]
  · intro id queue state hqueue _ hnonempty
    cases queue with
    | nil => contradiction
    | cons issued rest =>
      cases rest with
      | cons _ _ => exact False.elim hqueue
      | nil =>
        obtain ⟨batch, hslot, hr⟩ := hqueue
        exact ⟨issued, [], batch, { state with completed := none }, .refl _,
          poll_some state batch hslot, hr, rfl⟩
  · intro id queue state hqueue
    exact ⟨state, code_end state, hqueue⟩
  · intro id queue state tail hqueue
    refine ⟨{ state with tail := some tail }, tail_ready state tail, ?_⟩
    cases queue with
    | nil => exact hqueue
    | cons _ rest => cases rest <;> exact hqueue

/-- The tail delivered to the scheduler survives the final drain, so the slice adapter returns the
tail that the generic driver theorems describe. -/
theorem delivered_tail {profile : ValidationProfile} {S : Type} {source : stream.Source S} {id : U64} {state : S}
    {env : module.Env} {environmentLength : Usize} {before after : stream.SyncVisitor}
    (run : StreamRun.Remaining source sync id state env environmentLength before after profile) :
    after.tail = some run.tail := by
  have hready := run.ready_call
  rw [tail_ready] at hready
  have hreadyEq : run.ready = { run.decodedTail with tail := some run.tail } := by
    simpa using hready.symm
  have hfinal := retire_all_tail id run.ready after run.pending run.remaining run.drain_call
  simpa [hreadyEq] using hfinal

end Itasca.StreamSync
