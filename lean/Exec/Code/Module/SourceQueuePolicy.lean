import Itasca.Stream.SchedulerComplete

namespace Exec.Code.StreamAvailability
open Aeneas Aeneas.Std Itasca

/-- Local acceptance contract at a fixed validated environment and source
cursor. Unlike an unrestricted visitor contract, this permits finite numerical
module budgets and retains actual completed worker identities and finish checks. -/
structure QueuePolicy {V : Type} (visitor : Itasca.stream.StreamingVisitor V)
    (config : Itasca.stream.Config) (env : module.Env) (profile : ValidationProfile)
    (Queued : U64 → List StreamBatch.Issued → Nat → V → Prop) : Prop where
  batch_positive : 0 < config.batch_bytes.val
  capacity_positive : 0 < config.max_batches.val
  submit : ∀ id queue cursor issued before,
    Queued id queue cursor before → StreamAcceptingScheduler.Valid issued profile →
    issued.env = env → issued.module_id = id → issued.first_func.val = cursor →
    queue.length < config.max_batches.val →
    ∃ after, visitor.submit_code_batch before issued.seed = .ok (.Ok (),after) ∧
      Queued id (queue++[issued]) (cursor+issued.num_funcs.val) after
  poll : ∀ id queue cursor before, Queued id queue cursor before → queue ≠ [] →
    ∃ issued rest worker after, (issued::rest).Perm queue ∧
      visitor.poll_code_batch before = .ok (.Ok worker,after) ∧
      StreamBatch.Identity issued worker ∧ Itasca.stream.CodeBatch.finish worker = .ok (.Ok ()) ∧
      Queued id rest cursor after

/-- A real queued worker retires successfully. Its finish proof comes from
concrete compilation; dispatch cursors need not match an empty visitor run. -/
theorem retire_complete {V : Type} (visitor : Itasca.stream.StreamingVisitor V)
    (config : Itasca.stream.Config) (env : module.Env) (profile : ValidationProfile)
    (Queued : U64 → List StreamBatch.Issued → Nat → V → Prop)
    (policy : QueuePolicy visitor config env profile Queued)
    (id : U64) (queue : List StreamBatch.Issued) (cursor : Nat) (before : V)
    (pending : alloc.vec.Vec Usize) (held : Queued id queue cursor before)
    (valid : StreamAcceptingScheduler.ValidQueue id queue profile)
    (ids : pending.val.Perm (queue.map StreamBatch.Issued.batch_id)) (nonempty : pending.val ≠ []) :
    ∃ after remaining rest,
      Itasca.stream.retire_code_batch visitor id before pending = .ok (.Ok (),after,remaining) ∧
      Queued id rest cursor after ∧ StreamAcceptingScheduler.ValidQueue id rest profile ∧
      remaining.val.Perm (rest.map StreamBatch.Issued.batch_id) ∧ remaining.length+1 = pending.length := by
  have queued : queue ≠ [] := by
    intro empty
    have length := ids.length_eq
    simp only [empty,List.map_nil,List.length_nil] at length
    exact nonempty (by simpa using length)
  obtain ⟨issued,rest,worker,after,permutation,polled,identity,finished,retained⟩ := policy.poll id queue cursor before held queued
  have member : issued ∈ queue := permutation.mem_iff.mp (by simp)
  obtain ⟨moduleId,_⟩ := valid issued member
  have pendingIds : (issued.batch_id::rest.map StreamBatch.Issued.batch_id).Perm pending.val :=
    (permutation.map StreamBatch.Issued.batch_id).trans ids.symm
  obtain ⟨remaining,retired,removed⟩ := Itasca.stream.retire_code_batch.complete visitor id before after pending worker polled
    (identity.1.trans moduleId) (by rw [identity.2.1]; exact pendingIds.mem_iff.mp (by simp)) finished
  refine ⟨after,remaining,rest,retired,retained,?_,?_,?_⟩
  · intro old member
    exact valid old (permutation.mem_iff.mp (by simp [member]))
  · rw [identity.2.1] at removed
    exact List.Perm.cons_inv (removed.trans pendingIds.symm)
  · have length := removed.length_eq
    simpa only [List.length_cons] using length

/-- Draining the actual completed-worker queue preserves the source cursor and
terminates with every pending worker retired. -/
theorem drain_complete {V : Type} (visitor : Itasca.stream.StreamingVisitor V)
    (config : Itasca.stream.Config) (env : module.Env) (profile : ValidationProfile)
    (Queued : U64 → List StreamBatch.Issued → Nat → V → Prop)
    (policy : QueuePolicy visitor config env profile Queued)
    (id : U64) (queue : List StreamBatch.Issued) (cursor : Nat) (before : V)
    (pending : alloc.vec.Vec Usize) (held : Queued id queue cursor before)
    (valid : StreamAcceptingScheduler.ValidQueue id queue profile)
    (ids : pending.val.Perm (queue.map StreamBatch.Issued.batch_id)) :
    ∃ after remaining,
      Itasca.stream.retire_all_code_batches visitor id before pending = .ok (.Ok (),after,remaining) ∧
      remaining.val = [] ∧ Queued id [] cursor after := by
  generalize count : pending.val.length = n
  induction n using Nat.strong_induction_on generalizing queue before pending with
  | h n ih =>
    by_cases empty : pending.val = []
    · have queueEmpty : queue = [] := by
        have length := ids.length_eq
        simp only [empty,List.length_nil,List.length_map] at length
        simpa using length.symm
      refine ⟨before,pending,?_,empty,by simpa only [queueEmpty] using held⟩
      rw [Itasca.stream.retire_all_code_batches,Itasca.stream.retire_all_code_batches_loop,loop]
      simp [Itasca.stream.retire_all_code_batches_loop.body,alloc.vec.Vec.is_empty,empty]
    · obtain ⟨middle,remaining,rest,retired,retained,restValid,restIds,length⟩ :=
        retire_complete visitor config env profile Queued policy id queue cursor before pending held valid ids empty
      change remaining.val.length+1 = pending.val.length at length
      obtain ⟨after,final,continued,finished,result⟩ := ih remaining.val.length (by omega)
        rest middle remaining retained restValid restIds rfl
      refine ⟨after,final,?_,finished,result⟩
      rw [Itasca.stream.retire_all_code_batches,Itasca.stream.retire_all_code_batches_loop,loop]
      have nonempty : pending.val.isEmpty = false := by simpa using empty
      simpa [Itasca.stream.retire_all_code_batches_loop.body,alloc.vec.Vec.is_empty,nonempty,retired,
        core.result.Result.Insts.CoreOpsTry.branch,Itasca.stream.retire_all_code_batches,
        Itasca.stream.retire_all_code_batches_loop] using continued

end Exec.Code.StreamAvailability
