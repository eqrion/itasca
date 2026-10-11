import Itasca.Stream.StreamBatch
import Itasca.Stream.StreamRetirement
import Itasca.Module.ModuleCustomInvariant

open Aeneas Aeneas.Std

namespace Itasca.StreamScheduler

/-- Returning callbacks are independent of the soundness provenance contract.
Ordinary Rust errors and malformed returned worker records are allowed. -/
structure CallbacksTotal {V : Type} (visitor : stream.StreamingVisitor V) : Prop where
  custom : ModuleTail.HooksTotal visitor.moduleModuleVisitorInst
  region : ∀ v region, ∃ v', visitor.custom_region v region = .ok v'
  environment : ∀ v env, ∃ r, visitor.environment_ready v env = .ok r
  submit : ∀ v (issued : StreamBatch.Issued), issued.Bounded → CodeEntry.Bounds issued.env →
    ∃ r, visitor.submit_code_batch v issued.seed = .ok r
  poll : StreamRetirement.PollTotal visitor
  code_end : ∀ v, ∃ r, visitor.code_end v = .ok r
  tail_ready : ∀ v tail, ∃ r, visitor.tail_ready v tail = .ok r

/-- A scheduler preserves issued history across every callback. Polling a
matching historical identity supplies actual-operation reachability, not a
claim of worker success. Unknown, foreign, unfinished and replayed batches are
permitted; the driver remains responsible for pending IDs and finish checks. -/
structure Provenance {V : Type} (visitor : stream.StreamingVisitor V)
    (Tracks : U64 → List StreamBatch.Issued → V → Prop) : Prop where
  custom : ∀ id history, ModuleTail.PreservesInvariant
    visitor.moduleModuleVisitorInst (Tracks id history)
  region : ∀ id history v region v', Tracks id history v →
    visitor.custom_region v region = .ok v' → Tracks id history v'
  environment : ∀ id history v env config v', Tracks id history v →
    visitor.environment_ready v env = .ok (.Ok config, v') → Tracks id history v'
  submit : ∀ id history issued v v', Tracks id history v →
    issued.module_id = id → issued.Bounded → CodeEntry.Bounds issued.env →
    (∀ old ∈ history, old.batch_id ≠ issued.batch_id) →
    visitor.submit_code_batch v issued.seed = .ok (.Ok (), v') →
    Tracks id (history ++ [issued]) v'
  poll : ∀ id history v batch v', Tracks id history v →
    visitor.poll_code_batch v = .ok (.Ok batch, v') →
    Tracks id history v' ∧ ∀ issued ∈ history,
      issued.module_id = batch.module_id → issued.batch_id = batch.batch_id →
      StreamBatch.Reachable issued batch
  code_end : ∀ id history v v', Tracks id history v →
    visitor.code_end v = .ok (.Ok (), v') → Tracks id history v'
  tail_ready : ∀ id history v tail v', Tracks id history v →
    visitor.tail_ready v tail = .ok (.Ok (), v') → Tracks id history v'

/-- A completed batch has exact byte coverage and ordered semantic entry
certificates. This is derived at successful retirement, never a poll premise. -/
def Completed (issued : StreamBatch.Issued) : Prop :=
  ∃ entries, entries.length = issued.num_funcs.val ∧
    ModuleBinary.Rep ModuleBinary.CodeEncoding entries issued.code.val ∧
    ModuleCode.EntriesTyped issued.env issued.first_func.val entries

theorem Provenance.environment_preserves {V : Type} {visitor : stream.StreamingVisitor V}
    {Tracks : U64 → List StreamBatch.Issued → V → Prop} (hp : Provenance visitor Tracks)
    (id : U64) (history : List StreamBatch.Issued) (data : Slice U8)
    (v v' : V) (env : module.Env) (next : Usize)
    (h : module.validate_env_with visitor.moduleModuleVisitorInst data v = .ok (.Ok (env, next), v')) :
    Tracks id history v → Tracks id history v' :=
  module.validate_env_with.accepted_invariant _ _ (hp.custom id history) data v env next v' h

theorem Provenance.tail_preserves {V : Type} {visitor : stream.StreamingVisitor V}
    {Tracks : U64 → List StreamBatch.Issued → V → Prop} (hp : Provenance visitor Tracks)
    (id : U64) (history : List StreamBatch.Issued) (data : Slice U8) (pos : Usize)
    (v v' : V) (env : module.Env) (tail : module.Tail)
    (h : module.validate_tail_with visitor.moduleModuleVisitorInst data pos env v = .ok (.Ok tail, v')) :
    Tracks id history v → Tracks id history v' :=
  module.validate_tail_with.accepted_invariant _ _ (hp.custom id history) data pos env v tail v' h

/-- Successful retirement validates any historical descriptor matching the
removed pending identity. No finished/replay-free condition is assumed of polls. -/
theorem retire_sound {V : Type} (visitor : stream.StreamingVisitor V)
    (Tracks : U64 → List StreamBatch.Issued → V → Prop) (hp : Provenance visitor Tracks)
    (id : U64) (history : List StreamBatch.Issued) (v v' : V)
    (pending remaining : alloc.vec.Vec Usize) (hv : Tracks id history v)
    (henv : ∀ issued ∈ history, CodeEntry.Bounds issued.env ∧
      ∀ ft ∈ issued.env.types.val, ft.results.val.length ≤ 1)
    (h : stream.retire_code_batch visitor id v pending = .ok (.Ok (), v', remaining)) :
    Tracks id history v' ∧ ∃ batchId,
      (batchId :: remaining.val).Perm pending.val ∧
      ∀ issued ∈ history, issued.module_id = id → issued.batch_id = batchId → Completed issued := by
  obtain ⟨batch, hpolled, hmodule, hfinish, hperm⟩ :=
    stream.retire_code_batch.accepted visitor id v v' pending remaining h
  obtain ⟨hv', hr⟩ := hp.poll id history v batch v' hv hpolled
  refine ⟨hv', batch.batch_id, hperm, ?_⟩
  intro issued hm hid hbatch
  exact (hr issued hm (hid.trans hmodule.symm) hbatch).finished (henv issued hm).1 (henv issued hm).2 hfinish

end Itasca.StreamScheduler
