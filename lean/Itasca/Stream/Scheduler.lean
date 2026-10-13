import Itasca.Stream.Batch
import Itasca.Stream.Retirement
import Itasca.Module.Custom.Invariant
import Itasca.Support.Result

open Aeneas Aeneas.Std

namespace Itasca.StreamScheduler

variable {profile : ValidationProfile}

/-- Returning callbacks are independent of the soundness provenance contract.
Ordinary Rust errors and malformed returned worker records are allowed. -/
structure CallbacksTotal {V : Type} (visitor : stream.StreamingVisitor V)
    (profile : ValidationProfile := .Wasm1) : Prop where
  custom : ModuleTail.HooksTotal visitor.moduleModuleVisitorInst
  region : ∀ v region, ∃ v', visitor.custom_region v region = .ok v'
  environment : ∀ v env, ∃ r, visitor.environment_ready v env = .ok r
  submit : ∀ v (issued : StreamBatch.Issued), issued.Bounded → CodeEntry.Bounds issued.env → issued.profile = profile →
    ∃ r, visitor.submit_code_batch v issued.seed = .ok r
  poll : StreamRetirement.PollTotal visitor
  code_end : ∀ v, ∃ r, visitor.code_end v = .ok r
  tail_ready : ∀ v tail, ∃ r, visitor.tail_ready v tail = .ok r

/-- A scheduler preserves issued history across every callback. Polling a
matching historical identity supplies actual-operation reachability, not a
claim of worker success. Unknown, foreign, unfinished and replayed batches are
permitted; the driver remains responsible for pending IDs and finish checks. -/
structure Provenance {V : Type} (visitor : stream.StreamingVisitor V)
    (Tracks : U64 → List StreamBatch.Issued → V → Prop)
    (profile : ValidationProfile := .Wasm1) : Prop where
  custom : ∀ id history, ModuleTail.PreservesInvariant
    visitor.moduleModuleVisitorInst (Tracks id history)
  region : ∀ id history v region v', Tracks id history v →
    visitor.custom_region v region = .ok v' → Tracks id history v'
  environment : ∀ id history v env config v', Tracks id history v →
    visitor.environment_ready v env = .ok (.Ok config, v') → Tracks id history v'
  submit : ∀ id history issued v v', Tracks id history v →
    issued.module_id = id → issued.Bounded → CodeEntry.Bounds issued.env → issued.profile = profile →
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
def Completed (issued : StreamBatch.Issued) (profile : ValidationProfile := .Wasm1) : Prop :=
  ∃ entries, entries.length = issued.num_funcs.val ∧
    ModuleBinary.Rep (Profile.CodeEncoding profile) entries issued.code.val ∧
    ModuleCode.EntriesTyped (profile := profile) issued.env issued.first_func.val entries

theorem Provenance.environment_preserves {V : Type} {visitor : stream.StreamingVisitor V}
    {Tracks : U64 → List StreamBatch.Issued → V → Prop} (hp : Provenance visitor Tracks profile)
    (id : U64) (history : List StreamBatch.Issued) (data : Slice U8)
    (v v' : V) (env : module.Env) (next : Usize)
    (h : module.validate_env_with visitor.moduleModuleVisitorInst data profile v = .ok (.Ok (env, next), v')) :
    Tracks id history v → Tracks id history v' :=
  module.validate_env_with.accepted_invariant _ _ (hp.custom id history) data v env next v' h

theorem Provenance.tail_preserves {V : Type} {visitor : stream.StreamingVisitor V}
    {Tracks : U64 → List StreamBatch.Issued → V → Prop} (hp : Provenance visitor Tracks profile)
    (id : U64) (history : List StreamBatch.Issued) (data : Slice U8) (pos : Usize)
    (v v' : V) (env : module.Env) (tail : module.Tail)
    (h : module.validate_tail_with visitor.moduleModuleVisitorInst data pos env profile v = .ok (.Ok tail, v')) :
    Tracks id history v → Tracks id history v' :=
  module.validate_tail_with.accepted_invariant _ _ (hp.custom id history) data pos env v tail v' h

/-- Successful retirement validates any historical descriptor matching the
removed pending identity. No finished/replay-free condition is assumed of polls. -/
theorem retire_sound {V : Type} (visitor : stream.StreamingVisitor V)
    (Tracks : U64 → List StreamBatch.Issued → V → Prop) (hp : Provenance visitor Tracks profile)
    (id : U64) (history : List StreamBatch.Issued) (v v' : V)
    (pending remaining : alloc.vec.Vec Usize) (hv : Tracks id history v)
    (henv : ∀ issued ∈ history, CodeEntry.Bounds issued.env ∧
      ∀ ft ∈ issued.env.types.val, Profile.FuncType profile ft)
    (hprofiles : ∀ issued ∈ history, issued.profile = profile)
    (h : stream.retire_code_batch visitor id v pending = .ok (.Ok (), v', remaining)) :
    Tracks id history v' ∧ ∃ batchId,
      (batchId :: remaining.val).Perm pending.val ∧
      ∀ issued ∈ history, issued.module_id = id → issued.batch_id = batchId → Completed issued profile := by
  obtain ⟨batch, hpolled, hmodule, hfinish, hperm⟩ :=
    stream.retire_code_batch.accepted visitor id v v' pending remaining h
  obtain ⟨hv', hr⟩ := hp.poll id history v batch v' hv hpolled
  refine ⟨hv', batch.batch_id, hperm, ?_⟩
  intro issued hm hid hbatch
  exact (hr issued hm (hid.trans hmodule.symm) hbatch).finished (henv issued hm).1 (henv issued hm).2 (hprofiles issued hm) hfinish

end Itasca.StreamScheduler

open Aeneas Aeneas.Std

namespace Itasca.StreamScheduler

variable {profile : ValidationProfile}

/-- Final draining derives certificates for every originally pending issued
identity, while retaining provenance after every poll. -/
theorem drain_sound {V : Type} (visitor : stream.StreamingVisitor V)
    (Tracks : U64 → List StreamBatch.Issued → V → Prop) (hp : Provenance visitor Tracks profile)
    (id : U64) (history : List StreamBatch.Issued) (v v' : V)
    (pending remaining : alloc.vec.Vec Usize) (hv : Tracks id history v)
    (henv : ∀ issued ∈ history, CodeEntry.Bounds issued.env ∧
      ∀ ft ∈ issued.env.types.val, Profile.FuncType profile ft)
    (hprofiles : ∀ issued ∈ history, issued.profile = profile)
    (h : stream.retire_all_code_batches visitor id v pending = .ok (.Ok (), v', remaining)) :
    Tracks id history v' ∧ remaining.val = [] ∧
      ∀ issued ∈ history, issued.module_id = id → issued.batch_id ∈ pending.val → Completed issued profile := by
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
          retire_sound visitor Tracks hp id history v next pending rest hv henv hprofiles hretire
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
