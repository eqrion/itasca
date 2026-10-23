import Itasca.Stream.Batch
import Itasca.Stream.Retirement
import Itasca.Module.Custom.Invariant
import Itasca.Support.Result
import Itasca.Contracts

/-!
# Scheduler soundness

Consequences of the scheduler premises `StreamScheduler.CallbacksTotal` and
`StreamScheduler.Provenance`, defined in `Itasca/Contracts`. `retire_sound`
and `drain_sound` show that successful retirement and draining produce `StreamScheduler.Completed`
certificates (exact byte coverage and typed entries) for every pending issued batch.
-/

open Aeneas Aeneas.Std

namespace Itasca.StreamScheduler

variable {profile : ValidationProfile}

/-- A completed batch has exact byte coverage and ordered entry certificates. This is derived at
successful retirement and is never a premise on polls. -/
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

/-- After a successful retirement, every historical issued batch matching the removed pending ID
is completed, and provenance is preserved. Polls need not be replay-free. -/
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

/-- An accepted drain empties the pending vector and completes every historical issued batch
whose ID was pending, while provenance is preserved across every poll. -/
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
