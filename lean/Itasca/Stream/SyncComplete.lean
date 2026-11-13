import Itasca.Stream.FramingComplete
import Itasca.Stream.DriverRegions
import Itasca.Stream.Header
import Itasca.Stream.Source
import Itasca.Support.Result
import Itasca.Stream.SplitTotal
import Itasca.Stream.InvariantRetirement

/-!
Sections, each formerly its own module: SubmissionComplete, DriverComplete, Sync, SliceSound, SyncComplete.
-/

/-! ## SubmissionComplete -/

section

/-!
# Submission completeness

Completeness of `stream.submit_code_batches` over an available source and an accepting scheduler
(`StreamAcceptingScheduler.Accepts`). `StreamSubmission.CompleteInvariant` pairs the remaining
independently encoded and typed entries with the scheduler's queue and the pending vector.
`stream.submit_code_batches.complete` shows that submission succeeds and leaves a valid queue
whose batch IDs are exactly the pending IDs, ready for the final drain. The argument applies to Wasm 2.0.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleCode
/-- Typed entries of a concatenated list split into typed entries of each part. -/
theorem EntriesTyped.split {env i first second}
    (h : EntriesTyped env i (first ++ second)) :
    EntriesTyped env i first ∧ EntriesTyped env (i + first.length) second := by
  induction first generalizing i with
  | nil => exact ⟨.nil i, by simpa using h⟩
  | cons entry rest ih =>
    cases h with
    | cons he hs =>
      obtain ⟨hfirst, hsecond⟩ := ih hs
      exact ⟨.cons he hfirst, by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsecond⟩

end Itasca.ModuleCode

namespace Itasca.StreamSubmission
open ModuleBinary StreamAcceptingScheduler

/-- The scheduler's queue of valid work matches the pending vector, and the remaining bytes and
entries keep their independent encoding and typing. -/
def CompleteInvariant {V : Type} (Queued : U64 → List StreamBatch.Issued → V → Prop)
    (code : Slice U8) (env : metadata.Env) (id : U64) (config : stream.Config)
    (v : V) (pending : alloc.vec.Vec Usize) (pos func batchId : Usize) : Prop :=
  batchId.val ≤ func.val ∧ pending.length ≤ batchId.val ∧ pending.length ≤ config.max_batches.val ∧
    ∃ queue entries, Queued id queue v ∧ ValidQueue id queue ∧
      pending.val.Perm (queue.map StreamBatch.Issued.batch_id) ∧
      func.val + entries.length = env.func_type_indices.val.length ∧
      ModuleCode.EntriesTyped env func.val entries ∧
      At (Rep (Profile.CodeEncodingWithinLimits )) code pos entries (Slice.len code)

/-- A successful submission leaves a valid queue whose batch IDs are a permutation of the pending
IDs, so the final drain can retire exactly this queue. Errors are excluded. -/
def CompletePost {V : Type} (Queued : U64 → List StreamBatch.Issued → V → Prop)
    (id : U64) (config : stream.Config) :
    (core.result.Result (alloc.vec.Vec Usize) error.Error × V) → Prop
  | (.Ok pending, v) => ∃ queue, Queued id queue v ∧ ValidQueue id queue ∧
      pending.val.Perm (queue.map StreamBatch.Issued.batch_id) ∧ pending.length ≤ config.max_batches.val
  | (.Err _, _) => False

private def CompleteBodyPost {V : Type} (Queued : U64 → List StreamBatch.Issued → V → Prop)
    (code : Slice U8) (env : metadata.Env) (id : U64) (config : stream.Config) (func : Usize) :
    ControlFlow (V × alloc.vec.Vec Usize × Usize × Usize × Usize)
      (core.result.Result (alloc.vec.Vec Usize) error.Error × V) → Prop
  | .done result => CompletePost Queued id config result
  | .cont (v, pending, pos, next, batchId) =>
      CompleteInvariant Queued code env id config v pending pos next batchId ∧ func.val < next.val

private theorem increment (n bound : Usize) (h : n.val < bound.val) :
    ∃ next, (n + 1#usize : Result Usize) = .ok next ∧ next.val = n.val + 1 := by
  obtain ⟨next, hr, hv⟩ := WP.spec_imp_exists
    (UScalar.add_spec (x := n) (y := 1#usize) (by scalar_tac))
  exact ⟨next, hr, by simpa using hv⟩

private theorem resume_complete {S V : Type} (source : stream.Source S)
    (visitor : stream.StreamingVisitor V) (Queued : U64 → List StreamBatch.Issued → V → Prop)
    (config : stream.Config) (ha : Accepts visitor config Queued )
    (state : S) (moduleId : U64) (env : metadata.Env) (code : Slice U8)
    (environment tail : List U8) (hs : StreamSource.Available source state environment code.val tail)
    (henv : CodeEntry.Bounds env)
    (hlimits : Profile.EnvironmentWithinLimits env)
    (hcap : code.length ≤ limits.MAX_MODULE_BYTES.val)
    (v : V) (pending : alloc.vec.Vec Usize) (pos func batchId : Usize)
    (queue : List StreamBatch.Issued) (entries : List Code)
    (hv : Queued moduleId queue v) (hq : ValidQueue moduleId queue )
    (hp : pending.val.Perm (queue.map StreamBatch.Issued.batch_id))
    (hcount : func.val + entries.length = env.func_type_indices.val.length)
    (htyped : ModuleCode.EntriesTyped env func.val entries)
    (hbytes : At (Rep (Profile.CodeEncodingWithinLimits )) code pos entries (Slice.len code))
    (hbatch : batchId.val ≤ func.val) (hpending : pending.length ≤ batchId.val)
    (hfunc : func.val < env.func_type_indices.val.length)
    (hroom : pending.length < config.max_batches.val) :
    (do
      let r ← stream.get_next_batch source state (Slice.len code) pos func (alloc.vec.Vec.len env.func_type_indices) config.batch_bytes
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
        Result.ok (ControlFlow.done (r1, v))) ⦃ out => CompleteBodyPost Queued code env moduleId config func out ⦄ := by
  obtain ⟨finish, next, taken, rest, view, hframe, hframepost, heq, hne, hnext, hrestcount,
      htakenbytes, hrestbytes, hread, hspan, hrep⟩ := stream.get_next_batch.complete_view source state
    environment tail code hs (Slice.len code) pos func (alloc.vec.Vec.len env.func_type_indices)
    config.batch_bytes entries rfl (by simpa using hcap) (by simpa using hfunc)
    (by simpa using hcount) hbytes
  obtain ⟨hprogress, hfinishbound, hnextprogress, hnextbound⟩ := hframepost
  rw [heq] at htyped
  obtain ⟨htaken, hrest⟩ := htyped.split
  have hnexttyped : ModuleCode.EntriesTyped env next.val rest := by simpa [hnext] using hrest
  obtain ⟨nextPending, hpush, hpushval⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.push_spec pending batchId (by scalar_tac))
  obtain ⟨count, hsub, hsubval⟩ := WP.spec_imp_exists
    (UScalar.sub_spec (x := next) (y := func) (by scalar_tac))
  have hcountval : count.val = taken.length := by omega
  let issued : StreamBatch.Issued := ⟨moduleId, batchId, env, view, pos, func, count⟩
  have hbounded : issued.Bounded := by
    have hlen := hspan.length
    change finish.val = pos.val + view.length at hlen
    dsimp [issued, StreamBatch.Issued.Bounded]
    have hfunctions : next.val ≤ env.func_type_indices.val.length := by simpa using hnextbound
    have hfinishcap : finish.val ≤ limits.MAX_MODULE_BYTES.val :=
      le_trans (by simpa using hfinishbound) hcap
    simp only [Slice.length] at hlen ⊢
    omega
  have hvalid : Valid issued :=
    ⟨hbounded, henv, hlimits, taken, hcountval.symm, htaken, hrep⟩
  have hqueuelen : queue.length = pending.length := by
    simpa [alloc.vec.Vec.length] using hp.length_eq.symm
  obtain ⟨v', hsubmit, hv'⟩ := ha.submit moduleId queue issued v hv hvalid rfl (by omega)
  obtain ⟨nextId, hinc, hnextId⟩ := increment batchId (alloc.vec.Vec.len env.func_type_indices)
    (by simpa using (show batchId.val < env.func_type_indices.val.length by omega))
  simp only [issued, StreamBatch.Issued.seed] at hsubmit
  simp [hframe, core.result.Result.Insts.CoreOpsTry.branch, hread, hpush, hsub, hsubmit, hinc]
  change CompleteInvariant Queued code env moduleId config v' nextPending finish next nextId ∧ _
  constructor
  · refine ⟨by omega, ?_, ?_, queue ++ [issued], rest, hv', ?_, ?_, ?_, hnexttyped, hrestbytes⟩
    · change nextPending.val.length ≤ _
      rw [hpushval, List.length_append, List.length_singleton]
      change pending.val.length ≤ _ at hpending
      omega
    · change nextPending.val.length ≤ _
      rw [hpushval, List.length_append, List.length_singleton]
      change pending.val.length < _ at hroom
      omega
    · intro old hm
      rcases List.mem_append.mp hm with hm | hm
      · exact hq old hm
      · have he : old = issued := by simpa using hm
        exact he ▸ ⟨rfl, hvalid⟩
    · rw [hpushval, List.map_append, List.map_cons, List.map_nil]
      exact hp.append_right [batchId]
    · simpa using hrestcount.symm
  · simpa using hnextprogress

end Itasca.StreamSubmission

namespace Itasca.StreamSubmission
open ModuleBinary StreamAcceptingScheduler

private theorem body_complete {S V : Type} (source : stream.Source S)
    (visitor : stream.StreamingVisitor V) (Queued : U64 → List StreamBatch.Issued → V → Prop)
    (config : stream.Config) (ha : Accepts visitor config Queued )
    (state : S) (moduleId : U64) (env : metadata.Env) (code : Slice U8)
    (environment tail : List U8) (hs : StreamSource.Available source state environment code.val tail)
    (henv : CodeEntry.Bounds env)
    (hlimits : Profile.EnvironmentWithinLimits env)
    (hcap : code.length ≤ limits.MAX_MODULE_BYTES.val)
    (v : V) (pending : alloc.vec.Vec Usize) (pos func batchId : Usize)
    (hinv : CompleteInvariant Queued code env moduleId config v pending pos func batchId) :
    stream.submit_code_batches_loop.body source visitor moduleId state env.types env.imports
      env.globals env.exports env.elements env.data_count env.declared_funcs env.start
      env.func_type_indices env.func_types
      env.table_types env.mem_types env.global_types env.num_imported_funcs env.num_imported_globals
      (Slice.len code) config (alloc.vec.Vec.len env.func_type_indices) v pending pos func batchId
        ⦃ CompleteBodyPost Queued code env moduleId config func ⦄ := by
  obtain ⟨hbatch, hpending, hmax, queue, entries, hv, hq, hp, hcount, htyped, hbytes⟩ := hinv
  unfold stream.submit_code_batches_loop.body
  by_cases hmore : func < alloc.vec.Vec.len env.func_type_indices
  · rw [if_pos hmore]
    have hfunc : func.val < env.func_type_indices.val.length := by simpa using hmore
    by_cases hfull : alloc.vec.Vec.len pending ≥ config.max_batches
    · rw [if_pos hfull]
      have hnonempty : pending.val ≠ [] := by
        intro he
        have hz : pending.length = 0 := by simp [alloc.vec.Vec.length, he]
        have hp := ha.capacity_positive
        have hge : config.max_batches.val ≤ pending.length := by simpa using hfull
        omega
      obtain ⟨v', remaining, rest, hr, hv', hvalid, hids, hlen⟩ :=
        retire_complete visitor config Queued ha moduleId queue v pending hv hq hp hnonempty
      rw [hr]
      simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
      have hresume := resume_complete source visitor Queued config ha state moduleId env code
        environment tail hs henv hlimits hcap v' remaining pos func batchId rest entries
        hv' hvalid hids hcount htyped hbytes hbatch (by omega) hfunc (by omega)
      simp [core.result.Result.Insts.CoreOpsTry.branch] at hresume ⊢
      convert hresume using 1
      rfl
    · rw [if_neg hfull]
      exact resume_complete source visitor Queued config ha state moduleId env code
        environment tail hs henv hlimits hcap v pending pos func batchId queue entries
        hv hq hp hcount htyped hbytes hbatch hpending hfunc (by scalar_tac)
  · rw [if_neg hmore]
    have hn : env.func_type_indices.val.length ≤ func.val := by scalar_tac
    have he : entries = [] := by simpa using (show entries.length = 0 by omega)
    subst entries
    have hpos : pos = Slice.len code := hbytes.rep_nil.symm
    simp only [hpos, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact ⟨queue, hv, hq, hp, hmax⟩

end Itasca.StreamSubmission

namespace Itasca
open ModuleBinary StreamAcceptingScheduler

/-- The submission loop accepts independently encoded and typed entries, maintaining the queue of
outstanding work as its function cursor advances. -/
theorem stream.submit_code_batches_loop.complete_spec {S V : Type} (source : stream.Source S)
    (visitor : stream.StreamingVisitor V) (Queued : U64 → List StreamBatch.Issued → V → Prop)
    (config : stream.Config) (ha : Accepts visitor config Queued )
    (state : S) (moduleId : U64) (env : metadata.Env) (code : Slice U8)
    (environment tail : List U8) (hs : StreamSource.Available source state environment code.val tail)
    (henv : CodeEntry.Bounds env)
    (hlimits : Profile.EnvironmentWithinLimits env)
    (hcap : code.length ≤ limits.MAX_MODULE_BYTES.val)
    (v : V) (pending : alloc.vec.Vec Usize) (pos func batchId : Usize)
    (hinv : StreamSubmission.CompleteInvariant Queued code env moduleId config v pending pos func batchId) :
    stream.submit_code_batches_loop source visitor moduleId state env.types env.imports
      env.globals env.exports env.elements env.data_count env.declared_funcs env.start
      env.func_type_indices env.func_types
      env.table_types env.mem_types env.global_types env.num_imported_funcs env.num_imported_globals
      (Slice.len code) config v pending pos func batchId (alloc.vec.Vec.len env.func_type_indices)
        ⦃ StreamSubmission.CompletePost Queued moduleId config ⦄ := by
  unfold stream.submit_code_batches_loop
  apply loop.spec_decr_nat (fun s => env.func_type_indices.val.length - s.2.2.2.1.val)
    (fun s => StreamSubmission.CompleteInvariant Queued code env moduleId config
      s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2)
  · rintro ⟨v', pending', pos', func', batchId'⟩ h
    apply WP.spec_mono (StreamSubmission.body_complete source visitor Queued config ha state moduleId env
      code environment tail hs henv hlimits hcap v' pending' pos' func' batchId' h)
    intro out hout
    cases out with
    | done result => exact hout
    | cont next =>
      obtain ⟨v'', pending'', pos'', func'', batchId''⟩ := next
      obtain ⟨hinv'', hprogress⟩ := hout
      refine ⟨hinv'', ?_⟩
      obtain ⟨_, _, _, queue, entries, _, _, _, hcount, _, _⟩ := hinv''
      dsimp only
      omega
  · exact hinv

/-- From an independently encoded and typed code region and an accepting scheduler policy,
`stream.submit_code_batches` submits and retires batches successfully. The remaining valid queue
matches the pending IDs for the final drain. -/
theorem stream.submit_code_batches.complete {S V : Type} (source : stream.Source S)
    (visitor : stream.StreamingVisitor V) (Queued : U64 → List StreamBatch.Issued → V → Prop)
    (config : stream.Config) (ha : Accepts visitor config Queued )
    (state : S) (moduleId : U64) (env : metadata.Env) (code : Slice U8) (start : Usize)
    (environment tail : List U8) (hs : StreamSource.Available source state environment code.val tail)
    (henv : CodeEntry.Bounds env)
    (hlimits : Profile.EnvironmentWithinLimits env)
    (hcap : code.length ≤ limits.MAX_MODULE_BYTES.val)
    (entries : List Code) (hcount : entries.length = env.func_type_indices.val.length)
    (htyped : ModuleCode.EntriesTyped env 0 entries)
    (hbytes : At (Rep (Profile.CodeEncodingWithinLimits )) code start entries (Slice.len code))
    (v : V) (hv : Queued moduleId [] v) :
    ∃ pending v' queue,
      stream.submit_code_batches source visitor moduleId state env (Slice.len code) start config v =
        .ok (.Ok pending, v') ∧ Queued moduleId queue v' ∧ ValidQueue moduleId queue ∧
      pending.val.Perm (queue.map StreamBatch.Issued.batch_id) ∧
      pending.length ≤ config.max_batches.val := by
  have hi : StreamSubmission.CompleteInvariant Queued code env moduleId config v
      (alloc.vec.Vec.new _) start 0#usize 0#usize := by
    refine ⟨by simp, by simp [alloc.vec.Vec.new], by simp [alloc.vec.Vec.new],
      [], entries, hv, ?_, ?_, by simpa using hcount, htyped, hbytes⟩
    · simp [ValidQueue]
    · simp [alloc.vec.Vec.new]
  obtain ⟨⟨r, v'⟩, hr, hp⟩ := WP.spec_imp_exists
    (stream.submit_code_batches_loop.complete_spec source visitor Queued config ha state moduleId env code
      environment tail hs henv hlimits hcap v (alloc.vec.Vec.new _) start 0#usize 0#usize hi)
  cases r with
  | Err e => exact False.elim hp
  | Ok pending =>
    obtain ⟨queue, hv', hvalid, hids, hmax⟩ := hp
    exact ⟨pending, v', queue, hr, hv', hvalid, hids, hmax⟩

end Itasca

end

/-! ## DriverComplete -/

section

/-!
# Streaming driver completeness

`stream.validate_streaming.complete_core`: an independently encoded, elaborated and typed
module within the implementation limits is accepted by `stream.validate_streaming`, provided
the source makes the canonical split of the input available (`StreamSource.CanonicalAvailable`)
and the scheduler is accepting (`StreamAcceptingScheduler.Accepts`). The returned environment and
delivered tail describe the same raw module, including public metadata
(`Matches`, `AccessorTypes`). Both premises on the embedding are required: completeness fails if
reads are unavailable or workers do not accept. `Itasca/Results/Stream` states the public
`profile_complete`.
-/

open Aeneas Aeneas.Std

namespace Itasca.StreamRun
/-- The recorded remaining-phase calls compose to the driver result. -/
theorem Remaining.run {S V : Type} {source : stream.Source S}
    {visitor : stream.StreamingVisitor V} {id state env environmentLength before after}
    (h : Remaining source visitor id state env environmentLength before after ) :
    stream.validate_remaining source visitor id state env environmentLength before =
      .ok (.Ok (), after) := by
  simp [stream.validate_remaining, h.length_call, h.code_bound, h.header_call,
    h.configured_call, h.batch_bytes_positive, h.max_batches_positive, h.submit_call,
    h.end_call, h.tail_call, h.module_bound, h.region_call, h.decode_tail,
    h.ready_call, h.drain_call, core.result.Result.Insts.CoreOpsTry.branch]

/-- An accepted phase trace executes independently of the initial `storage` argument. -/
theorem Accepted.run {S V : Type} {source : stream.Source S}
    {visitor : stream.StreamingVisitor V} {id state before after env}
    (h : Accepted source visitor id state before after env ) (storage : metadata.Env) :
    stream.validate_streaming source visitor id state before storage =
      .ok (.Ok (), after, env) := by
  simp [stream.validate_streaming, h.environment_call, h.environment_bound,
    h.region_call, h.decode_environment, h.remaining.run,
    core.result.Result.Insts.CoreOpsTry.branch]

end Itasca.StreamRun

namespace Itasca.StreamCompleteRegions
/-- The concrete splitter and slice operations determine a unique source. -/
theorem Split.unique {data : Slice U8} {first second : stream.SliceSource}
    (hfirst : Split data first) (hsecond : Split data second) : first = second := by
  obtain ⟨a, b, hs, he, hc, ht⟩ := hfirst
  obtain ⟨a', b', hs', he', hc', ht'⟩ := hsecond
  have hb : a = a' ∧ b = b' := by simpa using hs.symm.trans hs'
  obtain ⟨rfl, rfl⟩ := hb
  have heq : first.env = second.env := by simpa using he.symm.trans he'
  have hcq : first.code = second.code := by simpa using hc.symm.trans hc'
  have htq : first.tail = second.tail := by simpa using ht.symm.trans ht'
  cases first
  cases second
  simp_all

end Itasca.StreamCompleteRegions

namespace Itasca.StreamSource

/-- Canonical availability transfers to any split of `data` produced by the splitter. -/
theorem CanonicalAvailable.for_split {S : Type} {source : stream.Source S} {state data regions}
    (h : CanonicalAvailable source state data) (hsplit : StreamCompleteRegions.Split data regions) :
    Available source state regions.env.val regions.code.val regions.tail.val := by
  obtain ⟨other, hother, ha⟩ := h
  rw [hsplit.unique hother]
  exact ha

end Itasca.StreamSource

namespace Itasca.StreamCompleteRegions
open StreamAcceptingScheduler

private theorem remaining_of_submission {S V : Type} (source : stream.Source S)
    (visitor : stream.StreamingVisitor V) (config : stream.Config)
    (Queued : U64 → List StreamBatch.Issued → V → Prop)
    (hp : Accepts visitor config Queued ) (id : U64) (state : S)
    (data : Slice U8) (raw : ModuleBinary.Module) (regions : stream.SliceSource)
    (env : metadata.Env) (tail : metadata.Tail) (hc : Certificate data raw regions env tail )
    (ha : StreamSource.Available source state regions.env.val regions.code.val regions.tail.val)
    (before configured submitted : V) (entries : Usize) (codeEnd : Usize)
    (pending : alloc.vec.Vec Usize) (queue : List StreamBatch.Issued)
    (hlen : source.code_len state = .ok (Slice.len regions.code))
    (hbound : limits.add_offset (Slice.len regions.env) (Slice.len regions.code) = .ok (.Ok codeEnd))
    (hend : codeEnd.val = regions.env.length + regions.code.length)
    (hheader : stream.read_code_header source state (Slice.len regions.code) env = .ok (.Ok entries))
    (hconfig : visitor.environment_ready before env = .ok (.Ok config, configured))
    (hsubmit : stream.submit_code_batches source visitor id state env (Slice.len regions.code)
      entries config configured = .ok (.Ok pending, submitted))
    (hv : Queued id queue submitted) (hq : ValidQueue id queue )
    (hids : pending.val.Perm (queue.map StreamBatch.Issued.batch_id)) :
    ∃ after, ∃ run : StreamRun.Remaining source visitor id state env (Slice.len regions.env) before after ,
      run.tail = tail ∧ Queued id [] after := by
  obtain ⟨ended, he, hve⟩ := hp.code_end id queue submitted hv
  obtain ⟨bytes, hread, hbytes⟩ := ha.tail_read
  have heq : bytes = regions.tail := Slice.ext _ _ hbytes
  subst bytes
  have hwhole : codeEnd.val + regions.tail.length ≤ limits.MAX_MODULE_BYTES.val := by
    have hh := congrArg List.length hc.bytes
    have hb := hc.bounded
    simp only [List.length_append, Slice.length] at hh hb hend ⊢
    omega
  obtain ⟨moduleEnd, hmodule, _⟩ := limits.add_offset.complete codeEnd (Slice.len regions.tail)
    (by simpa using hwhole)
  obtain ⟨region, hr, hvr⟩ := hp.region id queue ended .Tail hve
  obtain ⟨decoded, hd⟩ := metadata.validate_tail_with.accepted_lift
    visitor.metadataModuleVisitorInst hp.custom_accepts regions.tail 0#usize env region tail hc.tail_accepted
  have hvd := metadata.validate_tail_with.accepted_invariant visitor.metadataModuleVisitorInst
    (Queued id queue) (hp.custom_preserves id queue) regions.tail 0#usize env region tail decoded hd hvr
  obtain ⟨ready, ht, hvt⟩ := hp.tail_ready id queue decoded tail hvd
  obtain ⟨after, remaining, hfinish, _, hva⟩ :=
    drain_complete visitor config Queued hp id queue ready pending hvt hq hids
  refine ⟨after, ⟨Slice.len regions.code, codeEnd, entries, config, configured, pending,
    submitted, ended, regions.tail, moduleEnd, region, tail, decoded, ready, remaining,
    hlen, hbound, hheader, hconfig, ?_, ?_, hsubmit, he, hread, hmodule, hr, hd, ht, hfinish⟩,
    rfl, hva⟩
  · have := hp.batch_positive
    scalar_tac
  · have := hp.capacity_positive
    scalar_tac

end Itasca.StreamCompleteRegions

namespace Itasca.StreamCompleteRegions
open StreamAcceptingScheduler

/-- Independent region certificates drive every phase after the environment, including workers
retired in any order and the delivery of the tail. -/
theorem remaining_complete {S V : Type} (source : stream.Source S)
    (visitor : stream.StreamingVisitor V) (config : stream.Config)
    (Queued : U64 → List StreamBatch.Issued → V → Prop)
    (hp : Accepts visitor config Queued ) (id : U64) (state : S)
    (data : Slice U8) (raw : ModuleBinary.Module) (regions : stream.SliceSource)
    (env : metadata.Env) (tail : metadata.Tail) (hc : Certificate data raw regions env tail )
    (ha : StreamSource.Available source state regions.env.val regions.code.val regions.tail.val)
    (before : V) (hv : Queued id [] before) :
    ∃ after, ∃ run : StreamRun.Remaining source visitor id state env (Slice.len regions.env) before after ,
      run.tail = tail ∧ Queued id [] after := by
  obtain ⟨len, hlen, hlenval⟩ := ha.code_len_read
  have hlenEq : len = Slice.len regions.code := UScalar.eq_of_val_eq hlenval
  subst len
  have hcap : regions.env.length + regions.code.length ≤ limits.MAX_MODULE_BYTES.val := by
    have hh := congrArg List.length hc.bytes
    have hb := hc.bounded
    simp only [List.length_append, Slice.length] at hh hb ⊢
    omega
  have hcodeCap : regions.code.length ≤ limits.MAX_MODULE_BYTES.val := by omega
  obtain ⟨codeEnd, hbound, hend⟩ := limits.add_offset.complete
    (Slice.len regions.env) (Slice.len regions.code) (by simpa using hcap)
  obtain ⟨entries, hheader, hbytes⟩ := hc.code
  have hheaderRun := stream.read_code_header.complete source state (Slice.len regions.code)
    env entries regions.code regions.env.val regions.tail.val ha rfl hcodeCap hheader
  obtain ⟨configured, hconfig, hconfigured⟩ := hp.environment id [] before env hv
  obtain ⟨pending, submitted, queue, hsubmit, hqueued, hvalid, hids, _⟩ :=
    stream.submit_code_batches.complete source visitor Queued config hp state id env regions.code
      entries regions.env.val regions.tail.val ha hc.entry_bounds hc.signature_limits hcodeCap
      raw.codes hc.code_count hc.typed hbytes configured hconfigured
  exact remaining_of_submission source visitor config Queued hp id state data raw regions env tail
    hc ha before configured submitted entries codeEnd pending queue hlen hbound
    (by simpa using hend) hheaderRun hconfig hsubmit hqueued hvalid hids

/-- `stream.validate_streaming` accepts the regions of a `Certificate`. The returned run names the
tail supplied to `tail_ready`. -/
theorem complete_certificate {S V : Type} (source : stream.Source S)
    (visitor : stream.StreamingVisitor V) (config : stream.Config)
    (Queued : U64 → List StreamBatch.Issued → V → Prop)
    (hp : Accepts visitor config Queued ) (id : U64) (state : S)
    (data : Slice U8) (raw : ModuleBinary.Module) (regions : stream.SliceSource)
    (env : metadata.Env) (tail : metadata.Tail) (hc : Certificate data raw regions env tail )
    (ha : StreamSource.Available source state regions.env.val regions.code.val regions.tail.val)
    (before : V) (storage : metadata.Env) (hv : Queued id [] before) :
    ∃ after, ∃ run : StreamRun.Accepted source visitor id state before after env ,
      stream.validate_streaming source visitor id state before storage = .ok (.Ok (), after, env) ∧
      run.remaining.tail = tail ∧ Queued id [] after := by
  obtain ⟨bytes, hread, hbytes⟩ := ha.environment_read
  have heq : bytes = regions.env := Slice.ext _ _ hbytes
  subst bytes
  have hcap : regions.env.length ≤ limits.MAX_MODULE_BYTES.val := by
    have hh := congrArg List.length hc.bytes
    have hb := hc.bounded
    simp only [List.length_append, Slice.length] at hh hb ⊢
    omega
  obtain ⟨envLen, hbound, hlen⟩ := limits.add_offset.complete 0#usize (Slice.len regions.env)
    (by simpa using hcap)
  have hlenEq : envLen = Slice.len regions.env := by apply UScalar.eq_of_val_eq; simpa using hlen
  subst envLen
  obtain ⟨region, hregion, hvregion⟩ := hp.region id [] before .Environment hv
  obtain ⟨decoded, hdecode⟩ := metadata.validate_env_with.accepted_lift
    visitor.metadataModuleVisitorInst hp.custom_accepts regions.env region env
    (Slice.len regions.env) hc.environment
  have hvdecoded := metadata.validate_env_with.accepted_invariant visitor.metadataModuleVisitorInst
    (Queued id []) (hp.custom_preserves id []) regions.env region env (Slice.len regions.env)
    decoded hdecode hvregion
  obtain ⟨after, remaining, htail, hvafter⟩ := remaining_complete source visitor config Queued hp
    id state data raw regions env tail hc ha decoded hvdecoded
  let run : StreamRun.Accepted source visitor id state before after env :=
    ⟨regions.env, Slice.len regions.env, region, decoded, hread, hbound, hregion, hdecode, remaining⟩
  exact ⟨after, run, run.run storage, htail, hvafter⟩

end Itasca.StreamCompleteRegions

namespace Itasca
open ModuleBinary ModuleElaboration

/-- Independently encoded, elaborated, typed modules within the implementation limits are
accepted by `stream.validate_streaming` under canonical available reads and an accepting
scheduler. The returned environment and delivered tail describe the same raw module, including
public metadata. -/
theorem stream.validate_streaming.complete_core {S V : Type}
    (source : stream.Source S) (visitor : stream.StreamingVisitor V)
    (config : stream.Config) (Queued : U64 → List StreamBatch.Issued → V → Prop)
    (ha : StreamAcceptingScheduler.Accepts visitor config Queued )
    (id : U64) (state : S) (before : V) (storage : metadata.Env)
    (data : Slice U8) (raw : ModuleBinary.Module)
    (hb : ModuleEncodingWithinLimits raw data.val )
    (hsignatures : ModuleSignaturesWithinLimits raw)
    (he : Elaborates raw (moduleOf raw))
    (ht : Module_ok (moduleOf raw)) (hp : Restrictions raw )
    (hs : StreamSource.CanonicalAvailable source state data) (hv : Queued id [] before) :
    ∃ env after, ∃ run : StreamRun.Accepted source visitor id state before after env ,
      stream.validate_streaming source visitor id state before storage = .ok (.Ok (), after, env) ∧
      Matches env run.remaining.tail raw ∧ AccessorTypes env raw ∧ Queued id [] after := by
  obtain ⟨regions, env, tail, hc⟩ := StreamCompleteRegions.prepare data raw hb hsignatures he ht hp
  obtain ⟨after, run, hrun, htail, hvafter⟩ := StreamCompleteRegions.complete_certificate
    source visitor config Queued ha id state data raw regions env tail hc
    (hs.for_split hc.split) before storage hv
  exact ⟨env, after, run, hrun, by simpa [htail] using hc.realization, hc.metadata, hvafter⟩

end Itasca

end

/-! ## Sync -/

section

/-!
# Synchronous worker

The private synchronous scheduler `stream.SyncVisitor` that `validate_module` supplies to the
driver. It has one `completed` slot: submission runs `stream.CodeBatch.validate_all` on the seed
immediately and stores the result, and polling takes it. `StreamSync.provenance` and
`StreamSync.callbacks_total` show that it meets the `StreamScheduler.Provenance` and
`StreamScheduler.CallbacksTotal` contracts for module validation, so no embedding obligation remains
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

theorem tail_ready (state : stream.SyncVisitor) (tail : metadata.Tail) :
    (sync).tail_ready state tail = .ok (.Ok (), { state with tail := some tail }) := rfl

theorem environment_ready (state : stream.SyncVisitor) (env : metadata.Env) :
    (sync).environment_ready state env =
      .ok (.Ok { batch_bytes := 25000#usize, max_batches := 1#usize }, state) := rfl

theorem custom_accepts : ModuleTail.HooksAccept (sync).metadataModuleVisitorInst := by
  intro state chunk
  exact ⟨state, rfl⟩

theorem custom_region (state : stream.SyncVisitor) (region : stream.Region) :
    (sync).custom_region state region = .ok state := rfl

theorem code_end (state : stream.SyncVisitor) :
    (sync).code_end state = .ok (.Ok (), state) := rfl

/-- Submission runs the extracted worker even on malformed bytes and stores its reachable result.
Submission succeeding does not mean that `stream.CodeBatch.finish` passes. -/
theorem submit (state : stream.SyncVisitor) (issued : StreamBatch.Issued)
    (hissued : issued.Bounded) (hbound : CodeEntry.Bounds issued.env) :
    ∃ batch, (sync).submit_code_batch state issued.seed =
      .ok (.Ok (), { state with completed := some batch }) ∧
      StreamBatch.Reachable issued batch := by
  obtain ⟨batch, hr, hp⟩ := WP.spec_imp_exists
    (stream.CodeBatch.validate_all.reachable issued issued.seed hissued hbound .seed)
  exact ⟨batch, by simp [stream.SyncVisitor.Insts.ItascaStreamStreamingVisitor.submit_code_batch, hr], hp⟩

/-- The synchronous scheduler satisfies `StreamScheduler.Provenance` across every callback,
including custom regions and tail delivery. -/
theorem provenance : StreamScheduler.Provenance sync Tracks := by
  constructor
  · intro id history state chunk after hcall
    have he : state = after := by
      simpa [stream.SyncVisitor.Insts.ItascaMetadataModuleVisitor,
        metadata.ModuleVisitor.on_custom_section.default] using hcall
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
  · intro id history issued state after _ _ hissued hbound hfresh hcall
    obtain ⟨batch, hr, hreach⟩ := submit state issued hissued hbound
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
theorem callbacks_total : StreamScheduler.CallbacksTotal sync := by
  constructor
  · intro state chunk
    exact ⟨(.Ok (), state), rfl⟩
  · intro state region
    exact ⟨state, rfl⟩
  · intro state env
    exact ⟨_, environment_ready state env⟩
  · intro state issued hissued hbound
    obtain ⟨batch, hr, _⟩ := submit state issued hissued hbound
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

end

/-! ## SliceSound -/

section

/-!
# Contiguous adapter soundness and termination

`stream.validate_module_slice` splits a contiguous module with `stream.find_code_region` and runs
`stream.validate_streaming` over a `stream.SliceSource` and the synchronous scheduler; the public
`metadata.validate_module` is this function. `profile_total` shows it returns on arbitrary bytes and
`profile_sound` shows that acceptance gives `ModuleSound.Validated`. Source and scheduler
obligations are discharged by `stream.SliceSource.coherent` and `StreamSync.provenance`, so no
embedding premise remains. `profile_spec` combines both.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- `stream.validate_module_slice` returns on arbitrary input bytes. Its slice source and
synchronous scheduler satisfy every callback premise. -/
theorem stream.validate_module_slice.profile_total (bytes : Slice U8) :
    ∃ r, stream.validate_module_slice bytes = .ok r := by
  obtain ⟨⟨first, last⟩, hsplit, _⟩ := WP.spec_imp_exists (stream.find_code_region.spec bytes)
  obtain ⟨environment, code, tail, he, hc, ht, _⟩ := stream.find_code_region.slices bytes first last hsplit
  obtain ⟨env, henv, _⟩ := WP.spec_imp_exists metadata.Env.new.spec
  obtain ⟨⟨r, visitor, decoded⟩, hr⟩ := stream.validate_streaming.total_core
    stream.SliceSource.Insts.ItascaStreamSource stream.SyncVisitor.Insts.ItascaStreamStreamingVisitor
    0#u64 ⟨environment, code, tail⟩ ⟨none, none⟩ env
    (stream.SliceSource.callbacks_total _) StreamSync.callbacks_total
  unfold stream.validate_module_slice
  simp only [hsplit, bind_ok, Std.uncurry]
  simp only [he, hc, ht, henv, bind_ok, hr, Std.uncurry]
  cases r with
  | Err e => exact ⟨.Err e, by simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]⟩
  | Ok u =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    cases visitor.tail with
    | none => exact ⟨.Err .Host, rfl⟩
    | some tail => exact ⟨.Ok ⟨decoded, tail⟩, rfl⟩

/-- If `stream.validate_module_slice` accepts, the returned environment and tail are those of the
accepted streaming run, and they validate the input bytes. -/
theorem stream.validate_module_slice.profile_sound (bytes : Slice U8) (decoded : metadata.Module)
    (h : stream.validate_module_slice bytes = .ok (.Ok decoded)) :
    ModuleSound.Validated bytes decoded := by
  obtain ⟨⟨first, last⟩, hsplit, _⟩ := WP.spec_imp_exists (stream.find_code_region.spec bytes)
  obtain ⟨environment, code, tail, he, hc, ht, hbytes⟩ := stream.find_code_region.slices bytes first last hsplit
  obtain ⟨storage, hstorage, _⟩ := WP.spec_imp_exists metadata.Env.new.spec
  simp only [stream.validate_module_slice, hsplit, bind_ok, Std.uncurry] at h
  simp only [he, hc, ht, hstorage, bind_ok] at h
  obtain ⟨⟨r, visitor, env⟩, hrun, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
  | Ok u =>
    cases u
    simp only [Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at h
    cases hstored : visitor.tail with
    | none => simp [hstored] at h
    | some stored =>
      simp [hstored] at h
      subst decoded
      obtain ⟨run, hvalid, _⟩ := stream.validate_streaming.sound_core
        stream.SliceSource.Insts.ItascaStreamSource stream.SyncVisitor.Insts.ItascaStreamStreamingVisitor
        StreamSync.Tracks StreamSync.provenance 0#u64 ⟨environment, code, tail⟩ ⟨none, none⟩ visitor
        storage env bytes environment code tail (stream.SliceSource.coherent _) hbytes
        (StreamSync.tracks_empty _ _) hrun
      have hready := run.remaining.ready_call
      rw [StreamSync.tail_ready] at hready
      have hreadyEq : run.remaining.ready = { run.remaining.decodedTail with tail := some run.remaining.tail } := by
        simpa using hready.symm
      have hfinal := StreamSync.retire_all_tail 0#u64 run.remaining.ready visitor
        run.remaining.pending run.remaining.remaining run.remaining.drain_call
      rw [hreadyEq, hstored] at hfinal
      have htail : stored = run.remaining.tail := by simpa using hfinal
      simpa [htail] using hvalid

/-- Arbitrary inputs return normally, and every accepted result is `ModuleSound.Validated`, which
includes the independent module certificate and the returned metadata. -/
theorem stream.validate_module_slice.profile_spec (bytes : Slice U8) :
    stream.validate_module_slice bytes ⦃ r => match r with
      | .Ok decoded => ModuleSound.Validated bytes decoded
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr⟩ := stream.validate_module_slice.profile_total bytes
  rw [hr]
  simp only [WP.spec_ok]
  cases r with
  | Err _ => trivial
  | Ok decoded => exact stream.validate_module_slice.profile_sound bytes decoded hr

end Itasca

end

/-! ## SyncComplete -/

section

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
theorem accepts : StreamAcceptingScheduler.Accepts sync
    { batch_bytes := 25000#usize, max_batches := 1#usize } Queued := by
  constructor
  · decide
  · decide
  · exact custom_accepts
  · intro id queue state chunk after hcall hqueue
    have he : state = after := by
      simpa [stream.SyncVisitor.Insts.ItascaMetadataModuleVisitor,
        metadata.ModuleVisitor.on_custom_section.default] using hcall
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
      issued entries hvalid.bounded hn ht hvalid.limits hvalid.entry_bounds hb
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
theorem delivered_tail {S : Type} {source : stream.Source S} {id : U64} {state : S}
    {env : metadata.Env} {environmentLength : Usize} {before after : stream.SyncVisitor}
    (run : StreamRun.Remaining source sync id state env environmentLength before after) :
    after.tail = some run.tail := by
  have hready := run.ready_call
  rw [tail_ready] at hready
  have hreadyEq : run.ready = { run.decodedTail with tail := some run.tail } := by
    simpa using hready.symm
  have hfinal := retire_all_tail id run.ready after run.pending run.remaining run.drain_call
  simpa [hreadyEq] using hfinal

end Itasca.StreamSync

end
