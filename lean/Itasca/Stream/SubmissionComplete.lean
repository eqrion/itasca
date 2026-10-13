import Itasca.Stream.FramingComplete
import Itasca.Stream.SchedulerComplete

/-!
# Submission completeness

Completeness of `stream.submit_code_batches` over an available source and an accepting scheduler
(`StreamAcceptingScheduler.Accepts`). `StreamSubmission.CompleteInvariant` pairs the remaining
independently encoded and typed entries with the scheduler's queue and the pending vector.
`stream.submit_code_batches.complete` shows that submission succeeds and leaves a valid queue
whose batch IDs are exactly the pending IDs, ready for the final drain. Both profiles are covered
through the `profile` parameter.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleCode

variable {profile : ValidationProfile}

/-- Typed entries of a concatenated list split into typed entries of each part. -/
theorem EntriesTyped.split {env i first second}
    (h : EntriesTyped (profile := profile) env i (first ++ second)) :
    EntriesTyped (profile := profile) env i first ∧ EntriesTyped (profile := profile) env (i + first.length) second := by
  induction first generalizing i with
  | nil => exact ⟨.nil i, by simpa using h⟩
  | cons entry rest ih =>
    cases h with
    | cons he hs =>
      obtain ⟨hfirst, hsecond⟩ := ih hs
      exact ⟨.cons he hfirst, by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsecond⟩

end Itasca.ModuleCode

namespace Itasca.StreamSubmission

variable {profile : ValidationProfile}

open ModuleBinary StreamAcceptingScheduler

/-- The scheduler's queue of valid work matches the pending vector, and the remaining bytes and
entries keep their independent encoding and typing. -/
def CompleteInvariant {V : Type} (Queued : U64 → List StreamBatch.Issued → V → Prop)
    (code : Slice U8) (env : module.Env) (id : U64) (config : stream.Config)
    (v : V) (pending : alloc.vec.Vec Usize) (pos func batchId : Usize)
    (profile : ValidationProfile := .Wasm1) : Prop :=
  batchId.val ≤ func.val ∧ pending.length ≤ batchId.val ∧ pending.length ≤ config.max_batches.val ∧
    ∃ queue entries, Queued id queue v ∧ ValidQueue id queue profile ∧
      pending.val.Perm (queue.map StreamBatch.Issued.batch_id) ∧
      func.val + entries.length = env.func_type_indices.val.length ∧
      ModuleCode.EntriesTyped (profile := profile) env func.val entries ∧
      At (Rep (Profile.CodeEncodingWithinLimits profile)) code pos entries (Slice.len code)

/-- A successful submission leaves a valid queue whose batch IDs are a permutation of the pending
IDs, so the final drain can retire exactly this queue. Errors are excluded. -/
def CompletePost {V : Type} (Queued : U64 → List StreamBatch.Issued → V → Prop)
    (id : U64) (config : stream.Config)
    (profile : ValidationProfile := .Wasm1) :
    (core.result.Result (alloc.vec.Vec Usize) error.Error × V) → Prop
  | (.Ok pending, v) => ∃ queue, Queued id queue v ∧ ValidQueue id queue profile ∧
      pending.val.Perm (queue.map StreamBatch.Issued.batch_id) ∧ pending.length ≤ config.max_batches.val
  | (.Err _, _) => False

private def CompleteBodyPost {V : Type} (Queued : U64 → List StreamBatch.Issued → V → Prop)
    (code : Slice U8) (env : module.Env) (id : U64) (config : stream.Config) (func : Usize)
    (profile : ValidationProfile := .Wasm1) :
    ControlFlow (V × alloc.vec.Vec Usize × Usize × Usize × Usize)
      (core.result.Result (alloc.vec.Vec Usize) error.Error × V) → Prop
  | .done result => CompletePost (profile := profile) Queued id config result
  | .cont (v, pending, pos, next, batchId) =>
      CompleteInvariant (profile := profile) Queued code env id config v pending pos next batchId ∧ func.val < next.val

private theorem increment (n bound : Usize) (h : n.val < bound.val) :
    ∃ next, (n + 1#usize : Result Usize) = .ok next ∧ next.val = n.val + 1 := by
  obtain ⟨next, hr, hv⟩ := WP.spec_imp_exists
    (UScalar.add_spec (x := n) (y := 1#usize) (by scalar_tac))
  exact ⟨next, hr, by simpa using hv⟩

private theorem resume_complete {S V : Type} (source : stream.Source S)
    (visitor : stream.StreamingVisitor V) (Queued : U64 → List StreamBatch.Issued → V → Prop)
    (config : stream.Config) (ha : Accepts visitor config Queued profile)
    (state : S) (moduleId : U64) (env : module.Env) (code : Slice U8)
    (environment tail : List U8) (hs : StreamSource.Available source state environment code.val tail)
    (henv : CodeEntry.Bounds env) (hprofile : Profile.Environment profile env)
    (hlimits : Profile.EnvironmentWithinLimits profile env)
    (hcap : code.length ≤ limits.MAX_MODULE_BYTES.val)
    (v : V) (pending : alloc.vec.Vec Usize) (pos func batchId : Usize)
    (queue : List StreamBatch.Issued) (entries : List Code)
    (hv : Queued moduleId queue v) (hq : ValidQueue moduleId queue profile)
    (hp : pending.val.Perm (queue.map StreamBatch.Issued.batch_id))
    (hcount : func.val + entries.length = env.func_type_indices.val.length)
    (htyped : ModuleCode.EntriesTyped (profile := profile) env func.val entries)
    (hbytes : At (Rep (Profile.CodeEncodingWithinLimits profile)) code pos entries (Slice.len code))
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
            { module_id := moduleId, batch_id := batchId, profile := profile, env := env, code := bytes,
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
        Result.ok (ControlFlow.done (r1, v))) ⦃ out => CompleteBodyPost (profile := profile) Queued code env moduleId config func out ⦄ := by
  obtain ⟨finish, next, taken, rest, view, hframe, hframepost, heq, hne, hnext, hrestcount,
      htakenbytes, hrestbytes, hread, hspan, hrep⟩ := stream.get_next_batch.complete_view source state
    environment tail code hs (Slice.len code) pos func (alloc.vec.Vec.len env.func_type_indices)
    config.batch_bytes entries rfl (by simpa using hcap) (by simpa using hfunc)
    (by simpa using hcount) hbytes
  obtain ⟨hprogress, hfinishbound, hnextprogress, hnextbound⟩ := hframepost
  rw [heq] at htyped
  obtain ⟨htaken, hrest⟩ := htyped.split
  have hnexttyped : ModuleCode.EntriesTyped (profile := profile) env next.val rest := by simpa [hnext] using hrest
  obtain ⟨nextPending, hpush, hpushval⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.push_spec pending batchId (by scalar_tac))
  obtain ⟨count, hsub, hsubval⟩ := WP.spec_imp_exists
    (UScalar.sub_spec (x := next) (y := func) (by scalar_tac))
  have hcountval : count.val = taken.length := by omega
  let issued : StreamBatch.Issued := ⟨moduleId, batchId, env, view, pos, func, count, profile⟩
  have hbounded : issued.Bounded := by
    have hlen := hspan.length
    change finish.val = pos.val + view.length at hlen
    dsimp [issued, StreamBatch.Issued.Bounded]
    have hfunctions : next.val ≤ env.func_type_indices.val.length := by simpa using hnextbound
    have hfinishcap : finish.val ≤ limits.MAX_MODULE_BYTES.val :=
      le_trans (by simpa using hfinishbound) hcap
    simp only [Slice.length] at hlen ⊢
    omega
  have hvalid : Valid issued profile :=
    ⟨rfl, hbounded, henv, hprofile, hlimits, taken, hcountval.symm, htaken, hrep⟩
  have hqueuelen : queue.length = pending.length := by
    simpa [alloc.vec.Vec.length] using hp.length_eq.symm
  obtain ⟨v', hsubmit, hv'⟩ := ha.submit moduleId queue issued v hv hvalid rfl (by omega)
  obtain ⟨nextId, hinc, hnextId⟩ := increment batchId (alloc.vec.Vec.len env.func_type_indices)
    (by simpa using (show batchId.val < env.func_type_indices.val.length by omega))
  simp only [issued, StreamBatch.Issued.seed] at hsubmit
  simp [hframe, core.result.Result.Insts.CoreOpsTry.branch, hread, hpush, hsub, hsubmit, hinc]
  change CompleteInvariant (profile := profile) Queued code env moduleId config v' nextPending finish next nextId ∧ _
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

variable {profile : ValidationProfile}

open ModuleBinary StreamAcceptingScheduler

private theorem body_complete {S V : Type} (source : stream.Source S)
    (visitor : stream.StreamingVisitor V) (Queued : U64 → List StreamBatch.Issued → V → Prop)
    (config : stream.Config) (ha : Accepts visitor config Queued profile)
    (state : S) (moduleId : U64) (env : module.Env) (code : Slice U8)
    (environment tail : List U8) (hs : StreamSource.Available source state environment code.val tail)
    (henv : CodeEntry.Bounds env) (hprofile : Profile.Environment profile env)
    (hlimits : Profile.EnvironmentWithinLimits profile env)
    (hcap : code.length ≤ limits.MAX_MODULE_BYTES.val)
    (v : V) (pending : alloc.vec.Vec Usize) (pos func batchId : Usize)
    (hinv : CompleteInvariant (profile := profile) Queued code env moduleId config v pending pos func batchId) :
    stream.submit_code_batches_loop.body source visitor moduleId profile state env.types env.imports
      env.globals env.exports env.elements env.data_count env.declared_funcs env.start
      env.func_type_indices env.func_types
      env.table_types env.mem_types env.global_types env.num_imported_funcs env.num_imported_globals
      (Slice.len code) config (alloc.vec.Vec.len env.func_type_indices) v pending pos func batchId
        ⦃ CompleteBodyPost (profile := profile) Queued code env moduleId config func ⦄ := by
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
        environment tail hs henv hprofile hlimits hcap v' remaining pos func batchId rest entries
        hv' hvalid hids hcount htyped hbytes hbatch (by omega) hfunc (by omega)
      simp [core.result.Result.Insts.CoreOpsTry.branch] at hresume ⊢
      convert hresume using 1
      rfl
    · rw [if_neg hfull]
      exact resume_complete source visitor Queued config ha state moduleId env code
        environment tail hs henv hprofile hlimits hcap v pending pos func batchId queue entries
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

variable {profile : ValidationProfile}

open ModuleBinary StreamAcceptingScheduler

/-- The submission loop accepts independently encoded and typed entries, maintaining the queue of
outstanding work as its function cursor advances. -/
theorem stream.submit_code_batches_loop.complete_spec {S V : Type} (source : stream.Source S)
    (visitor : stream.StreamingVisitor V) (Queued : U64 → List StreamBatch.Issued → V → Prop)
    (config : stream.Config) (ha : Accepts visitor config Queued profile)
    (state : S) (moduleId : U64) (env : module.Env) (code : Slice U8)
    (environment tail : List U8) (hs : StreamSource.Available source state environment code.val tail)
    (henv : CodeEntry.Bounds env) (hprofile : Profile.Environment profile env)
    (hlimits : Profile.EnvironmentWithinLimits profile env)
    (hcap : code.length ≤ limits.MAX_MODULE_BYTES.val)
    (v : V) (pending : alloc.vec.Vec Usize) (pos func batchId : Usize)
    (hinv : StreamSubmission.CompleteInvariant (profile := profile) Queued code env moduleId config v pending pos func batchId) :
    stream.submit_code_batches_loop source visitor moduleId profile state env.types env.imports
      env.globals env.exports env.elements env.data_count env.declared_funcs env.start
      env.func_type_indices env.func_types
      env.table_types env.mem_types env.global_types env.num_imported_funcs env.num_imported_globals
      (Slice.len code) config v pending pos func batchId (alloc.vec.Vec.len env.func_type_indices)
        ⦃ StreamSubmission.CompletePost (profile := profile) Queued moduleId config ⦄ := by
  unfold stream.submit_code_batches_loop
  apply loop.spec_decr_nat (fun s => env.func_type_indices.val.length - s.2.2.2.1.val)
    (fun s => StreamSubmission.CompleteInvariant (profile := profile) Queued code env moduleId config
      s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2)
  · rintro ⟨v', pending', pos', func', batchId'⟩ h
    apply WP.spec_mono (StreamSubmission.body_complete source visitor Queued config ha state moduleId env
      code environment tail hs henv hprofile hlimits hcap v' pending' pos' func' batchId' h)
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
    (config : stream.Config) (ha : Accepts visitor config Queued profile)
    (state : S) (moduleId : U64) (env : module.Env) (code : Slice U8) (start : Usize)
    (environment tail : List U8) (hs : StreamSource.Available source state environment code.val tail)
    (henv : CodeEntry.Bounds env) (hprofile : Profile.Environment profile env)
    (hlimits : Profile.EnvironmentWithinLimits profile env)
    (hcap : code.length ≤ limits.MAX_MODULE_BYTES.val)
    (entries : List Code) (hcount : entries.length = env.func_type_indices.val.length)
    (htyped : ModuleCode.EntriesTyped (profile := profile) env 0 entries)
    (hbytes : At (Rep (Profile.CodeEncodingWithinLimits profile)) code start entries (Slice.len code))
    (v : V) (hv : Queued moduleId [] v) :
    ∃ pending v' queue,
      stream.submit_code_batches source visitor moduleId profile state env (Slice.len code) start config v =
        .ok (.Ok pending, v') ∧ Queued moduleId queue v' ∧ ValidQueue moduleId queue profile ∧
      pending.val.Perm (queue.map StreamBatch.Issued.batch_id) ∧
      pending.length ≤ config.max_batches.val := by
  have hi : StreamSubmission.CompleteInvariant (profile := profile) Queued code env moduleId config v
      (alloc.vec.Vec.new _) start 0#usize 0#usize := by
    refine ⟨by simp, by simp [alloc.vec.Vec.new], by simp [alloc.vec.Vec.new],
      [], entries, hv, ?_, ?_, by simpa using hcount, htyped, hbytes⟩
    · simp [ValidQueue]
    · simp [alloc.vec.Vec.new]
  obtain ⟨⟨r, v'⟩, hr, hp⟩ := WP.spec_imp_exists
    (stream.submit_code_batches_loop.complete_spec source visitor Queued config ha state moduleId env code
      environment tail hs henv hprofile hlimits hcap v (alloc.vec.Vec.new _) start 0#usize 0#usize hi)
  cases r with
  | Err e => exact False.elim hp
  | Ok pending =>
    obtain ⟨queue, hv', hvalid, hids, hmax⟩ := hp
    exact ⟨pending, v', queue, hr, hv', hvalid, hids, hmax⟩

end Itasca
