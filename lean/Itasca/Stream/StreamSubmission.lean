import Itasca.Support.Result
import Itasca.Stream.StreamPartition
import Itasca.Stream.StreamDrain
import Itasca.Stream.StreamBatchSound

open Aeneas Aeneas.Std

namespace Itasca.StreamSubmission

variable {profile : ValidationProfile}

open StreamScheduler

/-- Successful submission prefixes retain exact issuance order, the bounded
pending-ID set, and certificates only for work already successfully retired. -/
structure SoundInvariant (code : Slice U8) (env : module.Env) (start : Usize)
    (id : U64) (capacity : Usize) (history : List StreamBatch.Issued)
    (pending : alloc.vec.Vec Usize) (pos func nextId : Usize)
    (profile : ValidationProfile := .Wasm1) : Prop where
  partition : Partition code env start 0 history pos func.val
  position : pos.val ≤ code.length
  functions : func.val ≤ env.func_type_indices.val.length
  next_id : nextId.val = history.length
  numbered : history.map (fun issued => issued.batch_id.val) = List.range history.length
  issued : ∀ issued ∈ history, issued.module_id = id ∧ issued.env = env ∧ issued.Bounded
  pending_history : ∀ batchId ∈ pending.val, ∃ issued ∈ history, issued.batch_id = batchId
  pending_distinct : pending.val.Nodup
  pending_bound : pending.length ≤ capacity.val
  accounted : ∀ issued ∈ history, issued.batch_id ∈ pending.val ∨ Completed issued profile
  profiles : ∀ issued ∈ history, issued.profile = profile

theorem SoundInvariant.fresh {code env start id capacity history pending pos func nextId}
    (h : SoundInvariant (profile := profile) code env start id capacity history pending pos func nextId) :
    ∀ issued ∈ history, issued.batch_id ≠ nextId := by
  intro issued hm he
  have hb : issued.batch_id.val ∈ List.range history.length := by
    rw [← h.numbered]
    exact List.mem_map.mpr ⟨issued, hm, rfl⟩
  have hn := List.mem_range.mp hb
  rw [he, h.next_id] at hn
  omega

theorem SoundInvariant.pending_fresh {code env start id capacity history pending pos func nextId}
    (h : SoundInvariant (profile := profile) code env start id capacity history pending pos func nextId) :
    nextId ∉ pending.val := by
  intro hm
  obtain ⟨issued, hi, he⟩ := h.pending_history nextId hm
  exact h.fresh issued hi he

theorem SoundInvariant.initial {profile : ValidationProfile} (code : Slice U8) (env : module.Env) (start : Usize)
    (id : U64) (capacity : Usize) (hstart : start.val ≤ code.length) :
    SoundInvariant (profile := profile) code env start id capacity [] (alloc.vec.Vec.new _) start 0#usize 0#usize := by
  constructor
  · exact .nil start 0 hstart
  · exact hstart
  · simp
  · simp
  · simp
  · simp
  · simp [alloc.vec.Vec.new]
  · simp [alloc.vec.Vec.new]
  · simp [alloc.vec.Vec.new]
  · simp
  · simp

/-- Removing one pending identity creates a certificate only after successful
retirement; all other outstanding and completed work remains accounted for. -/
theorem SoundInvariant.retire {code env start id capacity history pending pos func nextId}
    (h : SoundInvariant (profile := profile) code env start id capacity history pending pos func nextId)
    (remaining : alloc.vec.Vec Usize) (batchId : Usize)
    (hperm : (batchId :: remaining.val).Perm pending.val)
    (hcomplete : ∀ issued ∈ history, issued.module_id = id → issued.batch_id = batchId → Completed issued profile) :
    SoundInvariant (profile := profile) code env start id capacity history remaining pos func nextId := by
  have hnodup := hperm.nodup_iff.mpr h.pending_distinct
  rw [List.nodup_cons] at hnodup
  have hlen := hperm.length_eq
  simp only [List.length_cons] at hlen
  refine ⟨h.partition, h.position, h.functions, h.next_id, h.numbered, h.issued,
    ?_, hnodup.2, ?_, ?_, h.profiles⟩
  · intro needle hm
    exact h.pending_history needle (hperm.mem_iff.mp (by simp [hm]))
  · change remaining.val.length ≤ _
    have hb := h.pending_bound
    change pending.val.length ≤ _ at hb
    omega
  · intro issued hi
    rcases h.accounted issued hi with hp | hc
    · have hm := hperm.mem_iff.mpr hp
      rcases List.mem_cons.mp hm with he | hr
      · exact .inr (hcomplete issued hi (h.issued issued hi).1 he)
      · exact .inl hr
    · exact .inr hc

/-- Adding the actual seed extends both independent byte/function tiling and
the exact numbered issuance history. The new ID is outstanding, not completed. -/
theorem SoundInvariant.issue {code env start id capacity history pending pos func nextId}
    (h : SoundInvariant (profile := profile) code env start id capacity history pending pos func nextId)
    (issued : StreamBatch.Issued) (nextPending : alloc.vec.Vec Usize)
    (finish nextFunc nextBatchId : Usize)
    (hmodule : issued.module_id = id) (henv : issued.env = env)
    (hbatch : issued.batch_id = nextId) (hbounded : issued.Bounded)
    (hoffset : issued.code_offset = pos) (hfirst : issued.first_func = func)
    (hbytes : Wasm.BytesAt code pos issued.code.val finish)
    (hcount : nextFunc.val = func.val + issued.num_funcs.val)
    (hfunctions : nextFunc.val ≤ env.func_type_indices.val.length)
    (hnext : nextBatchId.val = nextId.val + 1)
    (hpending : nextPending.val = pending.val ++ [nextId])
    (hroom : pending.length < capacity.val) (hprofile : issued.profile = profile) :
    SoundInvariant (profile := profile) code env start id capacity (history ++ [issued]) nextPending finish nextFunc nextBatchId := by
  refine ⟨?_, hbytes.bound, hfunctions, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcount]
    exact h.partition.snoc henv hoffset (by rw [hfirst]) hbytes
  · simp only [List.length_append, List.length_singleton]
    rw [hnext, h.next_id]
  · simp only [List.map_append, List.map_cons, List.map_nil, List.length_append, List.length_singleton,
      h.numbered, List.range_succ]
    congr 1
    simp [hbatch, h.next_id]
  · intro old hm
    rcases List.mem_append.mp hm with hm | hm
    · exact h.issued old hm
    · have he : old = issued := by simpa using hm
      exact he ▸ ⟨hmodule, henv, hbounded⟩
  · intro needle hm
    rw [hpending] at hm
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨old, ho, he⟩ := h.pending_history needle hm
      exact ⟨old, List.mem_append_left _ ho, he⟩
    · have he : needle = nextId := by simpa using hm
      exact ⟨issued, by simp, by simpa [he] using hbatch⟩
  · rw [hpending, List.nodup_append]
    refine ⟨h.pending_distinct, by simp, ?_⟩
    intro a ha b hb
    have he : b = nextId := by simpa using hb
    subst b
    intro he
    exact h.pending_fresh (he ▸ ha)
  · change nextPending.val.length ≤ _
    rw [hpending, List.length_append, List.length_singleton]
    change pending.val.length < _ at hroom
    omega
  · intro old hm
    rcases List.mem_append.mp hm with hm | hm
    · rcases h.accounted old hm with hp | hc
      · exact .inl (by rw [hpending]; simp [hp])
      · exact .inr hc
    · have he : old = issued := by simpa using hm
      subst old
      exact .inl (by rw [hbatch, hpending]; simp)
  · intro old hm
    rcases List.mem_append.mp hm with hm | hm
    · exact h.profiles old hm
    · have he : old = issued := by simpa using hm
      exact he ▸ hprofile

/-- Successful submission tiles the entire entry region and accounts for every
issued identity by outstanding work or a derived retirement certificate. -/
def SoundPost {V : Type} (Tracks : U64 → List StreamBatch.Issued → V → Prop)
    (code : Slice U8) (env : module.Env) (start : Usize) (id : U64) (capacity : Usize)
    (profile : ValidationProfile := .Wasm1) :
    (core.result.Result (alloc.vec.Vec Usize) error.Error × V) → Prop
  | (.Ok pending, v) => ∃ history nextId,
      SoundInvariant (profile := profile) code env start id capacity history pending (Slice.len code)
        (alloc.vec.Vec.len env.func_type_indices) nextId ∧ Tracks id history v
  | (.Err _, _) => True

private def BodyPost {V : Type} (Tracks : U64 → List StreamBatch.Issued → V → Prop)
    (code : Slice U8) (env : module.Env) (start : Usize) (id : U64)
    (capacity func : Usize)
    (profile : ValidationProfile := .Wasm1) :
    ControlFlow (V × alloc.vec.Vec Usize × Usize × Usize × Usize)
      (core.result.Result (alloc.vec.Vec Usize) error.Error × V) → Prop
  | .done result => SoundPost (profile := profile) Tracks code env start id capacity result
  | .cont (v, pending, pos, next, batchId) => ∃ history,
      SoundInvariant (profile := profile) code env start id capacity history pending pos next batchId ∧
      Tracks id history v ∧ func.val < next.val

end Itasca.StreamSubmission


namespace Itasca.StreamSubmission

variable {profile : ValidationProfile}

private theorem resume_sound {S V : Type} (source : stream.Source S) (visitor : stream.StreamingVisitor V)
    (Tracks : U64 → List StreamBatch.Issued → V → Prop)
    (hp : StreamScheduler.Provenance visitor Tracks profile)
    (state : S) (moduleId : U64) (env : module.Env) (code : Slice U8) (start : Usize)
    (config : stream.Config) (v : V) (pending : alloc.vec.Vec Usize)
    (pos func batchId : Usize) (history : List StreamBatch.Issued)
    (environment tail : List U8) (hsource : StreamSource.Coherent source state environment code.val tail)
    (henv : CodeEntry.Bounds env) (hcap : code.length ≤ limits.MAX_MODULE_BYTES.val)
    (hinv : SoundInvariant (profile := profile) code env start moduleId config.max_batches history pending pos func batchId)
    (hv : Tracks moduleId history v) (hfunc : func.val < env.func_type_indices.val.length)
    (hroom : pending.length < config.max_batches.val)
    (out : ControlFlow (V × alloc.vec.Vec Usize × Usize × Usize × Usize)
      (core.result.Result (alloc.vec.Vec Usize) error.Error × V))
    (h : (do
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
        Result.ok (ControlFlow.done (r1, v))) = .ok out) :
    BodyPost (profile := profile) Tracks code env start moduleId config.max_batches func out := by
  obtain ⟨r, hframe, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
  cases r with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
    subst out
    trivial
  | Ok pair =>
    obtain ⟨finish, next⟩ := pair
    obtain ⟨hprogress, hfinish, hnext, hnextbound⟩ := stream.get_next_batch.sound source state
      (Slice.len code) pos func (alloc.vec.Vec.len env.func_type_indices) config.batch_bytes finish next
      (by simpa using hcap) (by simpa using hinv.position) (by simpa using hfunc) hframe
    simp [core.result.Result.Insts.CoreOpsTry.branch] at h
    obtain ⟨r, hread, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
    cases r with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
      subst out
      trivial
    | Ok bytes =>
      have hview := stream.read_exact.sound source state environment code.val tail hsource
        pos finish bytes (by omega) (by simpa using hfinish) hread
      have hspan := Wasm.BytesAt.of_slice_view (by omega : pos.val ≤ finish.val)
        (by simpa using hfinish : finish.val ≤ code.length) hview.1
      simp at h
      obtain ⟨nextPending, hpush, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
      have hpushspec := alloc.vec.Vec.push_spec pending batchId (by scalar_tac)
      rw [hpush] at hpushspec
      simp only [WP.spec_ok] at hpushspec
      obtain ⟨count, hsub, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
      have hsubspec := UScalar.sub_equiv next func
      rw [hsub] at hsubspec
      let issued : StreamBatch.Issued := ⟨moduleId, batchId, env, bytes, pos, func, count, profile⟩
      have hissued : issued.Bounded := by
        dsimp [issued, StreamBatch.Issued.Bounded]
        have hlength := hspan.length
        change finish.val = pos.val + bytes.length at hlength
        have hbound := hspan.bound
        have hcountval := hsubspec.2.1
        have hnextbound' : next.val ≤ env.func_type_indices.val.length := by simpa using hnextbound
        simp only [Slice.length] at hlength hbound hcap ⊢
        omega
      obtain ⟨⟨reply, v'⟩, hsubmit, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
      cases reply with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
        subst out
        trivial
      | Ok u =>
        cases u
        have hsubmit' : visitor.submit_code_batch v issued.seed = .ok (.Ok (), v') := hsubmit
        have hv' := hp.submit moduleId history issued v v' hv rfl hissued henv rfl
          (by simpa [issued] using hinv.fresh) hsubmit'
        simp at h
        obtain ⟨nextId, hinc, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
        have hincspec := UScalar.add_equiv batchId 1#usize
        rw [hinc] at hincspec
        simp only [Result.ok.injEq] at h
        subst out
        refine ⟨history ++ [issued], ?_, hv', by simpa using hnext⟩
        exact hinv.issue issued nextPending finish next nextId rfl rfl rfl hissued rfl rfl hspan
          (by dsimp [issued]; have := hsubspec.1; have := hsubspec.2.1; omega)
          (by simpa using hnextbound) (by simpa using hincspec.2.1) hpushspec hroom rfl

end Itasca.StreamSubmission

namespace Itasca.StreamSubmission

variable {profile : ValidationProfile}

private theorem body_sound {S V : Type} (source : stream.Source S) (visitor : stream.StreamingVisitor V)
    (Tracks : U64 → List StreamBatch.Issued → V → Prop)
    (hp : StreamScheduler.Provenance visitor Tracks profile)
    (state : S) (moduleId : U64) (env : module.Env) (code : Slice U8) (start : Usize)
    (config : stream.Config) (v : V) (pending : alloc.vec.Vec Usize)
    (pos func batchId : Usize) (history : List StreamBatch.Issued)
    (environment tail : List U8) (hsource : StreamSource.Coherent source state environment code.val tail)
    (henv : CodeEntry.Bounds env)
    (hresults : ∀ ft ∈ env.types.val, Profile.FuncType profile ft)
    (hcap : code.length ≤ limits.MAX_MODULE_BYTES.val)
    (hinv : SoundInvariant (profile := profile) code env start moduleId config.max_batches history pending pos func batchId)
    (hv : Tracks moduleId history v)
    (out : ControlFlow (V × alloc.vec.Vec Usize × Usize × Usize × Usize)
      (core.result.Result (alloc.vec.Vec Usize) error.Error × V))
    (h : stream.submit_code_batches_loop.body source visitor moduleId profile state env.types env.imports
      env.globals env.exports env.elements env.start env.func_type_indices env.func_types
      env.table_types env.mem_types env.global_types env.num_imported_funcs env.num_imported_globals
      (Slice.len code) config (alloc.vec.Vec.len env.func_type_indices) v pending pos func batchId = .ok out) :
    BodyPost (profile := profile) Tracks code env start moduleId config.max_batches func out := by
  unfold stream.submit_code_batches_loop.body at h
  by_cases hmore : func < alloc.vec.Vec.len env.func_type_indices
  · rw [if_pos hmore] at h
    by_cases hfull : alloc.vec.Vec.len pending ≥ config.max_batches
    · rw [if_pos hfull] at h
      obtain ⟨⟨r, v', remaining⟩, hretire, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
      cases r with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
        subst out
        trivial
      | Ok u =>
        cases u
        have hentry : ∀ issued ∈ history, CodeEntry.Bounds issued.env ∧
            ∀ ft ∈ issued.env.types.val, Profile.FuncType profile ft := by
          intro issued hm
          have he := (hinv.issued issued hm).2.1
          simpa [he] using And.intro henv hresults
        obtain ⟨hv', retiredId, hperm, hcomplete⟩ := StreamScheduler.retire_sound
          visitor Tracks hp moduleId history v v' pending remaining hv hentry hinv.profiles hretire
        have hinv' := hinv.retire remaining retiredId hperm hcomplete
        have hlen : remaining.length + 1 = pending.length := by
          simpa [alloc.vec.Vec.length] using hperm.length_eq
        have hroom : remaining.length < config.max_batches.val := by
          have hb := hinv.pending_bound
          omega
        simp [core.result.Result.Insts.CoreOpsTry.branch] at h
        exact resume_sound source visitor Tracks hp state moduleId env code start config v' remaining
          pos func batchId history environment tail hsource henv hcap hinv' hv'
          (by scalar_tac) hroom out h
    · rw [if_neg hfull] at h
      exact resume_sound source visitor Tracks hp state moduleId env code start config v pending
        pos func batchId history environment tail hsource henv hcap hinv hv
        (by scalar_tac) (by scalar_tac) out h
  · rw [if_neg hmore] at h
    split at h
    · simp only [Result.ok.injEq] at h
      subst out
      trivial
    · rename_i hpos
      simp only [Result.ok.injEq] at h
      subst out
      have hfunc : func = alloc.vec.Vec.len env.func_type_indices := by
        apply UScalar.eq_of_val_eq
        have hb := hinv.functions
        scalar_tac
      have hpos : pos = Slice.len code := by apply UScalar.eq_of_val_eq; simpa using hpos
      subst func
      subst pos
      exact ⟨history, batchId, hinv, hv⟩

end Itasca.StreamSubmission

namespace Itasca

variable {profile : ValidationProfile}

/-- Follow the actual accepting submission run. Each successful iteration
extends history with its exact seed, optionally certifying one retired batch. -/
theorem stream.submit_code_batches_loop.sound {S V : Type}
    (source : stream.Source S) (visitor : stream.StreamingVisitor V)
    (Tracks : U64 → List StreamBatch.Issued → V → Prop)
    (hp : StreamScheduler.Provenance visitor Tracks profile)
    (state : S) (moduleId : U64) (env : module.Env) (code : Slice U8) (start : Usize)
    (config : stream.Config) (v : V) (pending : alloc.vec.Vec Usize)
    (pos func batchId : Usize) (history : List StreamBatch.Issued)
    (environment tail : List U8) (hsource : StreamSource.Coherent source state environment code.val tail)
    (henv : CodeEntry.Bounds env)
    (hresults : ∀ ft ∈ env.types.val, Profile.FuncType profile ft)
    (hcap : code.length ≤ limits.MAX_MODULE_BYTES.val)
    (hinv : StreamSubmission.SoundInvariant (profile := profile) code env start moduleId config.max_batches history pending pos func batchId)
    (hv : Tracks moduleId history v)
    (finalPending : alloc.vec.Vec Usize) (finalV : V)
    (h : stream.submit_code_batches_loop source visitor moduleId profile state env.types env.imports
      env.globals env.exports env.elements env.start env.func_type_indices env.func_types
      env.table_types env.mem_types env.global_types env.num_imported_funcs env.num_imported_globals
      (Slice.len code) config v pending pos func batchId (alloc.vec.Vec.len env.func_type_indices) =
        .ok (.Ok finalPending, finalV)) :
    StreamSubmission.SoundPost (profile := profile) Tracks code env start moduleId config.max_batches (.Ok finalPending, finalV) := by
  generalize hn : env.func_type_indices.val.length - func.val = n
  induction n using Nat.strong_induction_on generalizing v pending pos func batchId history with
  | h n ih =>
    unfold stream.submit_code_batches_loop at h
    rw [loop] at h
    obtain ⟨out, hbody, hrest⟩ := ResultFacts.bind_ok_inv _ _ _ h
    have hs := StreamSubmission.body_sound source visitor Tracks hp state moduleId env code start
      config v pending pos func batchId history environment tail hsource henv hresults hcap hinv hv out hbody
    cases out with
    | done result =>
      have he : result = (.Ok finalPending, finalV) := by simpa using hrest
      subst result
      exact hs
    | cont next =>
      obtain ⟨v', pending', pos', func', batchId'⟩ := next
      obtain ⟨history', hinv', hv', hprogress⟩ := hs
      have hlt : env.func_type_indices.val.length - func'.val < n := by
        have hb := hinv'.functions
        omega
      have hrecursive : stream.submit_code_batches_loop source visitor moduleId profile state env.types env.imports
          env.globals env.exports env.elements env.start env.func_type_indices env.func_types
          env.table_types env.mem_types env.global_types env.num_imported_funcs env.num_imported_globals
          (Slice.len code) config v' pending' pos' func' batchId' (alloc.vec.Vec.len env.func_type_indices) =
            .ok (.Ok finalPending, finalV) := hrest
      exact ih _ hlt v' pending' pos' func' batchId' history' hinv' hv' hrecursive rfl

/-- Accepted submission supplies a complete ordered byte/function partition,
exact issued identities, bounded distinct pending IDs, and certificates for
already retired work. Source coherence and callback provenance are the only
embedding assumptions; unexecuted callbacks need not return. -/
theorem stream.submit_code_batches.sound {S V : Type}
    (source : stream.Source S) (visitor : stream.StreamingVisitor V)
    (Tracks : U64 → List StreamBatch.Issued → V → Prop)
    (hp : StreamScheduler.Provenance visitor Tracks profile)
    (state : S) (moduleId : U64) (env : module.Env) (code : Slice U8) (start : Usize)
    (config : stream.Config) (v : V) (pending : alloc.vec.Vec Usize) (v' : V)
    (environment tail : List U8) (hsource : StreamSource.Coherent source state environment code.val tail)
    (henv : CodeEntry.Bounds env)
    (hresults : ∀ ft ∈ env.types.val, Profile.FuncType profile ft)
    (hcap : code.length ≤ limits.MAX_MODULE_BYTES.val) (hstart : start.val ≤ code.length)
    (hv : Tracks moduleId [] v)
    (h : stream.submit_code_batches source visitor moduleId profile state env (Slice.len code) start config v =
      .ok (.Ok pending, v')) :
    StreamSubmission.SoundPost (profile := profile) Tracks code env start moduleId config.max_batches (.Ok pending, v') := by
  exact stream.submit_code_batches_loop.sound source visitor Tracks hp state moduleId env code start
    config v (alloc.vec.Vec.new _) start 0#usize 0#usize [] environment tail hsource henv hresults hcap
    (StreamSubmission.SoundInvariant.initial code env start moduleId config.max_batches hstart) hv pending v' h

end Itasca
