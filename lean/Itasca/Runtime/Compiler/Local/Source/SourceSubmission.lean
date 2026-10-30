import Itasca.Stream.SubmissionSound
import Itasca.Stream.FramingComplete

/-!
Issued compiler batch submission and retirement, connected to source progress. Submit, Retire and their loop transport establish the source submission invariant.
-/

/-! ## Submission Transfer -/

section

namespace Itasca.Runtime.Compiler.SubmissionTransfer
open Aeneas Aeneas.Std Itasca

/-- Local accepted submission preserves a source-position-indexed invariant.
The obligation includes the exact framing and byte-read calls, so a decoded
source split can be retained without assuming a callback certificate. -/
def Submit {S V : Type} (source : stream.Source S) (visitor : stream.StreamingVisitor V)
    (state : S) (moduleId : U64) (env : metadata.Env) (code : Slice U8)
    (profile : ValidationProfile) (config : stream.Config) (P : Usize → Usize → V → Prop) : Prop :=
  ∀ (v v' : V) (pos func batchId finish next count : Usize) (bytes : Slice U8),
    P pos func v → pos.val ≤ code.length → func.val < env.func_type_indices.val.length →
    stream.get_next_batch source state (Slice.len code) pos func (alloc.vec.Vec.len env.func_type_indices)
      config.batch_bytes = .ok (.Ok (finish, next)) →
    stream.read_exact source state pos finish = .ok (.Ok bytes) →
    count.val = next.val - func.val →
    visitor.submit_code_batch v
      { module_id := moduleId, batch_id := batchId, profile, env, code := bytes,
        code_offset := pos, first_func := func, num_funcs := count,
        num_dispatched := 0#usize, dispatch_end := 0#usize,
        num_validated := 0#usize, validated_end := 0#usize, error := none } = .ok (.Ok (), v') →
    P finish next v'

def Retire {V : Type} (visitor : stream.StreamingVisitor V) (moduleId : U64)
    (P : Usize → Usize → V → Prop) : Prop :=
  ∀ (v v' : V) (pos func : Usize) (pending remaining : alloc.vec.Vec Usize),
    P pos func v → stream.retire_code_batch visitor moduleId v pending = .ok (.Ok (), v', remaining) →
    P pos func v'

private def ResultPost {V : Type} (P : Usize → Usize → V → Prop)
    (code : Slice U8) (env : metadata.Env) :
    (core.result.Result (alloc.vec.Vec Usize) error.Error × V) → Prop
  | (.Ok _, v) => P (Slice.len code) (alloc.vec.Vec.len env.func_type_indices) v
  | (.Err _, _) => True

private def BodyPost {V : Type} (P : Usize → Usize → V → Prop)
    (code : Slice U8) (env : metadata.Env) (func : Usize) :
    ControlFlow (V × alloc.vec.Vec Usize × Usize × Usize × Usize)
      (core.result.Result (alloc.vec.Vec Usize) error.Error × V) → Prop
  | .done result => ResultPost P code env result
  | .cont (v, _, pos, next, _) =>
      pos.val ≤ code.length ∧ next.val ≤ env.func_type_indices.val.length ∧
      P pos next v ∧ func.val < next.val

private theorem resume {S V : Type} (source : stream.Source S) (visitor : stream.StreamingVisitor V)
    (state : S) (moduleId : U64) (env : metadata.Env) (code : Slice U8)
    (profile : ValidationProfile) (config : stream.Config) (P : Usize → Usize → V → Prop)
    (submitted : Submit source visitor state moduleId env code profile config P)
    (v : V) (pending : alloc.vec.Vec Usize) (pos func batchId : Usize)
    (hcap : code.length ≤ limits.MAX_MODULE_BYTES.val)
    (hpos : pos.val ≤ code.length) (hv : P pos func v)
    (hfunc : func.val < env.func_type_indices.val.length)
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
    BodyPost P code env func out := by
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
      (by simpa using hcap) (by simpa using hpos) (by simpa using hfunc) hframe
    simp [core.result.Result.Insts.CoreOpsTry.branch] at h
    obtain ⟨r, hread, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
    cases r with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
      subst out
      trivial
    | Ok bytes =>
      simp at h
      obtain ⟨nextPending, hpush, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
      obtain ⟨count, hsub, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
      have hsubspec := UScalar.sub_equiv next func
      rw [hsub] at hsubspec
      obtain ⟨⟨reply, v'⟩, hsubmit, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
      cases reply with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
        subst out
        trivial
      | Ok u =>
        cases u
        have hv' := submitted v v' pos func batchId finish next count bytes hv hpos hfunc hframe hread
          (by have := hsubspec.2.1; omega) hsubmit
        simp at h
        obtain ⟨nextId, hinc, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
        have hincspec := UScalar.add_equiv batchId 1#usize
        rw [hinc] at hincspec
        simp only [Result.ok.injEq] at h
        subst out
        exact ⟨by simpa using hfinish, by simpa using hnextbound, hv', by simpa using hnext⟩

private theorem body {S V : Type} (source : stream.Source S) (visitor : stream.StreamingVisitor V)
    (state : S) (moduleId : U64) (env : metadata.Env) (code : Slice U8)
    (profile : ValidationProfile) (config : stream.Config) (P : Usize → Usize → V → Prop)
    (submitted : Submit source visitor state moduleId env code profile config P)
    (retired : Retire visitor moduleId P)
    (v : V) (pending : alloc.vec.Vec Usize) (pos func batchId : Usize)
    (hcap : code.length ≤ limits.MAX_MODULE_BYTES.val)
    (hpos : pos.val ≤ code.length) (hfunc : func.val ≤ env.func_type_indices.val.length)
    (hv : P pos func v)
    (out : ControlFlow (V × alloc.vec.Vec Usize × Usize × Usize × Usize)
      (core.result.Result (alloc.vec.Vec Usize) error.Error × V))
    (h : stream.submit_code_batches_loop.body source visitor moduleId profile state env.types env.imports
      env.globals env.exports env.elements env.data_count env.declared_funcs env.start
      env.func_type_indices env.func_types
      env.table_types env.mem_types env.global_types env.num_imported_funcs env.num_imported_globals
      (Slice.len code) config (alloc.vec.Vec.len env.func_type_indices) v pending pos func batchId = .ok out) :
    BodyPost P code env func out := by
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
        have hv' := retired v v' pos func pending remaining hv hretire
        simp [core.result.Result.Insts.CoreOpsTry.branch] at h
        exact resume source visitor state moduleId env code profile config P submitted v' remaining
          pos func batchId hcap hpos hv' (by scalar_tac) out h
    · rw [if_neg hfull] at h
      exact resume source visitor state moduleId env code profile config P submitted v pending
        pos func batchId hcap hpos hv (by scalar_tac) out h
  · rw [if_neg hmore] at h
    split at h
    · simp only [Result.ok.injEq] at h
      subst out
      trivial
    · rename_i samePos
      simp only [Result.ok.injEq] at h
      subst out
      have sameFunc : func = alloc.vec.Vec.len env.func_type_indices := by
        apply UScalar.eq_of_val_eq
        scalar_tac
      have position : pos = Slice.len code := by apply UScalar.eq_of_val_eq; simpa using samePos
      subst func
      subst pos
      exact hv

/-- Accepted execution of the actual submission loop transports a retained
source/compiler invariant through framing, submissions and retirements. -/
theorem loop {S V : Type} (source : stream.Source S) (visitor : stream.StreamingVisitor V)
    (state : S) (moduleId : U64) (env : metadata.Env) (code : Slice U8)
    (profile : ValidationProfile) (config : stream.Config) (P : Usize → Usize → V → Prop)
    (submitted : Submit source visitor state moduleId env code profile config P)
    (retired : Retire visitor moduleId P)
    (v : V) (pending : alloc.vec.Vec Usize) (pos func batchId : Usize)
    (hcap : code.length ≤ limits.MAX_MODULE_BYTES.val)
    (hpos : pos.val ≤ code.length) (hfunc : func.val ≤ env.func_type_indices.val.length)
    (hv : P pos func v)
    (finalPending : alloc.vec.Vec Usize) (finalV : V)
    (h : stream.submit_code_batches_loop source visitor moduleId profile state env.types env.imports
      env.globals env.exports env.elements env.data_count env.declared_funcs env.start
      env.func_type_indices env.func_types
      env.table_types env.mem_types env.global_types env.num_imported_funcs env.num_imported_globals
      (Slice.len code) config v pending pos func batchId (alloc.vec.Vec.len env.func_type_indices) =
        .ok (.Ok finalPending, finalV)) : P (Slice.len code) (alloc.vec.Vec.len env.func_type_indices) finalV := by
  generalize hn : env.func_type_indices.val.length - func.val = n
  induction n using Nat.strong_induction_on generalizing v pending pos func batchId with
  | h n ih =>
    unfold stream.submit_code_batches_loop at h
    rw [Aeneas.Std.loop] at h
    obtain ⟨out, hbody, hrest⟩ := ResultFacts.bind_ok_inv _ _ _ h
    have hs := body source visitor state moduleId env code profile config P submitted retired
      v pending pos func batchId hcap hpos hfunc hv out hbody
    cases out with
    | done result =>
      have same : result = (.Ok finalPending, finalV) := by simpa using hrest
      subst result
      exact hs
    | cont next =>
      obtain ⟨v', pending', pos', func', batchId'⟩ := next
      obtain ⟨hpos', hfunc', hv', hprogress⟩ := hs
      have smaller : env.func_type_indices.val.length - func'.val < n := by omega
      have recursive : stream.submit_code_batches_loop source visitor moduleId profile state env.types env.imports
          env.globals env.exports env.elements env.data_count env.declared_funcs env.start
          env.func_type_indices env.func_types
          env.table_types env.mem_types env.global_types env.num_imported_funcs env.num_imported_globals
          (Slice.len code) config v' pending' pos' func' batchId' (alloc.vec.Vec.len env.func_type_indices) =
            .ok (.Ok finalPending, finalV) := hrest
      exact ih _ smaller v' pending' pos' func' batchId' hpos' hfunc' hv' recursive rfl

/-- The public submission phase starts from the decoded code-header cursor
and source function zero. No callback correctness premise survives once the
local source-split and compiler-entry lemmas instantiate this transport. -/
theorem submit {S V : Type} (source : stream.Source S) (visitor : stream.StreamingVisitor V)
    (state : S) (moduleId : U64) (env : metadata.Env) (code : Slice U8)
    (profile : ValidationProfile) (config : stream.Config) (P : Usize → Usize → V → Prop)
    (submitted : Submit source visitor state moduleId env code profile config P)
    (retired : Retire visitor moduleId P)
    (v finalV : V) (start : Usize) (pending : alloc.vec.Vec Usize)
    (hcap : code.length ≤ limits.MAX_MODULE_BYTES.val) (hstart : start.val ≤ code.length)
    (initial : P start 0#usize v)
    (accepted : stream.submit_code_batches source visitor moduleId profile state env (Slice.len code) start config v =
      .ok (.Ok pending, finalV)) :
    P (Slice.len code) (alloc.vec.Vec.len env.func_type_indices) finalV :=
  loop source visitor state moduleId env code profile config P submitted retired
    v (alloc.vec.Vec.new _) start 0#usize 0#usize hcap hstart (by simp) initial pending finalV accepted

/-- Retirement does not add a mutation beyond the accepted poll callback. -/
theorem retire_of_poll {V : Type} (visitor : stream.StreamingVisitor V) (moduleId : U64)
    (P : Usize → Usize → V → Prop)
    (polled : ∀ v v' batch pos func, P pos func v →
      visitor.poll_code_batch v = .ok (.Ok batch, v') → P pos func v') :
    Retire visitor moduleId P := by
  intro v v' pos func pending remaining invariant accepted
  obtain ⟨batch, poll, _⟩ := stream.retire_code_batch.accepted visitor moduleId v v' pending remaining accepted
  exact polled v v' batch pos func invariant poll
end Itasca.Runtime.Compiler.SubmissionTransfer

end

/-! ## Source Submission -/

section

namespace Itasca.Runtime.Compiler.SourceSubmission
open Aeneas Aeneas.Std Itasca ModuleBinary

/-- The unconsumed source suffix is encoded at the actual next framing cursor.
The processed prefix fixes the global source-function index independently of
any compiler certificate. -/
def Progress {V : Type} (profile : ValidationProfile) (code : Slice U8)
    (env : metadata.Env) (entries : List ModuleBinary.Code) (Q : V → Prop)
    (position first : Usize) (visitor : V) : Prop :=
  ∃ processed remaining, entries = processed ++ remaining ∧
    processed.length = first.val ∧ first.val + remaining.length = env.func_type_indices.val.length ∧
    At (Rep (Profile.CodeEncoding profile)) code position remaining (Slice.len code) ∧ Q visitor

/-- A local batch proof receives its exact decoded source slice and issued
function offset. This contract is instantiated by the concrete entry fold. -/
def Batch {V : Type} (visitor : stream.StreamingVisitor V) (moduleId : U64)
    (profile : ValidationProfile) (env : metadata.Env) (entries : List ModuleBinary.Code) (Q : V → Prop) : Prop :=
  ∀ (before after : V) (issued : StreamBatch.Issued) (processed taken remaining : List ModuleBinary.Code),
    entries = processed ++ taken ++ remaining → issued.module_id = moduleId → issued.profile = profile →
    issued.env = env → issued.first_func.val = processed.length → issued.num_funcs.val = taken.length →
    Rep (Profile.CodeEncoding profile) taken issued.code.val → issued.Bounded → Q before →
    visitor.submit_code_batch before issued.seed = .ok (.Ok (), after) → Q after

theorem progress_submit {S V : Type} (source : stream.Source S) (visitor : stream.StreamingVisitor V)
    (state : S) (moduleId : U64) (env : metadata.Env) (code : Slice U8)
    (profile : ValidationProfile) (config : stream.Config) (entries : List ModuleBinary.Code) (Q : V → Prop)
    (environment tail : List U8) (available : StreamSource.Available source state environment code.val tail)
    (capacity : code.length ≤ limits.MAX_MODULE_BYTES.val)
    (batch : Batch visitor moduleId profile env entries Q) :
    SubmissionTransfer.Submit source visitor state moduleId env code profile config (Progress profile code env entries Q) := by
  intro before after pos first batchId finish next count bytes progress position more framed read counted submitted
  obtain ⟨processed, remaining, split, processedLength, total, suffix, invariant⟩ := progress
  have effect := stream.get_next_batch.complete_spec source state environment tail code available
    (Profile.CodeEncoding profile) (fun _ _ h => h) (Slice.len code) pos first
    (alloc.vec.Vec.len env.func_type_indices) config.batch_bytes remaining rfl capacity more total suffix
  rw [framed, WP.spec_ok] at effect
  obtain ⟨actualFinish, actualNext, taken, rest, same, bounded, remainingEq, nonempty, advanced, restCount, takenAt, restAt⟩ := effect
  obtain ⟨rfl, rfl⟩ := by simpa using same
  obtain ⟨view, viewed, span, encoded⟩ := stream.read_exact.complete_rep source state environment tail code available
    (Profile.CodeEncoding profile) pos finish taken takenAt
  have bytesEq : view = bytes := by simpa [read] using viewed.symm
  subst view
  let issued : StreamBatch.Issued := ⟨moduleId, batchId, env, bytes, pos, first, count, profile⟩
  have countEq : count.val = taken.length := by omega
  have countPositive : 0 < count.val := by
    have h : taken.length ≠ 0 := by simpa using nonempty
    omega
  have issuedBound : issued.Bounded := by
    have length := span.length
    have bound := span.bound
    have nextBound := bounded.2.2.2
    change 0 < count.val ∧ first.val + count.val ≤ env.func_type_indices.val.length ∧
      pos.val + bytes.length ≤ limits.MAX_MODULE_BYTES.val
    refine ⟨countPositive, ?_, ?_⟩
    · have nextBound' : next.val ≤ env.func_type_indices.val.length := by simpa using nextBound
      omega
    · change finish.val = pos.val + bytes.length at length
      omega
  have sourceEq : entries = processed ++ taken ++ rest := by rw [split, remainingEq, List.append_assoc]
  have changed := batch before after issued processed taken rest sourceEq rfl rfl rfl
    processedLength.symm countEq encoded issuedBound invariant submitted
  refine ⟨processed ++ taken, rest, sourceEq, ?_, restCount.symm, restAt, changed⟩
  simp only [List.length_append, processedLength, advanced]

/-- Actual submission preserves a concrete compiler invariant for a fixed
independently encoded source list, provided each real issued batch is checked. -/
theorem submit {S V : Type} (source : stream.Source S) (visitor : stream.StreamingVisitor V)
    (state : S) (moduleId : U64) (env : metadata.Env) (code : Slice U8)
    (profile : ValidationProfile) (config : stream.Config) (entries : List ModuleBinary.Code) (Q : V → Prop)
    (environment tail : List U8) (available : StreamSource.Available source state environment code.val tail)
    (capacity : code.length ≤ limits.MAX_MODULE_BYTES.val)
    (start : Usize) (sourceBytes : At (Rep (Profile.CodeEncoding profile)) code start entries (Slice.len code))
    (count : entries.length = env.func_type_indices.val.length)
    (batch : Batch visitor moduleId profile env entries Q)
    (polled : ∀ before after worker, Q before → visitor.poll_code_batch before = .ok (.Ok worker, after) → Q after)
    (before after : V) (pending : alloc.vec.Vec Usize) (initial : Q before)
    (accepted : stream.submit_code_batches source visitor moduleId profile state env (Slice.len code) start config before =
      .ok (.Ok pending, after)) : Q after := by
  have initialProgress : Progress profile code env entries Q start 0#usize before :=
    ⟨[], entries, by simp, by simp, by simpa using count, sourceBytes, initial⟩
  have retired : SubmissionTransfer.Retire visitor moduleId (Progress profile code env entries Q) := by
    apply SubmissionTransfer.retire_of_poll
    intro current next worker pos func invariant accepted
    obtain ⟨processed, remaining, split, processedLength, total, suffix, property⟩ := invariant
    exact ⟨processed, remaining, split, processedLength, total, suffix, polled current next worker property accepted⟩
  have startBound : start.val ≤ code.length := by
    obtain ⟨bytes, _, span⟩ := sourceBytes
    have length := span.length
    have bound := span.bound
    omega
  obtain ⟨processed, remaining, split, processedLength, total, suffix, final⟩ :=
    SubmissionTransfer.submit source visitor state moduleId env code profile config (Progress profile code env entries Q)
      (progress_submit source visitor state moduleId env code profile config entries Q environment tail available capacity batch)
      retired before after start pending capacity startBound initialProgress accepted
  exact final
end Itasca.Runtime.Compiler.SourceSubmission

end
