import Itasca.Runtime.Code.Local.Relations.Common.SubmissionTransfer
import Itasca.Stream.FramingComplete
namespace Itasca.Runtime.Code.SourceSubmission
open Aeneas Aeneas.Std Itasca ModuleBinary

/-- The unconsumed source suffix is encoded at the actual next framing cursor.
The processed prefix fixes the global source-function index independently of
any compiler certificate. -/
def Progress {V : Type} (profile : ValidationProfile) (code : Slice U8)
    (env : module.Env) (entries : List Code) (Q : V → Prop)
    (position first : Usize) (visitor : V) : Prop :=
  ∃ processed remaining, entries = processed ++ remaining ∧
    processed.length = first.val ∧ first.val + remaining.length = env.func_type_indices.val.length ∧
    At (Rep (Profile.CodeEncoding profile)) code position remaining (Slice.len code) ∧ Q visitor

/-- A local batch proof receives its exact decoded source slice and issued
function offset. This contract is instantiated by the concrete entry fold. -/
def Batch {V : Type} (visitor : stream.StreamingVisitor V) (moduleId : U64)
    (profile : ValidationProfile) (env : module.Env) (entries : List Code) (Q : V → Prop) : Prop :=
  ∀ (before after : V) (issued : StreamBatch.Issued) (processed taken remaining : List Code),
    entries = processed ++ taken ++ remaining → issued.module_id = moduleId → issued.profile = profile →
    issued.env = env → issued.first_func.val = processed.length → issued.num_funcs.val = taken.length →
    Rep (Profile.CodeEncoding profile) taken issued.code.val → issued.Bounded → Q before →
    visitor.submit_code_batch before issued.seed = .ok (.Ok (), after) → Q after

theorem progress_submit {S V : Type} (source : stream.Source S) (visitor : stream.StreamingVisitor V)
    (state : S) (moduleId : U64) (env : module.Env) (code : Slice U8)
    (profile : ValidationProfile) (config : stream.Config) (entries : List Code) (Q : V → Prop)
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
    (state : S) (moduleId : U64) (env : module.Env) (code : Slice U8)
    (profile : ValidationProfile) (config : stream.Config) (entries : List Code) (Q : V → Prop)
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
end Itasca.Runtime.Code.SourceSubmission
