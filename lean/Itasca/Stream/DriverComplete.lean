import Itasca.Stream.DriverRegions
import Itasca.Stream.SchedulerComplete
import Itasca.Stream.DriverRun
import Itasca.Stream.SubmissionComplete

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
