import Itasca.StreamRun
import Itasca.StreamSubmission
import Itasca.ModuleDecomposed
import Itasca.ModuleSoundness

open Aeneas Aeneas.Std

namespace Itasca

/-- Acceptance of the actual streaming driver certifies the concatenated bytes,
its returned environment, and the tail from its actual delivery call. Soundness
requires coherent views and worker provenance, not callback termination or
prevalidated bodies. -/
theorem stream.validate_streaming.wasm_sound {S V : Type}
    (source : stream.Source S) (visitor : stream.StreamingVisitor V)
    (Tracks : U64 → List StreamBatch.Issued → V → Prop)
    (hp : StreamScheduler.Provenance visitor Tracks)
    (id : U64) (state : S) (v v' : V) (storage env : module.Env)
    (data environment code tail : Slice U8)
    (hsource : StreamSource.Coherent source state environment.val code.val tail.val)
    (hbytes : data.val = environment.val ++ code.val ++ tail.val)
    (hv : Tracks id [] v)
    (h : stream.validate_streaming source visitor id state v storage = .ok (.Ok (), v', env)) :
    ∃ run : StreamRun.Accepted source visitor id state v v' env,
      ModuleSound.Validated data ⟨env, run.remaining.tail⟩ ∧
      data.length ≤ limits.MAX_MODULE_BYTES.val := by
  obtain ⟨run⟩ := stream.validate_streaming.accepted source visitor id state v v' storage env h
  have heq := hsource.environment_eq run.environment run.environment_call
  have hteq := hsource.tail_eq run.remaining.tailBytes run.remaining.tail_call
  have hlen := hsource.code_len_eq run.remaining.codeLength run.remaining.length_call
  have he := limits.add_offset.spec 0#usize (Slice.len run.environment)
  rw [run.environment_bound] at he
  simp only [WP.spec_ok] at he
  have hc := limits.add_offset.spec run.environmentLength run.remaining.codeLength
  rw [run.remaining.code_bound] at hc
  simp only [WP.spec_ok] at hc
  have hm := limits.add_offset.spec run.remaining.codeEnd (Slice.len run.remaining.tailBytes)
  rw [run.remaining.module_bound] at hm
  simp only [WP.spec_ok] at hm
  have hend : run.environmentLength = Slice.len run.environment := by
    apply UScalar.eq_of_val_eq
    simpa using he.1
  have hcap : code.length ≤ limits.MAX_MODULE_BYTES.val := by
    simp only [Slice.length] at ⊢
    omega
  have hecap : run.environment.length ≤ limits.MAX_MODULE_BYTES.val := by
    have := he.2
    rw [hend] at this
    simpa using this
  have hdecoded := module.validate_env_with.accepted_erase visitor.moduleModuleVisitorInst
    run.environment run.region env run.environmentLength run.decoded run.decode_environment
  obtain ⟨henv, hresults⟩ := ModuleEnv.accepted_entry_conditions _ _ _ hecap hdecoded
  have hsem := module.validate_env.semantic_spec run.environment
  rw [hdecoded] at hsem
  simp only [WP.spec_ok] at hsem
  obtain ⟨decls, hrep, hvalid, _, _, before, hprefix, hspan⟩ := hsem
  have hwhole : run.environment.val = before := by
    rw [hend] at hspan
    simpa using hspan.suffix
  have hheader := stream.read_code_header.sound source state run.remaining.codeLength env
    run.remaining.entries code environment.val tail.val hsource hlen run.remaining.header_call
  have hstart : run.remaining.entries.val ≤ code.length := by
    rcases hheader with hempty | ⟨_, _, hb⟩
    · simp [hempty.1, hempty.2.1, Slice.length]
    · exact hb
  have hcodeLen : run.remaining.codeLength = Slice.len code := by
    apply UScalar.eq_of_val_eq
    exact hlen
  have hregion := hp.region id [] v .Environment run.region hv run.region_call
  have hdecodedTracks := hp.environment_preserves id [] run.environment run.region run.decoded
    env run.environmentLength run.decode_environment hregion
  have hconfigured := hp.environment id [] run.decoded env run.remaining.config run.remaining.configured
    hdecodedTracks run.remaining.configured_call
  have hsubmit := run.remaining.submit_call
  rw [hcodeLen] at hsubmit
  obtain ⟨history, nextId, hinv, hsubmitted⟩ := stream.submit_code_batches.sound source visitor Tracks hp
    state id env code run.remaining.entries run.remaining.config run.remaining.configured
    run.remaining.pending run.remaining.submitted environment.val tail.val hsource henv hresults hcap hstart
    hconfigured hsubmit
  have hended := hp.code_end id history _ _ hsubmitted run.remaining.end_call
  have htailRegion := hp.region id history _ .Tail _ hended run.remaining.region_call
  have htailDecoded := hp.tail_preserves id history run.remaining.tailBytes 0#usize _ _ env
    run.remaining.tail run.remaining.decode_tail htailRegion
  have hready := hp.tail_ready id history _ _ _ htailDecoded run.remaining.ready_call
  have hentry : ∀ issued ∈ history, CodeEntry.Bounds issued.env ∧
      ∀ ft ∈ issued.env.types.val, ft.results.val.length ≤ 1 := by
    intro issued hi
    have he := (hinv.issued issued hi).2.1
    simpa [he] using And.intro henv hresults
  obtain ⟨_, _, hcompleted⟩ := StreamScheduler.drain_sound visitor Tracks hp id history
    run.remaining.ready v' run.remaining.pending run.remaining.remaining hready hentry run.remaining.drain_call
  have hall : ∀ issued ∈ history, StreamScheduler.Completed issued := by
    intro issued hi
    rcases hinv.accounted issued hi with hpend | hdone
    · exact hcompleted issued hi (hinv.issued issued hi).1 hpend
    · exact hdone
  obtain ⟨codes, hcode, htyped⟩ := StreamScheduler.Partition.code hheader hinv.partition hall
  have htail := module.validate_tail_with.accepted_erase visitor.moduleModuleVisitorInst
    run.remaining.tailBytes 0#usize env run.remaining.region run.remaining.tail run.remaining.decodedTail
    run.remaining.decode_tail
  have htailSem := module.validate_tail.spec run.remaining.tailBytes 0#usize env (by simp)
  rw [htail] at htailSem
  simp only [WP.spec_ok] at htailSem
  obtain ⟨⟨tailBytes, ht, hts⟩, hsegments⟩ := htailSem
  have htailWhole : run.remaining.tailBytes.val = tailBytes := by simpa using hts.suffix
  refine ⟨run, ?_, ?_⟩
  · exact ModuleSound.assembled_regions hbytes (by simpa [← hwhole, heq] using hprefix)
      hrep hvalid hcode htyped (by simpa [← htailWhole, hteq] using ht) hsegments
  · have heLength := congrArg List.length heq
    have htLength := congrArg List.length hteq
    have hdLength := congrArg List.length hbytes
    simp only [List.length_append] at hdLength
    simp only [Slice.len_val, Slice.length] at he hc hm ⊢
    omega

end Itasca
