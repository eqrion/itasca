import Exec.Code.Local.Source.SourceSlice
import Itasca.Stream.DriverSound
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

private theorem code_guards {env indices codes profile}
    (h : List.Forall₂ (fun idx entry => CodeEntry.Typed env idx entry profile) indices codes) :
    (∀ entry ∈ codes, ∀ group ∈ entry.locals, ModuleBinary.ValueTypeAllowed profile group.2) ∧
    (env.data_count = none → ∀ entry ∈ codes, ModuleBinary.instructionsUseData entry.body = false) := by
  induction h with
  | nil => simp
  | cons hp _ ih =>
    constructor
    · intro entry hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact hp.locals_allowed
      · exact ih.1 entry hm
    · intro hc entry hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact hp.no_data hc
      · exact ih.2 hc entry hm

private theorem assembly_guards {profile env decls codes} {segments : List module.Data}
    (hr : ModuleEnv.Represents env decls)
    (ha : ModuleBinary.ModuleTypesAllowed profile (decls.module [] []))
    (hcodes : List.Forall₂ (fun idx entry => CodeEntry.Typed env idx entry profile) env.func_type_indices.val codes)
    (hs : ∀ segment ∈ segments, ModuleData.Valid env segment)
    (hc : ∀ count, env.data_count = some count → count.val = segments.length) :
    ModuleBinary.ModuleTypesAllowed profile (decls.module codes (segments.map ModuleData.raw)) ∧
    ModuleBinary.DataCountValid (decls.module codes (segments.map ModuleData.raw)) := by
  have hg := code_guards hcodes
  constructor
  · refine ⟨ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1, hg.1, ha.2.2.2.2.2.1, ?_⟩
    intro entry hm
    obtain ⟨actual, hactual, rfl⟩ := List.mem_map.mp hm
    have hv := hs actual hactual
    cases hm : actual.mode with
    | Passive => simp [ModuleData.raw, hm]
    | Active idx offset =>
      have ho : ModuleConstants.Valid env offset .I32 := by
        exact (show idx.val < env.mem_types.val.length ∧ ModuleConstants.Valid env offset .I32 from by simpa [ModuleData.Valid, hm] using hv).2
      simpa only [ModuleData.raw, hm] using ho.const_allowed
        (show ModuleBinary.ValueTypeAllowed profile .I32 from by cases profile <;> trivial)
  · unfold ModuleBinary.DataCountValid
    change (match decls.dataCount with
      | none => ∀ entry ∈ codes, ModuleBinary.instructionsUseData entry.body = false
      | some count => count.val = (segments.map ModuleData.raw).length)
    rw [hr.dataCount]
    cases he : env.data_count with
    | none => exact hg.2 he
    | some count => simpa using hc count he


/-- Accepted driver phases recover the independent code section in the exact
buffer used for batching. This is source framing, not compiler correctness. -/
theorem stream_run_source {S V : Type} {profile : ValidationProfile}
    (source : stream.Source S) (visitor : stream.StreamingVisitor V)
    (Tracks : U64 → List StreamBatch.Issued → V → Prop)
    (hp : StreamScheduler.Provenance visitor Tracks profile)
    (id : U64) (state : S) (v v' : V) (env : module.Env)
    (data environment code tail : Slice U8)
    (hsource : StreamSource.Coherent source state environment.val code.val tail.val)
    (hbytes : data.val = environment.val ++ code.val ++ tail.val)
    (hv : Tracks id [] v)
    (run : StreamRun.Accepted source visitor id state v v' env profile) :
    ∃ raw, ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding profile) raw data.val profile ∧
      ModuleElaboration.Matches env run.remaining.tail raw ∧ ModuleEnv.Valid env profile ∧
      CodeEntry.Bounds env ∧ Profile.Environment profile env ∧
      raw.functions = env.func_type_indices.val ∧ raw.types = env.types.val ∧
      raw.codes.length = env.func_type_indices.val.length ∧
      StreamFraming.HeaderAt code env run.remaining.entries ∧
      ModuleBinary.At (ModuleBinary.Rep (Profile.CodeEncoding profile)) code run.remaining.entries raw.codes (Slice.len code) ∧
      code.length ≤ limits.MAX_MODULE_BYTES.val ∧ data.length ≤ limits.MAX_MODULE_BYTES.val := by
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
  obtain ⟨henv, hsignatures, _⟩ := ModuleEnv.profile_accepted_entry_conditions _ _ _ profile hecap hdecoded
  have hresults := hsignatures.1
  have hsem := module.validate_env.profile_semantic_spec run.environment profile
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
      ∀ ft ∈ issued.env.types.val, Profile.FuncType profile ft := by
    intro issued hi
    have he := (hinv.issued issued hi).2.1
    simpa [he] using And.intro henv hresults
  obtain ⟨_, _, hcompleted⟩ := StreamScheduler.drain_sound visitor Tracks hp id history
    run.remaining.ready v' run.remaining.pending run.remaining.remaining hready hentry hinv.profiles run.remaining.drain_call
  have hall : ∀ issued ∈ history, StreamScheduler.Completed issued profile := by
    intro issued hi
    rcases hinv.accounted issued hi with hpend | hdone
    · exact hcompleted issued hi (hinv.issued issued hi).1 hpend
    · exact hdone
  obtain ⟨codes, count, entriesEncoding, entriesTyped⟩ := hinv.partition.encoding hall
  have hcount : codes.length = env.func_type_indices.val.length := by simpa using count.symm
  have htyped := entriesTyped.forall₂ (by simpa using hcount)
  have hcode : ModuleBinary.PaddedEncoding 10#u8
      (ModuleBinary.VecEncoding (Profile.CodeEncoding profile)) [] codes code.val := by
    rcases hheader with ⟨empty, _, noFunctions⟩ | ⟨count, codeSection, _⟩
    · have noCodes : codes = [] := by simpa [noFunctions] using hcount
      simp only [noCodes, empty]
      exact ⟨[], [], .nil, .absent, rfl⟩
    · obtain ⟨bytes, encoded, span⟩ := ModuleCode.Section.encoding codeSection entriesEncoding hcount
      have sameBytes : code.val = bytes := by simpa using span.suffix
      exact ⟨[], code.val, .nil, sameBytes ▸ encoded, rfl⟩
  have htail := module.validate_tail_with.accepted_erase visitor.moduleModuleVisitorInst
    run.remaining.tailBytes 0#usize env run.remaining.region run.remaining.tail run.remaining.decodedTail
    run.remaining.decode_tail
  have htailSem := module.validate_tail.spec run.remaining.tailBytes 0#usize env (by simp) profile
  rw [htail] at htailSem
  simp only [WP.spec_ok] at htailSem
  obtain ⟨⟨tailBytes, ht, hts⟩, hsegments, hdataCount⟩ := htailSem
  have htailWhole : run.remaining.tailBytes.val = tailBytes := by simpa using hts.suffix
  let raw := ModuleElaboration.fromEnv env decls.tables decls.memories codes run.remaining.tail.data.val
  have guards := assembly_guards hrep hprefix.allowed htyped hsegments hdataCount
  have encoded : ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding profile) raw data.val profile := by
    change ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding profile)
      (ModuleElaboration.fromEnv env decls.tables decls.memories codes run.remaining.tail.data.val) data.val profile
    rw [← ModuleElaboration.represents_module hrep, hbytes]
    exact ModuleComposition.encoding (by simpa [← hwhole, heq] using hprefix) hcode
      (by simpa [← htailWhole, hteq] using ht) guards.1 guards.2
  refine ⟨raw, encoded, ModuleElaboration.matches_fromEnv _ hrep.cache, hvalid, henv, hsignatures,
    rfl, rfl, hcount, hheader, entriesEncoding, hcap, ?_⟩
  have heLength := congrArg List.length heq
  have htLength := congrArg List.length hteq
  have hdLength := congrArg List.length hbytes
  simp only [List.length_append] at hdLength
  simp only [Slice.len_val, Slice.length] at he hc hm ⊢
  omega
end Itasca.Runtime.Code
