import Itasca.Runtime.SourceMachine.Measure
import Itasca.Module.Soundness
import Itasca.Profile.BinaryUnique
import Itasca.Stream.DriverSound
import Itasca.Stream.Batch
import Itasca.Runtime.Compiler.Local.Source.SourceEntry
import Itasca.Stream.SubmissionSound
import Itasca.Stream.FramingComplete
import Itasca.Module.Elab.TypingInversion
import Itasca.Runtime.Spec.ModuleMembership
import Itasca.Module.Elab.SectionInversion

/-!
Sections, each formerly its own module: SourceSlice, SourceRun, SourceBatchLookup, SourceExecutable, SourceSubmission, SourceFunctionTyping, SourceSegmentPrograms.
-/

/-! ## SourceSlice -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- The store's code constructor for one independently decoded function. -/
def sourceFunctionCode (index : U32) (entry : ModuleBinary.Code) : funccode :=
  .FUNC (.mk_uN index.val) (entry.declared.map (fun ty => .LOCAL (Translate.valueType ty))) entry.body

def sourceFunctions (raw : ModuleBinary.Module) : List funccode :=
  List.zipWith sourceFunctionCode raw.functions raw.codes

/-- Conversion retains all source fields; the SpecTec module and store use
separate inductive constructor types. -/
def functionCode : func → funccode
  | .FUNC index locals body => .FUNC index locals body

@[simp] theorem function_code_entry (index : U32) (entry : ModuleBinary.Code) :
    functionCode (CodeEntry.function index entry) = sourceFunctionCode index entry := rfl

theorem source_functions_eq (raw : ModuleBinary.Module) :
    sourceFunctions raw = (List.zipWith CodeEntry.function raw.functions raw.codes).map functionCode := by
  simp [sourceFunctions, List.map_zipWith, Function.comp_def]

end Itasca.Runtime.Compiler

end

/-! ## SourceRun -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

private theorem code_guards {env indices codes}
    (h : List.Forall₂ (fun idx entry => CodeEntry.Typed env idx entry) indices codes) :
    env.data_count = none → ∀ entry ∈ codes, ModuleBinary.instructionsUseData entry.body = false := by
  induction h with
  | nil => simp
  | cons hp _ ih =>
    intro hc entry hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hp.no_data hc
    · exact ih hc entry hm

private theorem assembly_guards {env decls codes} {segments : List metadata.Data}
    (hr : ModuleEnv.Represents env decls)
    (hcodes : List.Forall₂ (fun idx entry => CodeEntry.Typed env idx entry) env.func_type_indices.val codes)
    (hc : ∀ count, env.data_count = some count → count.val = segments.length) :
    ModuleBinary.DataCountValid (decls.module codes (segments.map ModuleData.raw)) := by
  have hg := code_guards hcodes
  unfold ModuleBinary.DataCountValid
  change (match decls.dataCount with
    | none => ∀ entry ∈ codes, ModuleBinary.instructionsUseData entry.body = false
    | some count => count.val = (segments.map ModuleData.raw).length)
  rw [hr.dataCount]
  cases he : env.data_count with
  | none => exact hg he
  | some count => simpa using hc count he

/-- Accepted driver phases recover the independent code section in the exact
buffer used for batching. This is source framing, not compiler correctness. -/
theorem stream_run_source {S V : Type}
    (source : stream.Source S) (visitor : stream.StreamingVisitor V)
    (Tracks : U64 → List StreamBatch.Issued → V → Prop)
    (hp : StreamScheduler.Provenance visitor Tracks)
    (id : U64) (state : S) (v v' : V) (env : metadata.Env)
    (data environment code tail : Slice U8)
    (hsource : StreamSource.Coherent source state environment.val code.val tail.val)
    (hbytes : data.val = environment.val ++ code.val ++ tail.val)
    (hv : Tracks id [] v)
    (run : StreamRun.Accepted source visitor id state v v' env) :
    ∃ raw, ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding) raw data.val ∧
      ModuleElaboration.Matches env run.remaining.tail raw ∧ ModuleEnv.Valid env ∧
      CodeEntry.Bounds env ∧
      raw.functions = env.func_type_indices.val ∧ raw.types = env.types.val ∧
      raw.codes.length = env.func_type_indices.val.length ∧
      StreamFraming.HeaderAt code env run.remaining.entries ∧
      ModuleBinary.At (ModuleBinary.Rep (Profile.CodeEncoding)) code run.remaining.entries raw.codes (Slice.len code) ∧
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
  have hdecoded := metadata.validate_env_with.accepted_erase visitor.metadataModuleVisitorInst
    run.environment run.region env run.environmentLength run.decoded run.decode_environment
  obtain ⟨henv, _⟩ := ModuleEnv.profile_accepted_entry_conditions _ _ _ hecap hdecoded
  have hsem := metadata.validate_env.profile_semantic_spec run.environment
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
    run.remaining.pending run.remaining.submitted environment.val tail.val hsource henv hcap hstart
    hconfigured hsubmit
  have hended := hp.code_end id history _ _ hsubmitted run.remaining.end_call
  have htailRegion := hp.region id history _ .Tail _ hended run.remaining.region_call
  have htailDecoded := hp.tail_preserves id history run.remaining.tailBytes 0#usize _ _ env
    run.remaining.tail run.remaining.decode_tail htailRegion
  have hready := hp.tail_ready id history _ _ _ htailDecoded run.remaining.ready_call
  have hentry : ∀ issued ∈ history, CodeEntry.Bounds issued.env := by
    intro issued hi
    have he := (hinv.issued issued hi).2.1
    simpa [he] using henv
  obtain ⟨_, _, hcompleted⟩ := StreamScheduler.drain_sound visitor Tracks hp id history
    run.remaining.ready v' run.remaining.pending run.remaining.remaining hready hentry run.remaining.drain_call
  have hall : ∀ issued ∈ history, StreamScheduler.Completed issued := by
    intro issued hi
    rcases hinv.accounted issued hi with hpend | hdone
    · exact hcompleted issued hi (hinv.issued issued hi).1 hpend
    · exact hdone
  obtain ⟨codes, count, entriesEncoding, entriesTyped⟩ := hinv.partition.encoding hall
  have hcount : codes.length = env.func_type_indices.val.length := by simpa using count.symm
  have htyped := entriesTyped.forall₂ (by simpa using hcount)
  have hcode : ModuleBinary.PaddedEncoding 10#u8
      (ModuleBinary.VecEncoding (Profile.CodeEncoding)) [] codes code.val := by
    rcases hheader with ⟨empty, _, noFunctions⟩ | ⟨count, codeSection, _⟩
    · have noCodes : codes = [] := by simpa [noFunctions] using hcount
      simp only [noCodes, empty]
      exact ⟨[], [], .nil, .absent, rfl⟩
    · obtain ⟨bytes, encoded, span⟩ := ModuleCode.Section.encoding codeSection entriesEncoding hcount
      have sameBytes : code.val = bytes := by simpa using span.suffix
      exact ⟨[], code.val, .nil, sameBytes ▸ encoded, rfl⟩
  have htail := metadata.validate_tail_with.accepted_erase visitor.metadataModuleVisitorInst
    run.remaining.tailBytes 0#usize env run.remaining.region run.remaining.tail run.remaining.decodedTail
    run.remaining.decode_tail
  have htailSem := metadata.validate_tail.spec run.remaining.tailBytes 0#usize env (by simp)
  rw [htail] at htailSem
  simp only [WP.spec_ok] at htailSem
  obtain ⟨⟨tailBytes, ht, hts⟩, hsegments, hdataCount⟩ := htailSem
  have htailWhole : run.remaining.tailBytes.val = tailBytes := by simpa using hts.suffix
  let raw := ModuleElaboration.fromEnv env decls.tables decls.memories codes run.remaining.tail.data.val
  have guards := assembly_guards hrep htyped hdataCount
  have encoded : ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding) raw data.val := by
    change ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding)
      (ModuleElaboration.fromEnv env decls.tables decls.memories codes run.remaining.tail.data.val) data.val
    rw [← ModuleElaboration.represents_module hrep, hbytes]
    exact ModuleComposition.encoding (by simpa [← hwhole, heq] using hprefix) hcode
      (by simpa [← htailWhole, hteq] using ht) guards
  refine ⟨raw, encoded, ModuleElaboration.matches_fromEnv _ hrep.cache, hvalid, henv,
    rfl, rfl, hcount, hheader, entriesEncoding, hcap, ?_⟩
  have heLength := congrArg List.length heq
  have htLength := congrArg List.length hteq
  have hdLength := congrArg List.length hbytes
  simp only [List.length_append] at hdLength
  simp only [Slice.len_val, Slice.length] at he hc hm ⊢
  omega
end Itasca.Runtime.Compiler

end

/-! ## SourceBatchLookup -/

section

/-!
Lookup of independently encoded entries and their batch source positions. The batch theorem transports the entry witness through source function ordering.
-/

/-! ## Source Entry Lookup -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Prefix-unique encodings identify an entry by the number of preceding
encoded entries, even when the complete byte list has a suffix. -/
theorem encoded_entry_lookup {α : Type} {R : α → List U8 → Prop}
    (unique : ModuleBinary.PrefixUnique R)
    {entries bytes prior first value second tail rest}
    (whole : ModuleBinary.Rep R entries bytes)
    (before : ModuleBinary.Rep R prior first) (item : R value second)
    (joined : bytes ++ tail = first ++ second ++ rest)
    (bound : prior.length < entries.length) : entries[prior.length]? = some value := by
  induction before generalizing entries bytes with
  | nil =>
    cases whole with
    | nil => simp at bound
    | @cons head entries headBytes following headEncoded followingEncoded =>
      obtain ⟨rfl, _, _⟩ := unique headEncoded item (by simpa [List.append_assoc] using joined)
      simp
  | @cons head prior headBytes following headEncoded followingEncoded ih =>
    cases whole with
    | nil => simp at bound
    | @cons actual entries actualBytes remaining actualEncoded remainingEncoded =>
      obtain ⟨rfl, rfl, suffix⟩ := unique actualEncoded headEncoded (by simpa [List.append_assoc] using joined)
      simpa using ih remainingEncoded (by simpa only [List.append_assoc] using suffix) (by simpa using bound)

/-- A successful entry's actual body is the code-list member at the exact
validated prior index. Framing equality, not a compiler premise, selects it. -/
theorem witness_source_lookup {V : Type} {visitor : code.OpVisitor V}
    {data env index start finish before after}
    (w : CodeEntry.Witness visitor data env index start finish before after)
    {entries prior : List ModuleBinary.Code}
    (whole : ModuleBinary.Rep (Profile.CodeEncoding) entries data.val)
    (previous : ModuleBinary.At (ModuleBinary.Rep (Profile.CodeEncoding)) data 0#usize prior start)
    (bound : prior.length < entries.length) :
    ∃ entry, entries[prior.length]? = some entry ∧ w.groups = entry.locals ∧
      Profile.BodyEncoding w.body entry.body := by
  obtain ⟨ft, source, _, body, _⟩ := code.validate_body_with.profile_sound visitor w.body env w.ctx w.typeIdx
    w.startedState after w.body_accepted
  have actual := Profile.codeEncoding_of_parts w.header w.extent w.locals_bytes w.body_bytes body
  obtain ⟨first, prefixEncoding, prefixSpan⟩ := previous
  obtain ⟨last, lastEncoding, lastSpan⟩ := actual
  have joined : data.val ++ [] = first ++ last ++ data.val.drop finish.val := by
    have span := prefixSpan.suffix
    change data.val.drop 0 = first ++ data.val.drop start.val at span
    simp only [List.drop_zero] at span
    calc
      data.val ++ [] = data.val := List.append_nil _
      _ = first ++ data.val.drop start.val := span
      _ = first ++ last ++ data.val.drop finish.val := by rw [lastSpan.suffix, List.append_assoc]
  exact ⟨⟨w.groups, source⟩, encoded_entry_lookup (Profile.code_prefix_unique)
    whole prefixEncoding lastEncoding joined bound, rfl, body⟩

end Itasca.Runtime.Compiler

end

/-! ## Source Batch Lookup -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- The reachable worker's validated prefix identifies its next exact entry
inside the independently encoded issued code view. -/
theorem witness_batch_source_lookup {V : Type} {visitor : code.OpVisitor V}
    {issued : StreamBatch.Issued} {batch : stream.CodeBatch}
    {index finish before after}
    (w : CodeEntry.Witness visitor batch.code batch.env index batch.validated_end finish before after)
    (reachable : StreamBatch.Reachable issued batch)
    (bounds : CodeEntry.Bounds batch.env)
    {entries : List ModuleBinary.Code}
    (whole : ModuleBinary.Rep (Profile.CodeEncoding) entries issued.code.val)
    (count : batch.num_validated.val < entries.length) :
    ∃ entry, entries[batch.num_validated.val]? = some entry ∧ w.groups = entry.locals ∧
      Profile.BodyEncoding w.body entry.body := by
  obtain ⟨identity, previous, _⟩ := reachable.validation
  obtain ⟨_, _, envEq, codeEq, _, _, _⟩ := identity
  have bound : CodeEntry.Bounds issued.env := by simpa only [envEq] using bounds
  obtain ⟨prior, length, encoded, _⟩ := previous.typed bound
  have priorBytes : ModuleBinary.At (ModuleBinary.Rep (Profile.CodeEncoding))
      batch.code 0#usize prior batch.validated_end := by simpa only [codeEq] using encoded
  have complete : ModuleBinary.Rep (Profile.CodeEncoding) entries batch.code.val := by
    simpa only [ codeEq] using whole
  obtain ⟨entry, found, groups, body⟩ := witness_source_lookup w complete priorBytes (by omega)
  exact ⟨entry, by simpa only [length] using found, groups, body⟩

/-- The code-view ordinal is translated to the complete decoded code list by
its exact preceding source entries. -/
theorem source_entry_offset {prior entries remaining : List ModuleBinary.Code} {index entry}
    (found : entries[index]? = some entry) :
    (prior ++ entries ++ remaining)[prior.length + index]? = some entry := by
  rw [List.append_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
  exact found

theorem source_functions_lookup {raw : ModuleBinary.Module} {index : Nat} {typeIndex entry}
    (typeFound : raw.functions[index]? = some typeIndex)
    (codeFound : raw.codes[index]? = some entry) :
    (sourceFunctions raw)[index]? = some (sourceFunctionCode typeIndex entry) := by
  have typeBound := (List.getElem?_eq_some_iff.mp typeFound).1
  have codeBound := (List.getElem?_eq_some_iff.mp codeFound).1
  have bound : index < (sourceFunctions raw).length := by simp [sourceFunctions]; omega
  apply List.getElem?_eq_some_iff.mpr
  refine ⟨bound, ?_⟩
  simp only [sourceFunctions, List.getElem_zipWith]
  rw [(List.getElem?_eq_some_iff.mp typeFound).2, (List.getElem?_eq_some_iff.mp codeFound).2]

end Itasca.Runtime.Compiler

end

end

/-! ## SourceExecutable -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Coverage of every independently decoded function body by the complete
execution source grammar. This predicate imposes no subset restriction. -/
def ModuleExecutable (raw : ModuleBinary.Module) : Prop :=
  ∀ entry ∈ raw.codes, Forall SourceMachine.BinaryInstr entry.body

namespace SourceExecutable
private theorem rep_all {α : Type} {R : α → List U8 → Prop} {P : α → Prop}
    (entry : ∀ value bytes, R value bytes → P value) {values bytes}
    (encoded : ModuleBinary.Rep R values bytes) : Forall P values := by
  induction encoded with
  | nil => simp [Forall]
  | cons first _ ih =>
    simpa [Forall, or_imp, forall_and] using And.intro (entry _ _ first) ih

private theorem padded_all {α : Type} {R : α → List U8 → Prop} {P : α → Prop}
    (entry : ∀ value bytes, R value bytes → P value) {id values bytes}
    (encoded : ModuleBinary.PaddedEncoding id (ModuleBinary.VecEncoding R) [] values bytes) :
    Forall P values := by
  obtain ⟨customs, sec, _, secProof, _⟩ := encoded
  cases secProof with
  | absent => simp [Forall]
  | present content =>
    obtain ⟨size, payload, _, ⟨count, entries, _, entriesEncoded, _⟩, _⟩ := content
    exact rep_all entry entriesEncoded

theorem body_bytes {source bytes} (encoded : Profile.BodyBytes source bytes) :
    Forall SourceMachine.BinaryInstr source := by
  obtain ⟨tokens, encoded, inner, rfl, emitted⟩ := encoded
  have known := rep_all (fun _ _ h => token_wasm2 h) encoded
  exact emits_wasm2 emitted (fun token member => known token (List.mem_append_left _ member))

theorem code {entry bytes} (encoded : Profile.CodeEncoding entry bytes) :
    Forall SourceMachine.BinaryInstr entry.body := by
  obtain ⟨size, locals, body, _, _, bodyEncoded, _⟩ := encoded
  exact body_bytes bodyEncoded

/-- Independent full-module encoding suffices for all executable source bodies;
no validator callback or compiler correctness assumption occurs. -/
theorem module {raw bytes}
    (encoded : ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding) raw bytes) :
    ModuleExecutable raw := by
  obtain ⟨types, imports, functions, tables, memories, globals, exports, start, elements, dataCount,
    codes, datas, customs, _, _, _, _, _, _, _, _, _, _, codeSection, _, _, _, _⟩ := encoded
  exact padded_all (fun _ _ h => code h) codeSection

/-- The canonical function-code list retains the coverage of its decoded bodies. -/
theorem functions {raw bytes}
    (encoded : ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding) raw bytes) :
    ∀ source ∈ sourceFunctions raw, match source with
      | .HOST _ => False
      | .FUNC _ _ body => Forall SourceMachine.BinaryInstr body := by
  have all : ∀ (indices : List U32) (entries : List ModuleBinary.Code),
      (∀ entry ∈ entries, Forall SourceMachine.BinaryInstr entry.body) →
      ∀ source ∈ List.zipWith sourceFunctionCode indices entries, match source with
        | .HOST _ => False
        | .FUNC _ _ body => Forall SourceMachine.BinaryInstr body := by
    intro indices
    induction indices with
    | nil => simp
    | cons index indices ih =>
      intro entries known source member
      cases entries with
      | nil => simp at member
      | cons entry entries =>
        simp only [List.zipWith_cons_cons, List.mem_cons] at member
        rcases member with rfl | member
        · exact known entry (by simp)
        · exact ih entries (fun e he => known e (by simp [he])) source member
  exact all raw.functions raw.codes (module encoded)

end SourceExecutable
end Itasca.Runtime.Compiler

end

/-! ## SourceSubmission -/

section

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
     (config : stream.Config) (P : Usize → Usize → V → Prop) : Prop :=
  ∀ (v v' : V) (pos func batchId finish next count : Usize) (bytes : Slice U8),
    P pos func v → pos.val ≤ code.length → func.val < env.func_type_indices.val.length →
    stream.get_next_batch source state (Slice.len code) pos func (alloc.vec.Vec.len env.func_type_indices)
      config.batch_bytes = .ok (.Ok (finish, next)) →
    stream.read_exact source state pos finish = .ok (.Ok bytes) →
    count.val = next.val - func.val →
    visitor.submit_code_batch v
      { module_id := moduleId, batch_id := batchId, env, code := bytes,
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
     (config : stream.Config) (P : Usize → Usize → V → Prop)
    (submitted : Submit source visitor state moduleId env code config P)
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
     (config : stream.Config) (P : Usize → Usize → V → Prop)
    (submitted : Submit source visitor state moduleId env code config P)
    (retired : Retire visitor moduleId P)
    (v : V) (pending : alloc.vec.Vec Usize) (pos func batchId : Usize)
    (hcap : code.length ≤ limits.MAX_MODULE_BYTES.val)
    (hpos : pos.val ≤ code.length) (hfunc : func.val ≤ env.func_type_indices.val.length)
    (hv : P pos func v)
    (out : ControlFlow (V × alloc.vec.Vec Usize × Usize × Usize × Usize)
      (core.result.Result (alloc.vec.Vec Usize) error.Error × V))
    (h : stream.submit_code_batches_loop.body source visitor moduleId state env.types env.imports
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
        exact resume source visitor state moduleId env code config P submitted v' remaining
          pos func batchId hcap hpos hv' (by scalar_tac) out h
    · rw [if_neg hfull] at h
      exact resume source visitor state moduleId env code config P submitted v pending
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
     (config : stream.Config) (P : Usize → Usize → V → Prop)
    (submitted : Submit source visitor state moduleId env code config P)
    (retired : Retire visitor moduleId P)
    (v : V) (pending : alloc.vec.Vec Usize) (pos func batchId : Usize)
    (hcap : code.length ≤ limits.MAX_MODULE_BYTES.val)
    (hpos : pos.val ≤ code.length) (hfunc : func.val ≤ env.func_type_indices.val.length)
    (hv : P pos func v)
    (finalPending : alloc.vec.Vec Usize) (finalV : V)
    (h : stream.submit_code_batches_loop source visitor moduleId state env.types env.imports
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
    have hs := body source visitor state moduleId env code config P submitted retired
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
      have recursive : stream.submit_code_batches_loop source visitor moduleId state env.types env.imports
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
     (config : stream.Config) (P : Usize → Usize → V → Prop)
    (submitted : Submit source visitor state moduleId env code config P)
    (retired : Retire visitor moduleId P)
    (v finalV : V) (start : Usize) (pending : alloc.vec.Vec Usize)
    (hcap : code.length ≤ limits.MAX_MODULE_BYTES.val) (hstart : start.val ≤ code.length)
    (initial : P start 0#usize v)
    (accepted : stream.submit_code_batches source visitor moduleId state env (Slice.len code) start config v =
      .ok (.Ok pending, finalV)) :
    P (Slice.len code) (alloc.vec.Vec.len env.func_type_indices) finalV :=
  loop source visitor state moduleId env code config P submitted retired
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
def Progress {V : Type} (code : Slice U8)
    (env : metadata.Env) (entries : List ModuleBinary.Code) (Q : V → Prop)
    (position first : Usize) (visitor : V) : Prop :=
  ∃ processed remaining, entries = processed ++ remaining ∧
    processed.length = first.val ∧ first.val + remaining.length = env.func_type_indices.val.length ∧
    At (Rep (Profile.CodeEncoding)) code position remaining (Slice.len code) ∧ Q visitor

/-- A local batch proof receives its exact decoded source slice and issued
function offset. This contract is instantiated by the concrete entry fold. -/
def Batch {V : Type} (visitor : stream.StreamingVisitor V) (moduleId : U64)
     (env : metadata.Env) (entries : List ModuleBinary.Code) (Q : V → Prop) : Prop :=
  ∀ (before after : V) (issued : StreamBatch.Issued) (processed taken remaining : List ModuleBinary.Code),
    entries = processed ++ taken ++ remaining → issued.module_id = moduleId →
    issued.env = env → issued.first_func.val = processed.length → issued.num_funcs.val = taken.length →
    Rep (Profile.CodeEncoding) taken issued.code.val → issued.Bounded → Q before →
    visitor.submit_code_batch before issued.seed = .ok (.Ok (), after) → Q after

theorem progress_submit {S V : Type} (source : stream.Source S) (visitor : stream.StreamingVisitor V)
    (state : S) (moduleId : U64) (env : metadata.Env) (code : Slice U8)
     (config : stream.Config) (entries : List ModuleBinary.Code) (Q : V → Prop)
    (environment tail : List U8) (available : StreamSource.Available source state environment code.val tail)
    (capacity : code.length ≤ limits.MAX_MODULE_BYTES.val)
    (batch : Batch visitor moduleId env entries Q) :
    SubmissionTransfer.Submit source visitor state moduleId env code config (Progress code env entries Q) := by
  intro before after pos first batchId finish next count bytes progress position more framed read counted submitted
  obtain ⟨processed, remaining, split, processedLength, total, suffix, invariant⟩ := progress
  have effect := stream.get_next_batch.complete_spec source state environment tail code available
    (Profile.CodeEncoding) (fun _ _ h => h) (Slice.len code) pos first
    (alloc.vec.Vec.len env.func_type_indices) config.batch_bytes remaining rfl capacity more total suffix
  rw [framed, WP.spec_ok] at effect
  obtain ⟨actualFinish, actualNext, taken, rest, same, bounded, remainingEq, nonempty, advanced, restCount, takenAt, restAt⟩ := effect
  obtain ⟨rfl, rfl⟩ := by simpa using same
  obtain ⟨view, viewed, span, encoded⟩ := stream.read_exact.complete_rep source state environment tail code available
    (Profile.CodeEncoding) pos finish taken takenAt
  have bytesEq : view = bytes := by simpa [read] using viewed.symm
  subst view
  let issued : StreamBatch.Issued := ⟨moduleId, batchId, env, bytes, pos, first, count, ⟩
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
  have changed := batch before after issued processed taken rest sourceEq rfl rfl
    processedLength.symm countEq encoded issuedBound invariant submitted
  refine ⟨processed ++ taken, rest, sourceEq, ?_, restCount.symm, restAt, changed⟩
  simp only [List.length_append, processedLength, advanced]

/-- Actual submission preserves a concrete compiler invariant for a fixed
independently encoded source list, provided each real issued batch is checked. -/
theorem submit {S V : Type} (source : stream.Source S) (visitor : stream.StreamingVisitor V)
    (state : S) (moduleId : U64) (env : metadata.Env) (code : Slice U8)
     (config : stream.Config) (entries : List ModuleBinary.Code) (Q : V → Prop)
    (environment tail : List U8) (available : StreamSource.Available source state environment code.val tail)
    (capacity : code.length ≤ limits.MAX_MODULE_BYTES.val)
    (start : Usize) (sourceBytes : At (Rep (Profile.CodeEncoding)) code start entries (Slice.len code))
    (count : entries.length = env.func_type_indices.val.length)
    (batch : Batch visitor moduleId env entries Q)
    (polled : ∀ before after worker, Q before → visitor.poll_code_batch before = .ok (.Ok worker, after) → Q after)
    (before after : V) (pending : alloc.vec.Vec Usize) (initial : Q before)
    (accepted : stream.submit_code_batches source visitor moduleId state env (Slice.len code) start config before =
      .ok (.Ok pending, after)) : Q after := by
  have initialProgress : Progress code env entries Q start 0#usize before :=
    ⟨[], entries, by simp, by simp, by simpa using count, sourceBytes, initial⟩
  have retired : SubmissionTransfer.Retire visitor moduleId (Progress code env entries Q) := by
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
    SubmissionTransfer.submit source visitor state moduleId env code config (Progress code env entries Q)
      (progress_submit source visitor state moduleId env code config entries Q environment tail available capacity batch)
      retired before after start pending capacity startBound initialProgress accepted
  exact final
end Itasca.Runtime.Compiler.SourceSubmission

end

end

/-! ## SourceFunctionTyping -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Generated function typing also supplies the runtime function-code syntax.
The two generated datatypes use the same source fields. -/
theorem function_code_wf {C index locals body type}
    (typed : Func_ok C (.FUNC index locals body) type) :
    wf_funccode (.FUNC index locals body) := by
  have wfSource : wf_func (.FUNC index locals body) := by cases typed; assumption
  cases wfSource
  constructor <;> assumption

/-- The independently decoded module determines each defined source function's
actual type. This is a projection of generated module typing. -/
theorem source_function_typed {raw : ModuleBinary.Module}
    (elaborates : ModuleElaboration.Elaborates raw (ModuleElaboration.moduleOf raw))
    (typed : Module_ok (ModuleElaboration.moduleOf raw))
    (position : Nat) (index : U32) (entry : ModuleBinary.Code)
    (indexFound : raw.functions[position]? = some index)
    (entryFound : raw.codes[position]? = some entry) :
    Func_ok (ModuleElaboration.contextOf raw) (CodeEntry.function index entry)
      (ModuleElaboration.functionType raw.types index) := by
  have paired := (ModuleElaboration.sections_of_typing elaborates typed).functions
  have left := (List.getElem?_eq_some_iff.mp indexFound).1
  have right := (List.getElem?_eq_some_iff.mp entryFound).1
  have result := paired.get left right
  simpa only [List.get_eq_getElem, (List.getElem?_eq_some_iff.mp indexFound).2,
    (List.getElem?_eq_some_iff.mp entryFound).2] using result

/-- Every export name of a typed source module has generated Unicode syntax. -/
theorem source_export_name_wf {raw : ModuleBinary.Module}
    (elaborates : ModuleElaboration.Elaborates raw (ModuleElaboration.moduleOf raw))
    (typed : Module_ok (ModuleElaboration.moduleOf raw))
    (entry : ModuleBinary.Export) (member : entry ∈ raw.exports) :
    wf_name (ModuleBinary.nameOfBytes entry.name) := by
  obtain ⟨ty, checked⟩ := (ModuleElaboration.sections_of_typing elaborates typed).exports entry member
  have wfExport : wf_export (ModuleElaboration.exportDecl entry) := by cases checked; assumption
  cases wfExport
  assumption

/-- Every retained source function has the generated typing derivation selected
by the independent module's type-index vector. -/
theorem source_functions_typed {raw : ModuleBinary.Module}
    (elaborates : ModuleElaboration.Elaborates raw (ModuleElaboration.moduleOf raw))
    (typed : Module_ok (ModuleElaboration.moduleOf raw)) :
    ∀ source ∈ sourceFunctions raw, ∃ index locals body type,
      source = .FUNC index locals body ∧ Func_ok (ModuleElaboration.contextOf raw) (.FUNC index locals body) type := by
  have all : ∀ {indices entries}, List.Forall₂
      (fun index entry => Func_ok (ModuleElaboration.contextOf raw) (CodeEntry.function index entry)
        (ModuleElaboration.functionType raw.types index)) indices entries →
      ∀ source ∈ List.zipWith CodeEntry.function indices entries,
        ∃ type, Func_ok (ModuleElaboration.contextOf raw) source type := by
    intro indices entries paired
    induction paired with
    | nil => simp
    | cons first rest ih =>
      intro source member
      simp only [List.zipWith_cons_cons, List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨_, first⟩
      · exact ih source member
  intro source member
  rw [source_functions_eq] at member
  obtain ⟨function, found, rfl⟩ := List.mem_map.mp member
  obtain ⟨type, checked⟩ := all (ModuleElaboration.sections_of_typing elaborates typed).functions function found
  cases function with
  | FUNC index locals body => exact ⟨index, locals, body, type, rfl, checked⟩

theorem source_functions_wf {raw : ModuleBinary.Module}
    (elaborates : ModuleElaboration.Elaborates raw (ModuleElaboration.moduleOf raw))
    (typed : Module_ok (ModuleElaboration.moduleOf raw)) :
    Forall wf_funccode (sourceFunctions raw) := by
  intro source member
  obtain ⟨index, locals, body, type, rfl, checked⟩ := source_functions_typed elaborates typed source member
  exact function_code_wf checked

end Itasca.Runtime.Compiler

end

/-! ## SourceSegmentPrograms -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- The generated data-mode typing rule fixes active memory indices to zero. -/
theorem source_data_single_memory {C : context} (segment : ModuleBinary.Data)
    (typed : Data_ok C (ModuleData.translate segment)) :
    Spec.Segment.singleMemoryData (ModuleData.translate segment) := by
  have mode := ModuleElaboration.data_mode_typed typed
  cases equal : segment.mode with
  | Passive => simp [Spec.Segment.singleMemoryData, ModuleData.translate, ModuleSegments.dataMode, equal]
  | Active index offset =>
    change Datamode_ok C (ModuleSegments.dataMode segment.mode) at mode
    rw [equal] at mode
    have bound := (ModuleElaboration.datamode_active_properties mode).1
    simpa only [Spec.Segment.singleMemoryData, ModuleData.translate, equal, ModuleSegments.dataMode] using bound

theorem source_datas_single_memory (raw : ModuleBinary.Module)
    (elaborates : ModuleElaboration.Elaborates raw (ModuleElaboration.moduleOf raw))
    (typed : Module_ok (ModuleElaboration.moduleOf raw)) :
    ∀ segment ∈ raw.data.map ModuleData.translate, Spec.Segment.singleMemoryData segment := by
  intro segment member
  obtain ⟨rawSegment, present, rfl⟩ := List.mem_map.mp member
  exact source_data_single_memory rawSegment ((ModuleElaboration.sections_of_typing elaborates typed).data rawSegment present)
end Itasca.Runtime.Compiler

end
