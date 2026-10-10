import Itasca.StreamSliceComplete
import Itasca.StreamHeaderComplete
import Itasca.ModuleEnvComplete
import Itasca.ModuleRequirementsProof
import Itasca.ModuleReadyMetadata
import Itasca.ModuleCodeTyped
import Itasca.ModuleDataMaterialize
import Itasca.ModuleTailComplete
import Itasca.ModuleDecomposed

open Aeneas Aeneas.Std

namespace Itasca.ModuleBinary

/-- An independent encoding of a complete region remains the same encoding
when that region is supplied as its own streaming buffer. -/
theorem At.on_region {α : Type} {R : α → List U8 → Prop}
    {data region : Slice U8} {start next : Usize} {value : α}
    (hregion : Wasm.BytesAt data start region.val next)
    (h : At R data start value next) :
    At R region 0#usize value (Slice.len region) := by
  obtain ⟨bytes, he, hs⟩ := h
  refine ⟨bytes, he, hregion.restrict hs ?_ ?_ (Nat.le_refl _)⟩
  · simp
  · simpa using hregion.length

theorem Rep.locals_within_limits {entries bytes}
    (h : Rep CodeEncodingWithinLimits entries bytes) :
    ∀ entry ∈ entries, entry.declared.length ≤ limits.MAX_LOCALS.val := by
  induction h with
  | nil => simp
  | @cons entry entries first rest he hs ih =>
    intro value hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact he.local_bound
    · exact ih value hv

end Itasca.ModuleBinary

namespace Itasca.ModuleCode

/-- Generated typing in index order and independent local-limit witnesses
supply the entry certificates used by streaming batches. -/
theorem EntriesTyped.of_forall₂ {env entries i}
    (ht : List.Forall₂ (CodeEntry.Typed env) (env.func_type_indices.val.drop i) entries)
    (hb : ∀ entry ∈ entries, entry.declared.length ≤ limits.MAX_LOCALS.val) :
    EntriesTyped env i entries := by
  induction entries generalizing i with
  | nil => exact .nil _
  | cons entry entries ih =>
    have hlen := ht.length_eq
    have hi : i < env.func_type_indices.val.length := by
      simp only [List.length_drop, List.length_cons] at hlen
      omega
    rw [List.drop_eq_getElem_cons hi] at ht
    cases ht with
    | cons he hs =>
      exact .cons ⟨hi, he, hb _ (by simp)⟩
        (ih hs (fun value hv => hb value (by simp [hv])))

end Itasca.ModuleCode

namespace Itasca.StreamCompleteRegions

open ModuleBinary ModuleElaboration

/-- The actual splitter and slice operations produce these three byte regions. -/
def Split (data : Slice U8) (source : stream.SliceSource) : Prop :=
  ∃ codePos tailPos,
    stream.find_code_region data = .ok (codePos, tailPos) ∧
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      data ⟨0#usize, codePos⟩ = .ok source.env ∧
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      data ⟨codePos, tailPos⟩ = .ok source.code ∧
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      data ⟨tailPos, Slice.len data⟩ = .ok source.tail

/-- Region certificates are derived from independent encoding and typing.
They expose the shared component parser results, while body checking remains
a consequence of typed bounded encodings for the later streaming driver. -/
structure Certificate (data : Slice U8) (raw : ModuleBinary.Module)
    (source : stream.SliceSource) (env : module.Env) (tail : module.Tail) : Prop where
  split : Split data source
  bytes : data.val = source.env.val ++ source.code.val ++ source.tail.val
  bounded : data.length ≤ limits.MAX_MODULE_BYTES.val
  environment : module.validate_env source.env = .ok (.Ok (env, Slice.len source.env))
  ready : ∃ decls, ModuleEnv.Ready raw 9 decls env
  entry_bounds : CodeEntry.Bounds env
  profile : Wasm1.Environment env
  code : ∃ entries, StreamFraming.HeaderAt source.code env entries ∧
    At (Rep CodeEncodingWithinLimits) source.code entries raw.codes (Slice.len source.code)
  typed : ModuleCode.EntriesTyped env 0 raw.codes
  code_count : raw.codes.length = env.func_type_indices.val.length
  tail_accepted : module.validate_tail source.tail 0#usize env = .ok (.Ok tail)
  realization : Matches env tail raw
  metadata : AccessorTypes env raw

private theorem slice_spec (data : Slice U8) (first last : Usize)
    (hfirst : first.val ≤ last.val) (hlast : last.val ≤ data.length) :
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      data ⟨first, last⟩ ⦃ region => Wasm.BytesAt data first region.val last ⦄ := by
  step
  apply Wasm.BytesAt.of_slice_view hfirst hlast
  assumption

/-- Component completeness for the canonical streaming regions. No legacy
module/code driver execution or assumed parser/body success is required. -/
theorem prepare (data : Slice U8) (raw : ModuleBinary.Module)
    (hb : ModuleEncodingWithinLimits raw data.val)
    (he : Elaborates raw (moduleOf raw))
    (ht : Module_ok (moduleOf raw)) (hp : Profile raw) :
    ∃ source env tail, Certificate data raw source env tail := by
  have hs := sections_of_typing he ht
  have hr := requirements_of_typing he hs hp
  obtain ⟨decls, codePos, tailPos, hl⟩ := ModuleLayout.normalize data raw hb
  have hsplit := stream.find_code_region.complete_layout hl
  obtain ⟨hcodePos, htailPos⟩ := stream.find_code_region.bounds data codePos tailPos hsplit
  obtain ⟨environment, henvSlice, henvSpan⟩ := WP.spec_imp_exists
    (slice_spec data 0#usize codePos (by simp) (by omega))
  obtain ⟨code, hcodeSlice, hcodeSpan⟩ := WP.spec_imp_exists
    (slice_spec data codePos tailPos hcodePos htailPos)
  obtain ⟨tailBytes, htailSlice, htailSpan⟩ := WP.spec_imp_exists
    (slice_spec data tailPos (Slice.len data) (by simpa using htailPos) (by simp))
  have henvEnc := hl.environment.on_region henvSpan
  obtain ⟨env, finalDecls, henv, hready⟩ := module.validate_env.complete
    environment raw decls (Slice.len environment) henvEnc hl.raw_eq (.inl rfl) hr
  have henvSize : environment.length ≤ limits.MAX_MODULE_BYTES.val := by
    have := henvSpan.length
    have := hb.1
    have := hl.environment.span.2
    simp only [Slice.length] at *
    omega
  have hbounds := (ModuleEnv.accepted_entry_conditions environment env
    (Slice.len environment) henvSize henv).1
  have harity : ∀ ft ∈ env.types.val, ft.results.val.length ≤ 1 := by
    simpa [hready.types_eq (by omega)] using hp.arity
  have hprofile : Wasm1.Environment env :=
    ⟨hready.represents.cache.func_arity harity, harity⟩
  have htypes := hl.code.typed hready hs hp
  have hcount : raw.codes.length = env.func_type_indices.val.length := htypes.length_eq.symm
  have hcode : ∃ entries, StreamFraming.HeaderAt code env entries ∧
      At (Rep CodeEncodingWithinLimits) code entries raw.codes (Slice.len code) := by
    rcases hl.code with hcode | ⟨hempty, hsame, _⟩
    · have henc := hcode.on_region hcodeSpan
      obtain ⟨content, hheader, hpayload⟩ := henc.section_split
      obtain ⟨count, entries, hn, hdecoded, hentries⟩ := hpayload.vector_split
      exact ⟨entries, .inr ⟨count, ⟨content, hheader, hdecoded, hn.trans hcount⟩,
        hentries.span.1.trans hentries.span.2⟩, hentries⟩
    · have hzero : code.val = [] := by
        apply List.eq_nil_of_length_eq_zero
        have := hcodeSpan.length
        rw [hsame] at this
        omega
      have hfuncs : env.func_type_indices.val = [] := by
        apply List.eq_nil_of_length_eq_zero
        simpa [hempty] using hcount.symm
      refine ⟨0#usize, .inl ⟨hzero, rfl, hfuncs⟩, [], ?_, ?_⟩
      · simpa [hempty] using (Rep.nil : Rep CodeEncodingWithinLimits [] [])
      · exact ⟨by simp [hzero], by simp [hzero], by simp⟩
  have htyped : ModuleCode.EntriesTyped env 0 raw.codes := by
    obtain ⟨_, _, bytes, henc, _⟩ := hcode
    apply ModuleCode.EntriesTyped.of_forall₂ (by simpa using htypes)
    exact henc.locals_within_limits
  have htailEnc := hl.tail.on_region htailSpan
  obtain ⟨segments, hsegments, hvalid⟩ := ModuleTail.materialize
    tailBytes 0#usize (Slice.len tailBytes) raw finalDecls env htailEnc hs hready
  let tail : module.Tail := ⟨segments⟩
  have htail := module.validate_tail.complete tail (by simpa [tail, hsegments] using htailEnc) hvalid
  have hmatches := hready.matches tail hsegments
  have hsemantic := module.validate_env.semantic_spec environment
  rw [henv] at hsemantic
  simp only [WP.spec_ok] at hsemantic
  obtain ⟨_, hrep, hv, _, _, hprefix⟩ := hsemantic
  obtain ⟨bytes, hprefix, _⟩ := hprefix
  have hnames : ∀ entry ∈ env.exports.val, wf_name (ModuleBinary.nameOfBytes entry.name.val) := by
    intro entry hentry
    exact hprefix.export_names_wf (ModuleEnv.rawExport entry)
      (by rw [hrep.exports]; exact List.mem_map.mpr ⟨entry, hentry, rfl⟩)
  have hmeta := accessorTypes hmatches.2 hv hnames (codes := raw.codes) (segments := tail.data.val)
  rw [← hmatches.1] at hmeta
  refine ⟨⟨environment, code, tailBytes⟩, env, tail, ?_⟩
  exact ⟨⟨codePos, tailPos, hsplit, henvSlice, hcodeSlice, htailSlice⟩,
    by simpa using ((henvSpan.append hcodeSpan).append htailSpan).suffix,
    hb.1, henv, ⟨finalDecls, hready⟩, hbounds, hprofile, hcode, htyped, hcount,
    htail, hmatches, hmeta⟩

end Itasca.StreamCompleteRegions
