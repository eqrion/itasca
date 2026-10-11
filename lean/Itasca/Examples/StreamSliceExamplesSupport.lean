import Itasca.Stream.StreamSliceCompleteness
import Itasca.Module.ModuleValidation

open Aeneas Aeneas.Std

namespace Itasca.StreamSliceExamplesSupport

open ModuleBinary ModuleElaboration ModuleEnv StreamCompleteRegions

private theorem slice_spec (data : Slice U8) (first last : Usize)
    (hfirst : first.val ≤ last.val) (hlast : last.val ≤ data.length) :
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      data ⟨first, last⟩ ⦃ region => Wasm.BytesAt data first region.val last ⦄ := by
  step
  apply Wasm.BytesAt.of_slice_view hfirst hlast
  assumption

/-- Component-based regression certificates use the canonical independent
layout, declaration requirements, typed entries, and valid data segments. -/
theorem prepared_layout (data : Slice U8) (raw : ModuleBinary.Module)
    (decls : Declarations) (codePos tailPos : Usize)
    (hl : ModuleLayout.Layout data raw decls codePos tailPos)
    (hsize : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (hrequirements : Requirements raw) (tail : module.Tail)
    (hrawTail : tail.data.val.map ModuleData.raw = raw.data)
    (htypedReady : ∀ decls env, Ready raw 9 decls env →
      List.Forall₂ (CodeEntry.Typed env) env.func_type_indices.val raw.codes)
    (htailReady : ∀ decls env, Ready raw 9 decls env →
      ∀ segment ∈ tail.data.val, ModuleData.Valid env segment) :
    ∃ regions env, Certificate data raw regions env tail := by
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
    environment raw decls (Slice.len environment) henvEnc hl.raw_eq (.inl rfl) hrequirements
  have henvSize : environment.length ≤ limits.MAX_MODULE_BYTES.val := by
    have := henvSpan.length
    have := hsize
    have := hl.environment.span.2
    simp only [Slice.length] at *
    omega
  have hbounds := (ModuleEnv.accepted_entry_conditions environment env
    (Slice.len environment) henvSize henv).1
  have harity : ∀ ft ∈ env.types.val, ft.results.val.length ≤ 1 := by
    exact (ModuleEnv.accepted_entry_conditions environment env (Slice.len environment) henvSize henv).2
  have hprofile : Wasm1.Environment env :=
    ⟨hready.represents.cache.func_arity harity, harity⟩
  have htypes := htypedReady finalDecls env hready
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
  have htail := module.validate_tail.complete tail (by simpa [hrawTail] using htailEnc)
    (htailReady finalDecls env hready)
  have hmatches := hready.matches tail hrawTail
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
  refine ⟨⟨environment, code, tailBytes⟩, env, ?_⟩
  exact ⟨⟨codePos, tailPos, hsplit, henvSlice, hcodeSlice, htailSlice⟩,
    by simpa using ((henvSpan.append hcodeSpan).append htailSpan).suffix,
    hsize, henv, ⟨finalDecls, hready⟩, hbounds, hprofile, hcode, htyped, hcount,
    htail, hmatches, hmeta⟩


/-- Execute the concrete adapter from its component certificate, preserving the
exact supplied tail and the decoded environment. -/
theorem accepted_certificate (data : Slice U8) (raw : ModuleBinary.Module)
    (regions : stream.SliceSource) (env : module.Env) (tail : module.Tail)
    (hc : Certificate data raw regions env tail) :
    module.validate_module data = .ok (.Ok ⟨env, tail⟩) := by
  obtain ⟨first, last, hsplit, he, hcode, ht⟩ := hc.split
  obtain ⟨storage, hstorage, _⟩ := WP.spec_imp_exists module.Env.new.spec
  obtain ⟨after, run, hrun, htail, _⟩ := complete_certificate
    stream.SliceSource.Insts.ItascaStreamSource stream.SyncVisitor.Insts.ItascaStreamStreamingVisitor
    { batch_bytes := 25000#usize, max_batches := 1#usize } StreamSync.Queued StreamSync.accepts
    0#u64 regions data raw regions env tail hc (stream.SliceSource.available regions)
    ⟨none, none⟩ storage rfl
  have hstored := StreamSync.delivered_tail run.remaining
  rw [htail] at hstored
  change stream.validate_module_slice data = _
  unfold stream.validate_module_slice
  simp only [hsplit, bind_ok, Std.uncurry, he, hcode, ht, hstorage]
  cases regions
  simp [core.result.Result.Insts.CoreOpsTry.branch, hrun, hstored]

/-- Existing public module examples run through the streaming implementation;
component typing and encoding replace the removed code-section driver proof. -/
theorem accepted_layout (data : Slice U8) (raw : ModuleBinary.Module)
    (decls : Declarations) (codePos tailPos : Usize)
    (hl : ModuleLayout.Layout data raw decls codePos tailPos)
    (hsize : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (hrequirements : Requirements raw) (tail : module.Tail)
    (hrawTail : tail.data.val.map ModuleData.raw = raw.data)
    (htypedReady : ∀ decls env, Ready raw 9 decls env →
      List.Forall₂ (CodeEntry.Typed env) env.func_type_indices.val raw.codes)
    (htailReady : ∀ decls env, Ready raw 9 decls env →
      ∀ segment ∈ tail.data.val, ModuleData.Valid env segment) :
    ∃ env, module.validate_module data = .ok (.Ok ⟨env, tail⟩) := by
  obtain ⟨regions, env, hc⟩ := prepared_layout data raw decls codePos tailPos hl hsize
    hrequirements tail hrawTail htypedReady htailReady
  exact ⟨env, accepted_certificate data raw regions env tail hc⟩



/-- An environment consuming the whole input with no defined functions takes
the actual empty-code and empty-tail paths of the streaming wrapper. -/
theorem accepted_at_end (data : Slice U8) (env : module.Env)
    (hsize : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (hfuncs : env.func_type_indices.val = [])
    (henv : module.validate_env data = .ok (.Ok (env, Slice.len data))) :
    module.validate_module data = .ok (.Ok ⟨env, ⟨alloc.vec.Vec.new _⟩⟩) := by
  have hsemantic := module.validate_env.semantic_spec data
  rw [henv] at hsemantic
  simp only [WP.spec_ok] at hsemantic
  obtain ⟨decls, hrep, hv, _, _, hprefix⟩ := hsemantic
  have hsplit : stream.find_code_region data = .ok (Slice.len data, Slice.len data) := by
    unfold stream.find_code_region
    rw [split_skip_prefix hprefix, split_loop_eof]
  obtain ⟨environment, he, heSpan⟩ := WP.spec_imp_exists
    (slice_spec data 0#usize (Slice.len data) (by simp) (by simp))
  have heq : environment = data := by
    apply Slice.ext
    simpa using heSpan.suffix.symm
  subst environment
  let empty : Slice U8 := alloc.vec.Vec.deref (alloc.vec.Vec.new _)
  obtain ⟨emptyBytes, hempty, hemptySpan⟩ := WP.spec_imp_exists
    (slice_spec data (Slice.len data) (Slice.len data) (by omega) (by simp))
  have hnil : emptyBytes.val = [] := by
    apply List.eq_nil_of_length_eq_zero
    have := hemptySpan.length
    omega
  have hemptyEq : emptyBytes = empty := Slice.ext _ _ (by simpa [empty, alloc.vec.Vec.deref] using hnil)
  subst emptyBytes
  let raw := decls.module [] []
  let tail : module.Tail := ⟨alloc.vec.Vec.new _⟩
  have hready : Ready raw 9 decls env :=
    ⟨hrep, by simp [Phase], by intro; rfl, by intro; rfl, by intro; rfl,
      by intro; rfl, by intro; rfl, by intro; rfl, by intro; rfl,
      by intro; rfl, by intro; rfl⟩
  have htail : module.validate_tail empty 0#usize env = .ok (.Ok tail) := by
    have hr := ModuleTail.loop_eof empty env (alloc.vec.Vec.new _) false
    have hz : Slice.len empty = 0#usize := rfl
    rw [hz] at hr
    simp [module.validate_tail, module.validate_tail_with, hr, tail]
  have hm := hready.matches tail (by simp [tail, raw, Declarations.module])
  have hn : ∀ entry ∈ env.exports.val, wf_name (ModuleBinary.nameOfBytes entry.name.val) := by
    intro entry hentry
    obtain ⟨_, hp, _⟩ := hprefix
    exact hp.export_names_wf (ModuleEnv.rawExport entry)
      (by rw [hrep.exports]; exact List.mem_map.mpr ⟨entry, hentry, rfl⟩)
  have hmeta := accessorTypes hm.2 hv hn (codes := raw.codes) (segments := tail.data.val)
  rw [← hm.1] at hmeta
  have hc : Certificate data raw ⟨data, empty, empty⟩ env tail := by
    refine ⟨⟨Slice.len data, Slice.len data, hsplit, he, hempty, hempty⟩,
      by simp [empty, alloc.vec.Vec.deref], hsize, henv, ⟨decls, hready⟩,
      (ModuleEnv.accepted_entry_conditions data env (Slice.len data) hsize henv).1,
      ⟨hrep.cache.func_arity hv.types, hv.types⟩,
      ⟨0#usize, .inl ⟨rfl, rfl, hfuncs⟩, [], Rep.nil, ?_⟩,
      .nil _, by simp [raw, Declarations.module, hfuncs], htail, hm, hmeta⟩
    constructor <;> simp [empty, alloc.vec.Vec.deref]
  exact accepted_certificate data raw ⟨data, empty, empty⟩ env tail hc

end Itasca.StreamSliceExamplesSupport
