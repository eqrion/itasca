import Itasca.Main

/-!
Proofs for Examples / Module.

This module collects SliceLayout, Support.
Each section documents its contracts and consumers.
-/

/-! ## SliceLayout -/

section

/-!
# Layout facts for contiguous module examples

Wasm 2.0 lemmas that turn an independently described module layout into acceptance by
`metadata.validate_module`. `Examples.Stream.SliceSupport.prepared_layout` builds a
`Stream.CompleteRegions.Certificate` from a layout, `accepted_certificate` and `accepted_layout`
run the contiguous adapter from it, and `accepted_at_end` handles a module whose environment
consumes the whole input. The module examples use these.
-/

open Aeneas Aeneas.Std

namespace Itasca.Examples.Stream.SliceSupport

open Binary Module.Elaboration Module.Environment Stream.CompleteRegions

private theorem slice_spec (data : Slice U8) (first last : Usize)
    (hfirst : first.val ≤ last.val) (hlast : last.val ≤ data.length) :
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      data ⟨first, last⟩ ⦃ region => Body.Scalar.BytesAt data first region.val last ⦄ := by
  step
  apply Body.Scalar.BytesAt.of_slice_view hfirst hlast
  assumption

/-- Builds a Wasm 2.0 region certificate from the canonical layout, the declaration requirements,
the typed code entries and the valid data segments. -/
theorem prepared_layout (data : Slice U8) (raw : Binary.Module)
    (decls : Declarations) (codePos tailPos : Usize)
    (hl : Module.Layout data raw decls codePos tailPos )
    (hsize : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (hrequirements : Requirements raw ) (hrawCount : raw.dataCount = none) (tail : metadata.Tail)
    (hrawTail : tail.data.val.map Module.Data.raw = raw.data)
    (htypedReady : ∀ decls env, Ready raw 10 decls env →
      List.Forall₂ (fun idx entry => CodeEntry.Typed env idx entry ) env.func_type_indices.val raw.codes)
    (htailReady : ∀ decls env, Ready raw 10 decls env →
      ∀ segment ∈ tail.data.val, Module.Data.Valid env segment) :
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
  obtain ⟨env, finalDecls, henv, hready⟩ := metadata.validate_env.complete
    environment raw decls (Slice.len environment) henvEnc hl.raw_eq (.inl rfl) hrequirements
  have henvSize : environment.length ≤ limits.MAX_MODULE_BYTES.val := by
    have := henvSpan.length
    have := hsize
    have := hl.environment.span.2
    simp only [Slice.length] at *
    omega
  obtain ⟨hbounds, hlimits⟩ := Module.Environment.accepted_entry_conditions
    environment env (Slice.len environment) henvSize henv
  have htypes := htypedReady finalDecls env hready
  have hcount : raw.codes.length = env.func_type_indices.val.length := htypes.length_eq.symm
  have hcode : ∃ entries, Stream.Framing.HeaderAt code env entries ∧
      At (Rep (Itasca.CodeEntry.CodeEncodingWithinLimits )) code entries raw.codes (Slice.len code) := by
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
      · simpa [hempty] using (Rep.nil : Rep (Itasca.CodeEntry.CodeEncodingWithinLimits ) [] [])
      · exact ⟨by simp [hzero], by simp [hzero], by simp⟩
  have htyped : Module.Code.EntriesTyped env 0 raw.codes := by
    obtain ⟨_, _, bytes, henc, _⟩ := hcode
    apply Module.Code.EntriesTyped.of_forall₂ (by simpa using htypes)
    exact Binary.Rep.locals_within_limits henc
  have htailEnc := hl.tail.on_region htailSpan
  have htail := metadata.validate_tail.complete tail (by simpa [hrawTail] using htailEnc)
    (htailReady finalDecls env hready)
    (by simp [hready.data_count_eq (by decide), hrawCount])
  have hmatches := hready.matches tail hrawTail
  have hsemantic := metadata.validate_env.semantic_spec environment
  rw [henv] at hsemantic
  simp only [WP.spec_ok] at hsemantic
  obtain ⟨_, hrep, hv, _, _, hprefix⟩ := hsemantic
  obtain ⟨bytes, hprefix, _⟩ := hprefix
  have hnames : ∀ entry ∈ env.exports.val, wf_name (Binary.nameOfBytes entry.name.val) := by
    intro entry hentry
    exact hprefix.export_names_wf (Module.Environment.rawExport entry)
      (by rw [hrep.exports]; exact List.mem_map.mpr ⟨entry, hentry, rfl⟩)
  have hmeta := accessor_types hmatches.2 hv hnames (codes := raw.codes) (segments := tail.data.val)
  rw [← hmatches.1] at hmeta
  refine ⟨⟨environment, code, tailBytes⟩, env, ?_⟩
  exact ⟨⟨codePos, tailPos, hsplit, henvSlice, hcodeSlice, htailSlice⟩,
    ⟨codePos, tailPos, hl.canonical, span_slice henvSpan, span_slice hcodeSpan, span_slice htailSpan⟩,
    by simpa using ((henvSpan.append hcodeSpan).append htailSpan).suffix,
    hsize, henv, ⟨finalDecls, hready⟩, hbounds, hlimits, hcode, htyped, hcount,
    htail, hmatches, hmeta⟩

/-- `metadata.validate_module` accepts a region certificate and returns its environment and
tail. -/
theorem accepted_certificate (data : Slice U8) (raw : Binary.Module)
    (regions : stream.SliceSource) (env : metadata.Env) (tail : metadata.Tail)
    (hc : Certificate data raw regions env tail ) :
    metadata.validate_module data = .ok (.Ok ⟨env, tail⟩) := by
  obtain ⟨first, last, hsplit, he, hcode, ht⟩ := hc.split
  obtain ⟨storage, hstorage, _⟩ := WP.spec_imp_exists metadata.Env.new.spec
  obtain ⟨after, run, hrun, htail, _⟩ := complete_certificate
    stream.SliceSource.Insts.ItascaStreamSource stream.SyncVisitor.Insts.ItascaStreamStreamingVisitor
    { batch_bytes := 25000#usize, max_batches := 1#usize } Stream.Sync.Queued Stream.Sync.accepts
    0#u64 regions data raw regions env tail hc (stream.SliceSource.available regions)
    ⟨none, none⟩ storage rfl
  have hstored := Stream.Sync.delivered_tail run.remaining
  rw [htail] at hstored
  change stream.validate_module_slice data = _
  unfold stream.validate_module_slice
  simp only [hsplit, bind_ok, Std.uncurry, he, hcode, ht, hstorage]
  cases regions
  simp [core.result.Result.Insts.CoreOpsTry.branch, hrun, hstored]

/-- A module with a canonical layout, typed code entries and valid data segments is accepted by
`metadata.validate_module`, which runs through the streaming implementation. -/
theorem accepted_layout (data : Slice U8) (raw : Binary.Module)
    (decls : Declarations) (codePos tailPos : Usize)
    (hl : Module.Layout data raw decls codePos tailPos )
    (hsize : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (hrequirements : Requirements raw ) (hrawCount : raw.dataCount = none) (tail : metadata.Tail)
    (hrawTail : tail.data.val.map Module.Data.raw = raw.data)
    (htypedReady : ∀ decls env, Ready raw 10 decls env →
      List.Forall₂ (fun idx entry => CodeEntry.Typed env idx entry ) env.func_type_indices.val raw.codes)
    (htailReady : ∀ decls env, Ready raw 10 decls env →
      ∀ segment ∈ tail.data.val, Module.Data.Valid env segment) :
    ∃ env, metadata.validate_module data = .ok (.Ok ⟨env, tail⟩) := by
  obtain ⟨regions, env, hc⟩ := prepared_layout data raw decls codePos tailPos hl hsize
    hrequirements hrawCount tail hrawTail htypedReady htailReady
  exact ⟨env, accepted_certificate data raw regions env tail hc⟩

/-- An environment that consumes the whole input and defines no functions takes the empty-code and
empty-tail paths of the streaming adapter, and the module is accepted. -/
theorem accepted_at_end (data : Slice U8) (env : metadata.Env)
    (hsize : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (hfuncs : env.func_type_indices.val = [])
    (hdataCount : env.data_count = none)
    (henv : metadata.validate_env data = .ok (.Ok (env, Slice.len data))) :
    metadata.validate_module data = .ok (.Ok ⟨env, ⟨alloc.vec.Vec.new _⟩⟩) := by
  have hsemantic := metadata.validate_env.semantic_spec data
  rw [henv] at hsemantic
  simp only [WP.spec_ok] at hsemantic
  obtain ⟨decls, hrep, hv, _, _, hprefix⟩ := hsemantic
  have hsplit : stream.find_code_region data = .ok (Slice.len data, Slice.len data) := by
    unfold stream.find_code_region
    rw [Stream.Split.skip_prefix hprefix, Stream.Split.loop_eof]
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
  let tail : metadata.Tail := ⟨alloc.vec.Vec.new _⟩
  have hready : Ready raw 10 decls env :=
    ⟨hrep, by simp [Phase], by intro; rfl, by intro; rfl, by intro; rfl,
      by intro; rfl, by intro; rfl, by intro; rfl, by intro; rfl,
      by intro; rfl, by intro; rfl, by intro; rfl⟩
  have htail : metadata.validate_tail empty 0#usize env = .ok (.Ok tail) := by
    have hr := Module.Tail.loop_eof empty env (alloc.vec.Vec.new _) false (by simp [hdataCount])
    have hz : Slice.len empty = 0#usize := rfl
    rw [hz] at hr
    simp [metadata.validate_tail, metadata.validate_tail_with, hr, tail]
  have hm := hready.matches tail (by simp [tail, raw, Declarations.module])
  have hn : ∀ entry ∈ env.exports.val, wf_name (Binary.nameOfBytes entry.name.val) := by
    intro entry hentry
    obtain ⟨_, hp, _⟩ := hprefix
    exact hp.export_names_wf (Module.Environment.rawExport entry)
      (by rw [hrep.exports]; exact List.mem_map.mpr ⟨entry, hentry, rfl⟩)
  have hmeta := accessor_types hm.2 hv hn (codes := raw.codes) (segments := tail.data.val)
  rw [← hm.1] at hmeta
  have hc : Certificate data raw ⟨data, empty, empty⟩ env tail := by
    refine ⟨⟨Slice.len data, Slice.len data, hsplit, he, hempty, hempty⟩,
      ⟨Slice.len data, Slice.len data,
        ⟨Stream.Split.canonical_prefix hprefix, .inr ⟨rfl, .inl rfl⟩⟩,
        span_slice heSpan, span_slice hemptySpan, span_slice hemptySpan⟩,
      by simp [empty, alloc.vec.Vec.deref], hsize, henv, ⟨decls, hready⟩,
      (Module.Environment.accepted_entry_conditions data env (Slice.len data) hsize henv).1,
      hv.environment_within_limits hrep.cache,
      ⟨0#usize, .inl ⟨rfl, rfl, hfuncs⟩, [], Rep.nil, ?_⟩,
      .nil _, by simp [raw, Declarations.module, hfuncs], htail, hm, hmeta⟩
    constructor <;> simp [empty, alloc.vec.Vec.deref]
  exact accepted_certificate data raw ⟨data, empty, empty⟩ env tail hc

end Itasca.Examples.Stream.SliceSupport

end

/-! ## Support -/

section

/-!
# Shared helpers for module examples

Helpers for writing whole-module byte fixtures: `bytes` builds a slice literal, and `leb`, `one`,
`padded` and `omitted` build the `Binary` encoding derivations for one-byte LEB128 values,
one-element vectors, present sections and omitted sections.
-/

open Aeneas Aeneas.Std

namespace Itasca.Examples.Module.Support

open Binary

/-- A bounded slice literal. Fixtures are checked by the kernel, with no external evaluator. -/
def bytes (xs : List U8) (h : xs.length ≤ Usize.max := by scalar_tac) : Slice U8 :=
  alloc.vec.Vec.deref (alloc.vec.Vec.from xs h)

/-- A byte below 128 is its own one-byte unsigned LEB128 encoding. -/
theorem leb (b : U8) (h : b.val < 128 := by decide) : Binary.Leb128.Encoding [b] b.val :=
  ⟨[], b, rfl, by simp, by simp, h, by simp, by simp [Binary.Leb128.payload, Nat.mod_eq_of_lt h]⟩

/-- A one-element vector is the count byte 1 followed by its element. -/
theorem one {α : Type} {R : α → List U8 → Prop} {x bs}
    (h : R x bs) : VecEncoding R [x] (1#u8 :: bs) :=
  ⟨[1#u8], bs, leb 1#u8, by simpa using Rep.cons h Rep.nil, rfl⟩

/-- A present section with a one-byte size and no leading custom sections. -/
theorem padded {α : Type} {R : α → List U8 → Prop} (id size : U8)
    (absent : α) {x bs} (h : R x bs) (hlen : bs.length = size.val)
    (hsize : size.val < 128 := by decide) :
    PaddedEncoding id R absent x (id :: size :: bs) :=
  ⟨[], _, .nil, .present ⟨[size], bs, hlen ▸ leb size hsize, h, rfl⟩, rfl⟩

/-- An omitted section with no surrounding custom sections. -/
theorem omitted {α : Type} (id : U8) (R : α → List U8 → Prop) (absent : α) :
    PaddedEncoding id R absent absent [] := ⟨[], [], .nil, .absent, rfl⟩

end Itasca.Examples.Module.Support

end
