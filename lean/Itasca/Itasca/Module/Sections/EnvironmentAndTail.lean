import Itasca.Module.Env.Declarations
import Itasca.Module.Sections.Headers
import Itasca.Module.Readers.Completeness
import Itasca.Module.Elab.SegmentTyping
import Itasca.Module.Readers.Syntax
import Itasca.Module.Const.Parser
import Itasca.Stream.Definitions
import Itasca.Results.Definitions.Streaming

/-!
Proofs for Module / Sections.

This module collects Payloads, EnvironmentAndTail.
Each section documents its contracts and consumers.
-/

/-! ## Payloads -/

section

/-!
# Section payload contracts

Export/start, memory/table and data-section readers establish ordered environment effects
and independent payload spans. Name freshness, index bounds and segment encodings remain
explicit in their operation contracts.
-/

/-! ## Export -/

section

/-!
# Export and start section parsers

Soundness of `metadata.decode_export_section` and `metadata.decode_start_section`. `ExportsAdded` says
the environment gains the exports in order, each with a fresh name, an in-range index and the
function references it declares. The decoded span is a `VecEncoding ExportEncoding`. An accepted
start section names a function without parameters or results. Completeness is in
`Module/Sections/DeclarationsComplete`.
-/

open Aeneas Aeneas.Std

namespace Itasca

private theorem names_equal_loop_spec (a b : Slice U8) (i : Usize)
    (hlen : a.length = b.length) (hi : i.val ≤ a.length)
    (hprefix : a.val.take i.val = b.val.take i.val) :
    metadata.names_equal_loop a b i ⦃ result => result = true ↔ a.val = b.val ⦄ := by
  unfold metadata.names_equal_loop
  apply loop.spec_decr_nat (fun pos => a.length - pos.val)
    (fun pos => pos.val ≤ a.length ∧ a.val.take pos.val = b.val.take pos.val)
  · intro pos hp
    obtain ⟨hpos, heq⟩ := hp
    unfold metadata.names_equal_loop.body
    step*
    · have hend : pos.val = a.length := by scalar_tac
      have he : a.val = b.val := by
        rw [hend, List.take_length, hlen, List.take_length] at heq
        exact heq
      simp [he]
    · refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      have ha : pos.val < a.val.length := by scalar_tac
      have hb : pos.val < b.val.length := by scalar_tac
      have hbyte : a.val[pos.val] = b.val[pos.val] := by
        apply UScalar.eq_of_val_eq
        simpa [i2_post, i3_post] using ‹¬(i2 != i3) = true›
      rw [i4_post, List.take_succ_eq_append_getElem ha, List.take_succ_eq_append_getElem hb, heq, hbyte]
  · exact ⟨hi, hprefix⟩

/-- `metadata.names_equal` returns normally and decides equality of the byte lists. -/
@[step]
theorem metadata.names_equal.spec (a b : Slice U8) :
    metadata.names_equal a b ⦃ result => result = true ↔ a.val = b.val ⦄ := by
  unfold metadata.names_equal
  dsimp only
  split
  · rename_i hne
    simp only [WP.spec_ok, Bool.false_eq_true, false_iff]
    intro heq
    have hlen : a.length = b.length := congrArg List.length heq
    simp [hlen] at hne
  · rename_i heq
    exact names_equal_loop_spec a b 0#usize (by scalar_tac) (by simp) (by simp)

/-- `metadata.export_name_taken` decides whether the name is already exported. -/
@[step]
theorem metadata.export_name_taken.spec (env : metadata.Env) (nm : Slice U8) :
    metadata.export_name_taken env nm ⦃ result =>
      result = true ↔ nm.val ∈ env.exports.val.map (fun entry => entry.name.val) ⦄ := by
  unfold metadata.export_name_taken metadata.export_name_taken_loop
  apply loop.spec_decr_nat (fun pos => env.exports.val.length - pos.val)
    (fun pos => pos.val ≤ env.exports.val.length ∧
      ∀ j (hj : j < env.exports.val.length), j < pos.val → env.exports.val[j].name.val ≠ nm.val)
  · intro pos hp
    obtain ⟨hpos, hprefix⟩ := hp
    unfold metadata.export_name_taken_loop.body
    step*
    · simp only [Bool.false_eq_true, false_iff]
      intro hm
      obtain ⟨entry, hm, hname⟩ := List.mem_map.mp hm
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hm
      exact hprefix j hj (by scalar_tac) hname
    · have hname : e.name.val = nm.val := by
        simpa [alloc.vec.Vec.deref] using b_post.mp ‹b = true›
      simp only [true_iff]
      exact List.mem_map.mpr ⟨e, by rw [e_post]; exact List.getElem_mem _, hname⟩
    · refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      intro j hj hlt
      by_cases hbefore : j < pos.val
      · exact hprefix j hj hbefore
      · have heq : j = pos.val := by scalar_tac
        intro hname
        apply ‹¬b = true›
        apply b_post.mpr
        simpa [alloc.vec.Vec.deref, e_post, heq] using hname
  · exact ⟨by simp, by simp⟩

end Itasca

namespace Itasca.Module.Sections

/-- `result` is `env` with `entry` appended to the exports, under a fresh name with a resolvable
descriptor, and its function references appended to the declared functions. Nothing else
changes. -/
def ExportAdded (env result : metadata.Env) (entry : metadata.Export) : Prop :=
  result = { env with exports := result.exports, declared_funcs := result.declared_funcs } ∧
  result.exports.val = env.exports.val ++ [entry] ∧
  entry.name.val ∉ env.exports.val.map (fun e => e.name.val) ∧
  (∃ xt, Module.Externals.ExportResolves env entry xt) ∧
  result.declared_funcs.val = env.declared_funcs.val ++ Module.References.exportIndices entry

/-- `result` is `initial` after adding `entries` one at a time by `ExportAdded`. -/
inductive ExportsAdded (initial : metadata.Env) : List metadata.Export → metadata.Env → Prop where
  | nil : ExportsAdded initial [] initial
  | snoc {entries before after entry} : ExportsAdded initial entries before →
      ExportAdded before after entry → ExportsAdded initial (entries ++ [entry]) after

/-- The result's exports are the initial exports followed by the added entries. -/
theorem ExportsAdded.exports {env entries result} (h : ExportsAdded env entries result) :
    result.exports.val = env.exports.val ++ entries := by
  induction h with
  | nil => simp
  | snoc _ ha ih => simpa [ih, List.append_assoc] using ha.2.1

/-- Adding exports changes only the exports and the declared functions. -/
theorem ExportsAdded.unchanged {env entries result} (h : ExportsAdded env entries result) :
    result = { env with exports := result.exports, declared_funcs := result.declared_funcs } := by
  induction h with
  | nil => cases env; rfl
  | snoc _ ha ih => rw [ha.1, ih]

/-- The binary kind byte of an export descriptor. -/
def descByte : metadata.ExportDesc → U8
  | .Func _ => 0#u8 | .Table _ => 1#u8 | .Memory _ => 2#u8 | .Global _ => 3#u8

/-- The index of an export descriptor. -/
def descIndex : metadata.ExportDesc → U32
  | .Func idx | .Table idx | .Memory idx | .Global idx => idx

/-- The descriptor's index is in range for its index space. -/
def ExportDescValid (env : metadata.Env) : metadata.ExportDesc → Prop
  | .Func idx => idx.val < env.func_types.val.length
  | .Table idx => idx.val < env.table_types.val.length
  | .Memory idx => idx.val < env.mem_types.val.length
  | .Global idx => idx.val < env.global_types.val.length

/-- A valid descriptor has an external type. -/
theorem ExportDescValid.resolves {env desc} (h : ExportDescValid env desc) (nm : alloc.vec.Vec U8) :
    ∃ xt, Module.Externals.ExportResolves env ⟨nm, desc⟩ xt := by
  cases desc with
  | Func idx => exact ⟨.Func env.func_types.val[idx.val], h, rfl⟩
  | Table idx => exact ⟨.Table env.table_types.val[idx.val], h, rfl⟩
  | Memory idx => exact ⟨.Memory env.mem_types.val[idx.val], h, rfl⟩
  | Global idx => exact ⟨.Global env.global_types.val[idx.val], h, rfl⟩

/-- A kind byte followed by the index encoding is an `ExportDescEncoding`. -/
theorem export_desc_encoded (desc : metadata.ExportDesc) {bytes}
    (h : Binary.IndexEncoding (descIndex desc) bytes) :
    Binary.ExportDescEncoding desc (descByte desc :: bytes) := by
  cases desc with
  | Func idx => exact .func idx.val ((Binary.Leb128.encoding_iff _ _).mp h)
  | Table idx => exact .table idx.val ((Binary.Leb128.encoding_iff _ _).mp h)
  | Memory idx => exact .memory idx.val ((Binary.Leb128.encoding_iff _ _).mp h)
  | Global idx => exact .global idx.val ((Binary.Leb128.encoding_iff _ _).mp h)

/-- A name, a kind byte and an index in sequence form an `ExportEncoding`. -/
theorem export_encoded {data start p1 p2 next nm kind idx desc}
    (hn : Binary.At Binary.NameEncoding data start nm p1)
    (hk : Binary.At Binary.ByteEncoding data p1 kind p2)
    (hd : Binary.Leb128.Decoded data p2 idx next)
    (hkind : kind = descByte desc) (hindex : idx = descIndex desc) :
    Binary.At Binary.ExportEncoding data start ⟨nm, desc⟩ next := by
  obtain ⟨nameBytes, hname, hs⟩ := hn
  obtain ⟨indexBytes, hs', hl', hb', hidx⟩ := hd
  have he : Binary.ExportDescEncoding desc (kind :: indexBytes) := by
    rw [hkind]
    exact export_desc_encoded desc (by simpa [Binary.IndexEncoding, hindex] using hidx)
  exact ⟨nameBytes ++ (kind :: indexBytes),
    Binary.ExportEncoding.reader_parts.mpr ⟨nameBytes, kind :: indexBytes, hname, he, rfl⟩,
    hs.append (by simpa using (Binary.At.byte hk).append ⟨hs', hl', hb'⟩)⟩

end Itasca.Module.Sections

namespace Itasca

open Module.Sections

/-- `metadata.export_desc` returns the descriptor for a kind byte and index, which is in range. -/
@[step]
theorem metadata.export_desc.spec (env : metadata.Env) (kind : U8) (idx : U32) :
    metadata.export_desc env kind idx ⦃ r => match r with
      | .Ok desc => kind = descByte desc ∧ idx = descIndex desc ∧ ExportDescValid env desc
      | .Err _ => True ⦄ := by
  unfold metadata.export_desc
  step
  split <;> step* <;> simp_all [descByte, descIndex, ExportDescValid]
  all_goals with_unfolding_all rfl

/-- An accepted `metadata.decode_start_section` reads a `StartEncoding` span and records an in-range
function without parameters or results as the start. -/
@[step]
theorem metadata.decode_start_section.spec (data : Slice U8) (start : Usize) (env : metadata.Env) :
    metadata.decode_start_section data start env ⦃ r => match r.1 with
      | .Ok next => ∃ idx, Binary.At Binary.StartEncoding data start (some idx) next ∧
          r.2 = { env with start := some idx } ∧
          ∃ hi : idx.val < env.func_types.val.length,
            env.func_types.val[idx.val].params.val = [] ∧ env.func_types.val[idx.val].results.val = []
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hd⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data start)
  cases r with
  | Err e =>
      simp [metadata.decode_start_section, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
      obtain ⟨idx, next⟩ := pair
      simp [metadata.decode_start_section, hr, core.result.Result.Insts.CoreOpsTry.branch]
      step*
      simp [alloc.vec.Vec.is_empty]
      split_ifs <;> simp
      have hidx : i.val = idx.val := by scalar_tac
      have hbound : idx.val < env.func_types.val.length := by scalar_tac
      obtain ⟨bytes, hs, hl, hb, he⟩ := hd
      refine ⟨⟨bytes, ⟨idx, rfl, he⟩, hs, hl, hb⟩, hbound, ?_, ?_⟩
      all_goals simp_all

end Itasca

namespace Itasca

open Binary Module.Sections

attribute [local simp] core.result.Result.Insts.CoreOpsTry.branch
  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
  error.Error.Insts.CoreConvertFromOpError.from

private theorem export_step (data : Slice U8) (count : U32) (env : metadata.Env)
    (pos : Usize) (i : U32) (hi : i.val < count.val) (hbound : Module.Environment.Bounded env pos.val) :
    metadata.decode_export_section_loop.body data count env pos i ⦃ r => match r with
      | .done (.Err _, _) => True
      | .done (.Ok _, _) => False
      | .cont (result, next, j) => ∃ entry, ExportAdded env result entry ∧
          At ExportEncoding data pos (Module.Environment.rawExport entry) next ∧
          Module.Environment.Bounded result next.val ∧ j.val = i.val + 1 ⦄ := by
  have hmore : ¬i ≥ count := by scalar_tac
  obtain ⟨r, hn, hname⟩ := WP.spec_imp_exists (metadata.decode_name.spec data pos)
  cases r with
  | Err e => simp [metadata.decode_export_section_loop.body, hmore, hn]
  | Ok pair =>
      obtain ⟨nm, p1⟩ := pair
      obtain ⟨taken, ht, htaken⟩ := WP.spec_imp_exists
        (metadata.export_name_taken.spec env (alloc.vec.Vec.deref nm))
      cases taken with
      | true => simp [metadata.decode_export_section_loop.body, hmore, hn, ht]
      | false =>
          have hfresh : nm.val ∉ env.exports.val.map (fun entry => entry.name.val) := by
            simpa [alloc.vec.Vec.deref] using htaken
          obtain ⟨r, hk, hkind⟩ := WP.spec_imp_exists (reader.read_byte.module_spec data p1)
          cases r with
          | Err e => simp [metadata.decode_export_section_loop.body, hmore, hn, ht, hk]
          | Ok pair =>
              obtain ⟨kind, p2⟩ := pair
              obtain ⟨r, hu, hindex⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data p2)
              cases r with
              | Err e => simp [metadata.decode_export_section_loop.body, hmore, hn, ht, hk, hu]
              | Ok pair =>
                  obtain ⟨idx, next⟩ := pair
                  obtain ⟨r, hd, hdesc⟩ := WP.spec_imp_exists (metadata.export_desc.spec env kind idx)
                  cases r with
                  | Err e => simp [metadata.decode_export_section_loop.body, hmore, hn, ht, hk, hu, hd]
                  | Ok desc =>
                      obtain ⟨hbyte, hidx, hvalid⟩ := hdesc
                      have he := export_encoded hname hkind hindex hbyte hidx
                      have hs := hname.span
                      have hs' := hkind.span
                      have hs'' := hindex.span
                      have hprogress : pos.val < next.val := by omega
                      have hsize := hbound.exports
                      have hcapacity : env.exports.val.length < Usize.max := by scalar_tac
                      have hsizeRefs := hbound.declaredFuncs
                      have hcapacityRefs : env.declared_funcs.val.length < Usize.max := by scalar_tac
                      simp [metadata.decode_export_section_loop.body, hmore, hn, ht, hk, hu, hd]
                      cases desc <;> step*
                      all_goals
                        refine ⟨⟨nm, _⟩, ⟨rfl, ?_, hfresh, hvalid.resolves nm, ?_⟩, he, ?_, ?_⟩
                        · first | exact v1_post | exact v_post
                        · simp_all only [Module.References.exportIndices, List.append_nil]
                        · cases hbound
                          constructor <;>
                            simp_all only [List.length_append, List.length_singleton] <;> omega
                        · scalar_tac

/-- The export loop adds `count` exports forming a `Rep ExportEncoding` span, each with a fresh
name and valid descriptor. -/
theorem metadata.decode_export_section_loop.spec (data : Slice U8) (env : metadata.Env)
    (count : U32) (start : Usize) (hstart : start.val ≤ data.length)
    (hbound : Module.Environment.Bounded env start.val) :
    metadata.decode_export_section_loop data env count start 0#u32 ⦃ r => match r.1 with
      | .Ok next => ∃ entries, entries.length = count.val ∧ ExportsAdded env entries r.2 ∧
          At (Rep ExportEncoding) data start (entries.map Module.Environment.rawExport) next ∧
          Module.Environment.Bounded r.2 next.val
      | .Err _ => True ⦄ := by
  unfold metadata.decode_export_section_loop
  apply loop.spec_decr_nat (fun s => count.val - s.2.2.val)
    (fun s => s.2.2.val ≤ count.val ∧ ∃ entries, entries.length = s.2.2.val ∧
      ExportsAdded env entries s.1 ∧
      At (Rep ExportEncoding) data start (entries.map Module.Environment.rawExport) s.2.1 ∧
      Module.Environment.Bounded s.1 s.2.1.val)
  · rintro ⟨current, pos, i⟩ ⟨hi, entries, hlen, hhistory, hbytes, hbound⟩
    dsimp only at *
    by_cases hdone : count.val ≤ i.val
    · have he : i ≥ count := by scalar_tac
      simp [metadata.decode_export_section_loop.body, he]
      exact ⟨entries, by omega, hhistory, hbytes, hbound⟩
    · apply WP.spec_mono (export_step data count current pos i (by omega) hbound)
      intro r hr
      cases r with
      | done result =>
          obtain ⟨r, final⟩ := result
          cases r with
          | Err e => trivial
          | Ok next => exact False.elim hr
      | cont state =>
          obtain ⟨final, next, j⟩ := state
          obtain ⟨entry, ha, he, hb, hj⟩ := hr
          dsimp only at *
          refine ⟨⟨by omega, entries ++ [entry], ?_, .snoc hhistory ha, ?_, hb⟩, by omega⟩
          · simp only [List.length_append, List.length_singleton]
            omega
          · simpa using hbytes.snoc he
  · exact ⟨by simp, [], by simp, .nil, ⟨[], .nil, Body.Scalar.BytesAt.nil data start hstart⟩, hbound⟩

/-- `metadata.decode_export_section` adds the exports of a `VecEncoding ExportEncoding` span, each
with a fresh name and valid descriptor. -/
@[step]
theorem metadata.decode_export_section.spec (data : Slice U8) (start : Usize) (env : metadata.Env)
    (hbound : Module.Environment.Bounded env start.val) :
    metadata.decode_export_section data start env ⦃ r => match r.1 with
      | .Ok next => ∃ entries, ExportsAdded env entries r.2 ∧
          At (VecEncoding ExportEncoding) data start (entries.map Module.Environment.rawExport) next ∧
          Module.Environment.Bounded r.2 next.val
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hd⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data start)
  cases r with
  | Err e => simp [metadata.decode_export_section, hr]
  | Ok pair =>
      obtain ⟨count, pos⟩ := pair
      obtain ⟨⟨r, final⟩, hl, hp⟩ := WP.spec_imp_exists
        (metadata.decode_export_section_loop.spec data env count pos hd.span.2.2
          (hbound.mono (Nat.le_of_lt hd.span.1)))
      cases r with
      | Err e => simp [metadata.decode_export_section, hr, hl]
      | Ok next =>
          obtain ⟨entries, hlen, hhistory, hbytes, hb⟩ := hp
          simp [metadata.decode_export_section, hr, hl]
          exact ⟨entries, hhistory, At.vector hd hbytes (by simpa using hlen), hb⟩

end Itasca

end

/-! ## Memory -/

section

/-!
# Memory section parser

Soundness of `metadata.decode_memory_section` and its loop. `MemoriesAdded` says the environment
gains the decoded memory types. The span is a `VecEncoding MemTypeEncoding` whose limits are
within 2^16 pages, and the environment never holds more than one memory unless it already did.
Completeness is in `Module/Sections/IndexSpacesComplete`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Binary

/-- A memory type encoding consumes at least one byte. -/
theorem At.mem_type_progress {data start ty next} (h : At MemTypeEncoding data start ty next) :
    start.val < next.val := by
  obtain ⟨bytes, he, hs⟩ := h
  change LimitsEncoding ty.limits bytes at he
  have hn : bytes ≠ [] := by
    rintro rfl
    exact WebAssembly.Binary.LimitsEncoding.nonempty he rfl
  have := hs.length
  have := List.length_pos_iff.mpr hn
  omega

end Itasca.Binary

namespace Itasca.Module.Sections

/-- `result` is `env` with the memory types `added` appended and nothing else changed. -/
def MemoriesAdded (env result : metadata.Env) (added : List wasm_types.MemType) : Prop :=
  result = { env with mem_types := result.mem_types } ∧ result.mem_types.val = env.mem_types.val ++ added

end Itasca.Module.Sections

namespace Itasca

open Binary Module.Sections

/-- The memory loop adds `count` memory types forming a `Rep MemTypeEncoding` span with valid
limits. -/
@[step]
theorem metadata.decode_memory_section_loop.spec (data : Slice U8) (env : metadata.Env)
    (count : U32) (start : Usize) (hstart : start.val ≤ data.length)
    (hsize : env.mem_types.val.length ≤ start.val) :
    metadata.decode_memory_section_loop data env count start 0#u32 ⦃ r => match r.1 with
      | .Ok next => ∃ added, added.length = count.val ∧ MemoriesAdded env r.2 added ∧
          At (Rep MemTypeEncoding) data start added next ∧
          (∀ ft ∈ added, Module.Translation.LimitsValid ft.limits (2 ^ 16)) ∧ r.2.mem_types.val.length ≤ next.val ∧
          r.2.mem_types.val.length ≤ max env.mem_types.val.length 1
      | .Err _ => True ⦄ := by
  unfold metadata.decode_memory_section_loop
  apply loop.spec_decr_nat (fun s => count.val - s.2.2.val)
    (fun s => s.2.2.val ≤ count.val ∧ ∃ added, added.length = s.2.2.val ∧
      MemoriesAdded env s.1 added ∧ At (Rep MemTypeEncoding) data start added s.2.1 ∧
      (∀ ft ∈ added, Module.Translation.LimitsValid ft.limits (2 ^ 16)) ∧ s.1.mem_types.val.length ≤ s.2.1.val ∧
      s.1.mem_types.val.length ≤ max env.mem_types.val.length 1)
  · rintro ⟨current, pos, i⟩ ⟨hi, added, hlen, henv, hbytes, hvalid, hsize, hcount⟩
    dsimp only at hi hlen henv hbytes hvalid hsize hcount
    unfold metadata.decode_memory_section_loop.body
    dsimp only
    split
    · rename_i hstop
      have heq : i.val = count.val := by scalar_tac
      exact ⟨added, by omega, henv, hbytes, hvalid, hsize, hcount⟩
    · rename_i hmore
      obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (metadata.decode_mem_type.spec data pos)
      rw [hr]
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok pair =>
        obtain ⟨ft, next⟩ := pair
        obtain ⟨hb, ht⟩ := hp
        have hprogress := hb.mem_type_progress
        have hbound := hb.span.2
        have hcapacity : current.mem_types.val.length < Usize.max := by scalar_tac
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        step
        split
        · simp
        · rename_i hmax
          step
          refine ⟨?_, ⟨added ++ [ft], ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
          · scalar_tac
          · simp only [List.length_append, List.length_singleton]; scalar_tac
          · constructor
            · rw [henv.1]
            · simp [r_post, henv.2, List.append_assoc]
          · exact hbytes.snoc hb
          · intro ty hm
            rcases List.mem_append.mp hm with hm | hm
            · exact hvalid ty hm
            · simpa [List.mem_singleton.mp hm, Module.Translation.LimitsValid, Binary.LimitsValid,
                Option.mem_def, global_simps, U32.rMax] using ht
          · simp only [r_post, List.length_append, List.length_singleton]; omega
          · have hx : r.val.length ≤ 1 := by simpa [global_simps] using hmax
            exact hx.trans (Nat.le_max_right _ _)
          · scalar_tac
  · exact ⟨by simp, [], by simp, ⟨by cases env; rfl, by simp⟩,
      ⟨[], .nil, Body.Scalar.BytesAt.nil data start hstart⟩, by simp, hsize, Nat.le_max_left _ _⟩

/-- `metadata.decode_memory_section` adds the memory types of a `VecEncoding MemTypeEncoding` span
with valid limits. -/
@[step]
theorem metadata.decode_memory_section.spec (data : Slice U8) (pos : Usize) (env : metadata.Env)
    (hsize : env.mem_types.val.length ≤ pos.val) :
    metadata.decode_memory_section data pos env ⦃ r => match r.1 with
      | .Ok next => ∃ added, MemoriesAdded env r.2 added ∧
          At (VecEncoding MemTypeEncoding) data pos added next ∧
          (∀ ft ∈ added, Module.Translation.LimitsValid ft.limits (2 ^ 16)) ∧ r.2.mem_types.val.length ≤ next.val ∧
          r.2.mem_types.val.length ≤ max env.mem_types.val.length 1
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hc⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
  cases r with
  | Err e => simp [metadata.decode_memory_section, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
    obtain ⟨count, start⟩ := pair
    have hs := hc.span
    obtain ⟨⟨r, result⟩, hloop, hp⟩ := WP.spec_imp_exists
      (metadata.decode_memory_section_loop.spec data env count start hs.2.2 (by omega))
    simp [metadata.decode_memory_section, hr, core.result.Result.Insts.CoreOpsTry.branch]
    rw [hloop]
    cases r with
    | Err e => simp
    | Ok next =>
      obtain ⟨added, hlen, henv, hb, ht, hsize, hcount⟩ := hp
      exact ⟨added, henv, At.vector hc hb hlen, ht, hsize, by simpa using hcount⟩

end Itasca

end

/-! ## Table -/

section

/-!
# Table section parser

Soundness of `metadata.decode_table_section` and its loop. `TablesAdded` says the environment gains
the decoded table types. The span is a `VecEncoding TableTypeEncoding`, each table has limits
within the table cap. Completeness is in `Module/Sections/IndexSpacesComplete`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Binary

/-- A table type encoding consumes at least one byte. -/
theorem At.table_type_progress {data start ty next} (h : At TableTypeEncoding data start ty next) :
    start.val < next.val := by
  obtain ⟨bytes, he, hs⟩ := h
  obtain ⟨limits, _, rfl⟩ := tableType_reader_span he
  have := hs.length
  simp only [List.length_cons] at this
  omega

end Itasca.Binary

namespace Itasca.Module.Sections

/-- `result` is `env` with the table types `added` appended and nothing else changed. -/
def TablesAdded (env result : metadata.Env) (added : List wasm_types.TableType) : Prop :=
  result = { env with table_types := result.table_types } ∧ result.table_types.val = env.table_types.val ++ added

end Itasca.Module.Sections

namespace Itasca

open Binary Module.Sections

/-- The table loop adds `count` table types forming a `Rep TableTypeEncoding` span, with valid
limits. -/
@[step]
theorem metadata.decode_table_section_loop.spec (data : Slice U8) (env : metadata.Env)
    (count : U32) (start : Usize) (hstart : start.val ≤ data.length)
    (hsize : env.table_types.val.length ≤ start.val) :
    metadata.decode_table_section_loop data env count start 0#u32 ⦃ r => match r.1 with
      | .Ok next => ∃ added, added.length = count.val ∧ TablesAdded env r.2 added ∧
          At (Rep TableTypeEncoding) data start added next ∧
          (∀ ft ∈ added, Module.Translation.LimitsValid ft.limits (2 ^ 32 - 1)) ∧ r.2.table_types.val.length ≤ next.val
      | .Err _ => True ⦄ := by
  unfold metadata.decode_table_section_loop
  apply loop.spec_decr_nat (fun s => count.val - s.2.2.val)
    (fun s => s.2.2.val ≤ count.val ∧ ∃ added, added.length = s.2.2.val ∧
      TablesAdded env s.1 added ∧ At (Rep TableTypeEncoding) data start added s.2.1 ∧
      (∀ ft ∈ added, Module.Translation.LimitsValid ft.limits (2 ^ 32 - 1)) ∧ s.1.table_types.val.length ≤ s.2.1.val)
  · rintro ⟨current, pos, i⟩ ⟨hi, added, hlen, henv, hbytes, hvalid, hsize⟩
    dsimp only at hi hlen henv hbytes hvalid hsize
    unfold metadata.decode_table_section_loop.body
    dsimp only
    split
    · rename_i hstop
      have heq : i.val = count.val := by scalar_tac
      exact ⟨added, by omega, henv, hbytes, hvalid, hsize⟩
    · rename_i hmore
      obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (metadata.decode_table_type.spec data pos)
      rw [hr]
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok pair =>
        obtain ⟨ft, next⟩ := pair
        obtain ⟨hb, ht⟩ := hp
        have hprogress := hb.table_type_progress
        have hbound := hb.span.2
        have hcapacity : current.table_types.val.length < Usize.max := by scalar_tac
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        step
        step
        refine ⟨?_, ⟨added ++ [ft], ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
        · scalar_tac
        · simp only [List.length_append, List.length_singleton]; scalar_tac
        · constructor
          · rw [henv.1]
          · simp [r_post, henv.2, List.append_assoc]
        · exact hbytes.snoc hb
        · intro ty hm
          rcases List.mem_append.mp hm with hm | hm
          · exact hvalid ty hm
          · simpa [List.mem_singleton.mp hm, Module.Translation.LimitsValid, Binary.LimitsValid,
              Option.mem_def, global_simps, U32.rMax] using ht
        · simp only [r_post, List.length_append, List.length_singleton]; omega
        · scalar_tac
  · exact ⟨by simp, [], by simp, ⟨by cases env; rfl, by simp⟩,
      ⟨[], .nil, Body.Scalar.BytesAt.nil data start hstart⟩, by simp, hsize⟩

/-- `metadata.decode_table_section` adds the table types of a `VecEncoding TableTypeEncoding` span,
with valid limits. -/
@[step]
theorem metadata.decode_table_section.spec (data : Slice U8) (pos : Usize) (env : metadata.Env)
    (hsize : env.table_types.val.length ≤ pos.val) :
    metadata.decode_table_section data pos env ⦃ r => match r.1 with
      | .Ok next => ∃ added, TablesAdded env r.2 added ∧
          At (VecEncoding TableTypeEncoding) data pos added next ∧
          (∀ ft ∈ added, Module.Translation.LimitsValid ft.limits (2 ^ 32 - 1)) ∧ r.2.table_types.val.length ≤ next.val
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hc⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
  cases r with
  | Err e => simp [metadata.decode_table_section, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
    obtain ⟨count, start⟩ := pair
    have hs := hc.span
    obtain ⟨⟨r, result⟩, hloop, hp⟩ := WP.spec_imp_exists
      (metadata.decode_table_section_loop.spec data env count start hs.2.2 (by omega))
    simp [metadata.decode_table_section, hr, core.result.Result.Insts.CoreOpsTry.branch]
    rw [hloop]
    cases r with
    | Err e => simp
    | Ok next =>
      obtain ⟨added, hlen, henv, hb, ht, hsize⟩ := hp
      exact ⟨added, henv, At.vector hc hb hlen, ht, hsize⟩

end Itasca

end

/-! ## Data -/

section

/-!
# Data section parser

Soundness of `metadata.decode_data_segment`, `metadata.decode_data_section_loop` and
`metadata.decode_data_section`. Accepted segments are spans of the independent grammar
(`DataEncoding`) and satisfy `Module.Data.Valid`,
which covers the memory index and the offset initializer of active segments. Completeness is in `Module/Sections/TailComplete`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Module.Data

/-- A repetition span extends by one segment at its end. -/
theorem at_snoc {R : Binary.Data → List U8 → Prop} {data start pos next values value}
    (h : Binary.At (Binary.Rep R) data start values pos)
    (h' : Binary.At R data pos value next) :
    Binary.At (Binary.Rep R) data start (values ++ [value]) next := by
  obtain ⟨bytes, hr, hs⟩ := h
  obtain ⟨last, he, ht⟩ := h'
  exact ⟨bytes ++ last, hr.snoc he, hs.append ht⟩

/-- Like `encoded`: a flag word and the index encoding give an active
`DataEncoding`. -/
theorem encoded {data start first p1 p2 p3 next flags memory explicit offset count init}
    (hf : Binary.Leb128.Decoded data start flags first)
    (hm : Binary.At (fun pair => Binary.SegmentIndexEncoding flags pair.1 pair.2)
      data first (memory, explicit) p1)
    (ho : Binary.At Binary.ConstEncoding data p1 offset p2)
    (hc : Binary.Leb128.Decoded data p2 count p3)
    (hi : Body.Scalar.BytesAt data p3 init next) (hlen : init.length = count.val) :
    Binary.At Binary.DataEncoding data start
      ⟨.Active memory offset, init⟩ next := by
  obtain ⟨fb, hf, hfs⟩ := Binary.At.of_u32 hf
  obtain ⟨mb, hm, hms⟩ := hm
  obtain ⟨ob, ho, hos⟩ := ho
  obtain ⟨cb, hcs, hcl, hcb, hc⟩ := hc
  have hspan : Body.Scalar.BytesAt data p2 cb p3 := ⟨hcs, hcl, hcb⟩
  refine ⟨fb ++ mb ++ ob ++ (cb ++ init), ?_, ?_⟩
  · apply Binary.DataEncoding.of_parts hf hm ho
    exact Binary.ByteVecEncoding.iff.mpr ⟨cb, by simpa [hlen] using hc, rfl⟩
  · exact ((hfs.append hms).append hos).append (hspan.append hi)

/-- Flag `1` followed by a counted byte string is a passive Wasm 2.0 data segment. -/
theorem passive_encoded {data start first content next count init}
    (hf : Binary.Leb128.Decoded data start 1#u32 first)
    (hc : Binary.Leb128.Decoded data first count content)
    (hi : Body.Scalar.BytesAt data content init next) (hlen : init.length = count.val) :
    Binary.At Binary.DataEncoding data start ⟨.Passive, init⟩ next := by
  obtain ⟨fb, hf, hfs⟩ := Binary.At.of_u32 hf
  obtain ⟨cb, hcs, hcl, hcb, hc⟩ := hc
  have hcount : Body.Scalar.BytesAt data first cb content := ⟨hcs, hcl, hcb⟩
  exact ⟨fb ++ (cb ++ init), Binary.DataEncoding.of_passive hf
    (Binary.ByteVecEncoding.iff.mpr ⟨cb, by simpa [hlen] using hc, rfl⟩),
    hfs.append (hcount.append hi)⟩

end Itasca.Module.Data

namespace Itasca

/-- An accepted `metadata.decode_data_segment` is a `DataEncoding` span and its segment
is `Module.Data.Valid`. -/
@[step]
theorem metadata.decode_data_segment.spec (data : Slice U8) (pos : Usize) (env : metadata.Env) :
    metadata.decode_data_segment data pos env ⦃ r => match r with
      | .Ok (segment, next) =>
          Binary.At Binary.DataEncoding data pos (Module.Data.raw segment) next ∧
          Module.Data.Valid env segment
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hm⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
  cases r with
  | Err e =>
    simp [metadata.decode_data_segment, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
    rcases pair with ⟨flags, first⟩
    change Binary.Leb128.Decoded data pos flags first at hm
    by_cases hpass : flags = 1#u32
    · subst flags
      obtain ⟨r, hlen, hc⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data first)
      cases r with
      | Err e => simp [metadata.decode_data_segment, hr, hlen, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          error.Error.Insts.CoreConvertFromOpError.from]
      | Ok pair =>
        obtain ⟨count, content⟩ := pair
        simp [metadata.decode_data_segment, hr, hlen, core.result.Result.Insts.CoreOpsTry.branch]
        step
        have hcontent : content.val ≤ data.length := hc.span.2.2
        obtain ⟨r, hh, havail⟩ := WP.spec_imp_exists (metadata.have_bytes.spec data content n hcontent)
        cases r with
        | Err e => simp [hh, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok u =>
          cases u
          simp only [hh, bind_ok]
          have havail' : content.val + n.val ≤ data.length := havail.1.mp rfl
          step
          step
          refine ⟨Module.Data.passive_encoded hm hc init_post ?_, trivial⟩
          have hl := init_post.length
          scalar_tac
    ·
      obtain ⟨r, hseg, hindex⟩ := WP.spec_imp_exists
        (metadata.decode_segment_index.spec data first flags hm.span.2.2)
      cases r with
      | Err e =>
          simp [metadata.decode_data_segment, hr, hseg, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          split <;> first | contradiction | simp
      | Ok triple =>
          obtain ⟨memory, p1, explicit⟩ := triple
          simp [metadata.decode_data_segment, hr, hseg, core.result.Result.Insts.CoreOpsTry.branch]
          split <;> try contradiction
          step
          split
          · simp
          · have hmem : memory.val < env.mem_types.val.length := by scalar_tac
            obtain ⟨r, hr, ho⟩ := WP.spec_imp_exists (metadata.decode_const_expr.spec data p1 env .I32)
            cases r with
            | Err e =>
              simp [hr, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
            | Ok pair =>
              rcases pair with ⟨offset, p2⟩
              change Binary.At Binary.ConstEncoding data p1 offset p2 ∧
                Module.Constants.Valid env offset .I32 at ho
              obtain ⟨r, hlen, hc⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data p2)
              cases r with
              | Err e =>
                simp [hr, hlen, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                  error.Error.Insts.CoreConvertFromOpError.from]
              | Ok pair =>
                rcases pair with ⟨count, p3⟩
                change Binary.Leb128.Decoded data p2 count p3 at hc
                simp [hr, hlen]
                step
                have hp3 : p3.val ≤ data.length := hc.span.2.2
                obtain ⟨r, hh, havail⟩ := WP.spec_imp_exists (metadata.have_bytes.spec data p3 n hp3)
                cases r with
                | Err e =>
                  simp [hh, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
                | Ok u =>
                  cases u
                  simp only [hh, bind_ok]
                  have havail' : p3.val + n.val ≤ data.length := havail.1.mp rfl
                  step
                  step
                  refine ⟨Module.Data.encoded hm hindex ho.1 hc init_post ?_, hmem, ho.2⟩
                  have hl := init_post.length
                  scalar_tac

/-- The data loop returns `count` segments forming a `Rep` span, all valid. -/
@[step]
theorem metadata.decode_data_section_loop.spec (data : Slice U8) (env : metadata.Env)
    (count : U32) (start : Usize) (hstart : start.val ≤ data.length) :
    metadata.decode_data_section_loop data env count (alloc.vec.Vec.new _) start 0#u32 ⦃ r =>
      match r with
      | .Ok (segments, next) => segments.val.length = count.val ∧
          Binary.At (Binary.Rep Binary.DataEncoding)
            data start (segments.val.map Module.Data.raw) next ∧
          ∀ segment ∈ segments.val, Module.Data.Valid env segment
      | .Err _ => True ⦄ := by
  unfold metadata.decode_data_section_loop
  apply loop.spec_decr_nat (fun s => count.val - s.2.2.val)
    (fun s => s.2.2.val ≤ count.val ∧ s.1.val.length = s.2.2.val ∧
      Binary.At (Binary.Rep Binary.DataEncoding)
        data start (s.1.val.map Module.Data.raw) s.2.1 ∧
      ∀ segment ∈ s.1.val, Module.Data.Valid env segment)
  · rintro ⟨out, pos, i⟩ ⟨hi, hlen, hbytes, hvalid⟩
    dsimp only at hi hlen hbytes hvalid
    unfold metadata.decode_data_section_loop.body
    dsimp only
    split
    · rename_i hstop
      have heq : i.val = count.val := by scalar_tac
      exact ⟨by omega, hbytes, hvalid⟩
    · rename_i hmore
      have hlt : i.val < count.val := by scalar_tac
      have hcapacity : out.val.length < Usize.max := by scalar_tac
      obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (metadata.decode_data_segment.spec data pos env)
      rw [hr]
      cases r with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok pair =>
        rcases pair with ⟨segment, next⟩
        obtain ⟨hb, ht⟩ := hp
        simp [core.result.Result.Insts.CoreOpsTry.branch]
        step
        step
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · scalar_tac
        · simp only [out1_post, List.length_append, List.length_singleton]
          scalar_tac
        · simpa [out1_post, List.map_append] using Module.Data.at_snoc hbytes hb
        · intro entry he
          rw [out1_post] at he
          rcases List.mem_append.mp he with he | he
          · exact hvalid entry he
          · simpa [List.mem_singleton.mp he] using ht
        · scalar_tac
  · refine ⟨by simp, by simp, ?_, by simp [alloc.vec.Vec.new]⟩
    exact ⟨[], .nil, Body.Scalar.BytesAt.nil data start hstart⟩

/-- An accepted `metadata.decode_data_section` returns segments forming a `VecEncoding` span, all
valid. -/
@[step]
theorem metadata.decode_data_section.spec (data : Slice U8) (pos : Usize) (env : metadata.Env) :
    metadata.decode_data_section data pos env ⦃ r => match r with
      | .Ok (segments, next) =>
          Binary.At (Binary.VecEncoding Binary.DataEncoding)
            data pos (segments.val.map Module.Data.raw) next ∧
          ∀ segment ∈ segments.val, Module.Data.Valid env segment
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hc⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
  cases r with
  | Err e =>
    simp [metadata.decode_data_section, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
    rcases pair with ⟨count, start⟩
    change Binary.Leb128.Decoded data pos count start at hc
    obtain ⟨r, hloop, hp⟩ := WP.spec_imp_exists
      (metadata.decode_data_section_loop.spec data env count start hc.span.2.2)
    simp [metadata.decode_data_section, hr, core.result.Result.Insts.CoreOpsTry.branch]
    rw [hloop]
    cases r with
    | Err e => simp
    | Ok pair =>
      rcases pair with ⟨segments, next⟩
      obtain ⟨hlen, hbytes, hvalid⟩ := hp
      obtain ⟨bytes, he, hs⟩ := hbytes
      obtain ⟨countBytes, hcs, hcl, hcb, hce⟩ := hc
      have hcspan : Body.Scalar.BytesAt data pos countBytes start := ⟨hcs, hcl, hcb⟩
      refine ⟨⟨countBytes ++ bytes, ?_, hcspan.append hs⟩, hvalid⟩
      exact ⟨countBytes, bytes, by simpa [hlen] using hce, he, rfl⟩

end Itasca

end

end

/-! ## EnvironmentAndTail -/

section

/-!
# Environment declarations and module tails

Global, function, import and element sections extend the decoded environment with exact
grammar witnesses. Tail traversal composes custom/data sections after code while retaining
callback and region effects.
-/

/-! ## Global -/

section

/-!
# Global section parser

Soundness of `metadata.decode_global_section` and its loop. `GlobalsAdded` says the environment
gains the decoded globals, their types and the function references their initializers declare.
The span is a `VecEncoding GlobalEncoding` and each initializer is `Module.Constants.Valid` at its
global's type. Completeness is in `Module/Sections/DeclarationsComplete`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Module.Constants

/-- Constant validity is preserved when globals are appended after the imported ones. -/
theorem Valid.append_globals {env result e t} (h : Valid env e t)
    (suffix : List wasm_types.GlobalType)
    (hglobals : result.global_types.val = env.global_types.val ++ suffix)
    (hcount : result.num_imported_globals = env.num_imported_globals)
    (hfuncs : result.func_types = env.func_types) : Valid result e t := by
  cases h with
  | i32 value => exact .i32 value
  | i64 value => exact .i64 value
  | f32 value => exact .f32 value
  | f64 value => exact .f64 value
  | v128 low high => exact .v128 low high
  | refNull ty => exact .refNull ty
  | refFunc idx hi => exact .refFunc idx (by simpa [hfuncs] using hi)
  | globalGet idx gt hi hgt himport hconst =>
    have hi' : idx.val < result.global_types.val.length := by simp [hglobals]; omega
    exact Valid.globalGet idx gt hi'
      (by simpa only [hglobals, List.getElem_append_left hi] using hgt)
      (by simpa [hcount] using himport) hconst

end Itasca.Module.Constants

namespace Itasca.Module.Sections

/-- `result` is `env` with the globals `added` appended to the globals and global types, and the
function references of their initializers appended to the declared functions. Nothing else
changes. -/
def GlobalsAdded (env result : metadata.Env) (added : List metadata.Global) : Prop :=
  result = { env with globals := result.globals, global_types := result.global_types, declared_funcs := result.declared_funcs } ∧
  result.globals.val = env.globals.val ++ added ∧
  result.global_types.val = env.global_types.val ++ added.map metadata.Global.gtype ∧
  result.declared_funcs.val = env.declared_funcs.val ++ added.flatMap Module.References.global

/-- A global type and an initializer span in sequence form a `GlobalEncoding`. -/
theorem global_encoded {data start pos next gt init}
    (hg : Binary.At Binary.GlobalTypeEncoding data start gt pos)
    (hi : Binary.At Binary.ConstEncoding data pos init next) :
    Binary.At Binary.GlobalEncoding data start ⟨gt, init⟩ next := by
  obtain ⟨gbytes, hg, hs⟩ := hg
  obtain ⟨ibytes, hi, his⟩ := hi
  exact ⟨gbytes ++ ibytes, Binary.GlobalEncoding.reader_parts.mpr ⟨gbytes, ibytes, hg, hi, rfl⟩, hs.append his⟩

end Itasca.Module.Sections

namespace Itasca

open Binary Module.Sections

/-- The global loop adds `count` globals forming a `Rep GlobalEncoding` span, with valid
initializers. -/
@[step]
theorem metadata.decode_global_section_loop.spec (data : Slice U8) (env : metadata.Env)
    (count : U32) (start : Usize) (hstart : start.val ≤ data.length)
    (hglobals : env.globals.val.length ≤ start.val)
    (htypes : env.global_types.val.length ≤ start.val)
    (hreferences : env.declared_funcs.val.length ≤ start.val) :
    metadata.decode_global_section_loop data env count start 0#u32 ⦃ r => match r.1 with
      | .Ok next => ∃ added, added.length = count.val ∧ GlobalsAdded env r.2 added ∧
          At (Rep GlobalEncoding) data start added next ∧
          (∀ g ∈ added, Module.Constants.Valid r.2 g.init g.gtype.valtype) ∧
          r.2.globals.val.length ≤ next.val ∧ r.2.global_types.val.length ≤ next.val ∧
          r.2.declared_funcs.val.length ≤ next.val
      | .Err _ => True ⦄ := by
  unfold metadata.decode_global_section_loop
  apply loop.spec_decr_nat (fun s => count.val - s.2.2.val)
    (fun s => s.2.2.val ≤ count.val ∧ ∃ added, added.length = s.2.2.val ∧
      GlobalsAdded env s.1 added ∧ At (Rep GlobalEncoding) data start added s.2.1 ∧
      (∀ g ∈ added, Module.Constants.Valid s.1 g.init g.gtype.valtype) ∧
      s.1.globals.val.length ≤ s.2.1.val ∧ s.1.global_types.val.length ≤ s.2.1.val ∧
      s.1.declared_funcs.val.length ≤ s.2.1.val)
  · rintro ⟨current, pos, i⟩ ⟨hi, added, hlen, henv, hbytes, hvalid, hglobals, htypes, hreferences⟩
    dsimp only at hi hlen henv hbytes hvalid hglobals htypes hreferences
    unfold metadata.decode_global_section_loop.body
    dsimp only
    split
    · rename_i hstop
      have heq : i.val = count.val := by scalar_tac
      exact ⟨added, by omega, henv, hbytes, hvalid, hglobals, htypes, hreferences⟩
    · rename_i hmore
      obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (metadata.decode_global_type.spec data pos)
      rw [hr]
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok pair =>
        obtain ⟨gt, middle⟩ := pair
        have hprogress : pos.val < middle.val := by
          obtain ⟨bytes, he, hs⟩ := hp
          obtain rfl := GlobalTypeEncoding.reader_bytes.mp he
          have := hs.length
          simp only [List.length_cons, List.length_nil] at this
          omega
        obtain ⟨r, hc, hconst⟩ := WP.spec_imp_exists (metadata.decode_const_expr.spec data middle current gt.valtype)
        cases r with
        | Err e => simp [hc, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok pair =>
          obtain ⟨init, next⟩ := pair
          obtain ⟨hcb, hcv⟩ := hconst
          have hs := hcb.span
          have hcapacity : current.global_types.val.length < Usize.max := by scalar_tac
          have hcapacity' : current.globals.val.length < Usize.max := by scalar_tac
          have hcapacityRefs : current.declared_funcs.val.length < Usize.max := by scalar_tac
          simp [hc, core.result.Result.Insts.CoreOpsTry.branch]
          step as ⟨declared, hdeclared⟩
          have hdstate := hdeclared.1
          rw [hdstate]
          clear hdstate
          step
          step
          step
          let entry : metadata.Global := ⟨gt, init⟩
          refine ⟨?_, ⟨added ++ [entry], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
          · scalar_tac
          · simp only [List.length_append, List.length_singleton]; scalar_tac
          · refine ⟨?_, ?_, ?_, ?_⟩
            · rw [henv.1]
            · simp only [v1_post, henv.2.1, List.append_assoc, entry]
            · simp [v_post, henv.2.2.1, List.append_assoc, entry]
            · simp [hdeclared.2, henv.2.2.2, List.flatMap_append,
                Module.References.global, entry, List.append_assoc]
          · exact hbytes.snoc (global_encoded hp hcb)
          · intro g hm
            rcases List.mem_append.mp hm with hm | hm
            · exact (hvalid g hm).append_globals [gt] v_post rfl rfl
            · obtain rfl := List.mem_singleton.mp hm
              exact hcv.append_globals [gt] v_post rfl rfl
          · simp only [v1_post, List.length_append, List.length_singleton]; omega
          · simp only [v_post, List.length_append, List.length_singleton]; omega
          · have hlen : (Module.References.initializer init).length ≤ 1 := by
              cases init <;> simp [Module.References.initializer]
            simp only [hdeclared.2, List.length_append]
            omega
          · scalar_tac
  · exact ⟨by simp, [], by simp,
      ⟨by cases env; rfl, by simp, by simp, by simp⟩,
      ⟨[], .nil, Body.Scalar.BytesAt.nil data start hstart⟩, by simp, hglobals, htypes, hreferences⟩

/-- `metadata.decode_global_section` adds the globals of a `VecEncoding GlobalEncoding` span, with
valid initializers. -/
@[step]
theorem metadata.decode_global_section.spec (data : Slice U8) (pos : Usize) (env : metadata.Env)
    (hglobals : env.globals.val.length ≤ pos.val)
    (htypes : env.global_types.val.length ≤ pos.val)
    (hreferences : env.declared_funcs.val.length ≤ pos.val) :
    metadata.decode_global_section data pos env ⦃ r => match r.1 with
      | .Ok next => ∃ added, GlobalsAdded env r.2 added ∧
          At (VecEncoding GlobalEncoding) data pos added next ∧
          (∀ g ∈ added, Module.Constants.Valid r.2 g.init g.gtype.valtype) ∧
          r.2.globals.val.length ≤ next.val ∧ r.2.global_types.val.length ≤ next.val ∧
          r.2.declared_funcs.val.length ≤ next.val
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hc⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
  cases r with
  | Err e => simp [metadata.decode_global_section, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
    obtain ⟨count, start⟩ := pair
    have hs := hc.span
    obtain ⟨⟨r, result⟩, hloop, hp⟩ := WP.spec_imp_exists
      (metadata.decode_global_section_loop.spec data env count start hs.2.2 (by omega) (by omega) (by omega))
    simp [metadata.decode_global_section, hr, core.result.Result.Insts.CoreOpsTry.branch]
    rw [hloop]
    cases r with
    | Err e => simp
    | Ok next =>
      obtain ⟨added, hlen, henv, hb, ht, hg, hgt, href⟩ := hp
      exact ⟨added, henv, At.vector hc hb hlen, ht, hg, hgt, href⟩

end Itasca

end

/-! ## Function -/

section

/-!
# Function section parser

Soundness of `metadata.decode_function_section` and its loop. `FunctionsAdded` says the environment
gains the decoded type indices and the signatures they resolve to, in order. The decoded span is
a `VecEncoding IndexEncoding`. Completeness is in `Module/Sections/DeclarationsComplete`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Module.Sections

/-- `result` is `env` with `indices` appended to the function type indices and the resolved
`signatures` appended to the function types, and nothing else changed. -/
def FunctionsAdded (env result : metadata.Env) (indices : List U32)
    (signatures : List wasm_types.FuncType) : Prop :=
  result = { env with func_type_indices := result.func_type_indices, func_types := result.func_types } ∧
    result.func_type_indices.val = env.func_type_indices.val ++ indices ∧
    result.func_types.val = env.func_types.val ++ signatures ∧
    List.Forall₂ (Module.Environment.Resolves env.types.val) indices signatures

end Itasca.Module.Sections

namespace Itasca

open Binary Module.Sections

/-- The function loop adds `count` indices forming a `Rep IndexEncoding` span. -/
@[step]
theorem metadata.decode_function_section_loop.spec (data : Slice U8) (env : metadata.Env)
    (count : U32) (start : Usize) (hstart : start.val ≤ data.length)
    (hfuncs : env.func_types.val.length ≤ start.val)
    (hindices : env.func_type_indices.val.length ≤ start.val) :
    metadata.decode_function_section_loop data env count start 0#u32 ⦃ r => match r.1 with
      | .Ok next => ∃ indices signatures, indices.length = count.val ∧
          FunctionsAdded env r.2 indices signatures ∧
          At (Rep IndexEncoding) data start indices next ∧
          r.2.func_types.val.length ≤ next.val ∧ r.2.func_type_indices.val.length ≤ next.val
      | .Err _ => True ⦄ := by
  unfold metadata.decode_function_section_loop
  apply loop.spec_decr_nat (fun s => count.val - s.2.2.val)
    (fun s => s.2.2.val ≤ count.val ∧ ∃ indices signatures,
      indices.length = s.2.2.val ∧ FunctionsAdded env s.1 indices signatures ∧
      At (Rep IndexEncoding) data start indices s.2.1 ∧
      s.1.func_types.val.length ≤ s.2.1.val ∧ s.1.func_type_indices.val.length ≤ s.2.1.val)
  · rintro ⟨current, pos, i⟩ ⟨hi, indices, signatures, hlen, henv, hbytes, hfuncs, hindices⟩
    dsimp only at hi hlen henv hbytes hfuncs hindices
    unfold metadata.decode_function_section_loop.body
    dsimp only
    split
    · rename_i hstop
      have heq : i.val = count.val := by scalar_tac
      exact ⟨indices, signatures, by omega, henv, hbytes, hfuncs, hindices⟩
    · rename_i hmore
      obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
      rw [hr]
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          error.Error.Insts.CoreConvertFromOpError.from]
      | Ok pair =>
        obtain ⟨idx, next⟩ := pair
        have hs := hp.span
        obtain ⟨r, ht, hlookup⟩ := WP.spec_imp_exists (metadata.lookup_type.spec current idx)
        cases r with
        | Err e => simp [ht, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok ft =>
          have hcapacity : current.func_types.val.length < Usize.max := by scalar_tac
          have hcapacity' : current.func_type_indices.val.length < Usize.max := by scalar_tac
          have htypes : current.types = env.types := by rw [henv.1]
          have hresolve : Module.Environment.Resolves env.types.val idx ft := by
            simpa [Module.Environment.Resolves, htypes] using hlookup
          simp [ht, core.result.Result.Insts.CoreOpsTry.branch]
          step
          step
          step
          refine ⟨?_, ⟨indices ++ [idx], ?_, ⟨signatures ++ [ft], ?_⟩, ?_, ?_, ?_⟩, ?_⟩
          · scalar_tac
          · simp only [List.length_append, List.length_singleton]; scalar_tac
          · refine ⟨?_, ?_, ?_, ?_⟩
            · rw [henv.1]
            · simp [v1_post, henv.2.1, List.append_assoc]
            · simp [v_post, henv.2.2.1, List.append_assoc]
            · exact List.rel_append henv.2.2.2 (.cons hresolve .nil)
          · exact hbytes.snoc (At.of_u32 hp)
          · simp only [v_post, List.length_append, List.length_singleton]; omega
          · simp only [v1_post, List.length_append, List.length_singleton]; omega
          · scalar_tac
  · exact ⟨by simp, [], [], by simp,
      ⟨by cases env; rfl, by simp, by simp, .nil⟩,
      ⟨[], .nil, Body.Scalar.BytesAt.nil data start hstart⟩, hfuncs, hindices⟩

/-- `metadata.decode_function_section` adds the indices of a `VecEncoding IndexEncoding` span with
their resolved signatures. -/
@[step]
theorem metadata.decode_function_section.spec (data : Slice U8) (pos : Usize) (env : metadata.Env)
    (hfuncs : env.func_types.val.length ≤ pos.val)
    (hindices : env.func_type_indices.val.length ≤ pos.val) :
    metadata.decode_function_section data pos env ⦃ r => match r.1 with
      | .Ok next => ∃ indices signatures, FunctionsAdded env r.2 indices signatures ∧
          At (VecEncoding IndexEncoding) data pos indices next ∧
          r.2.func_types.val.length ≤ next.val ∧ r.2.func_type_indices.val.length ≤ next.val
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hc⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
  cases r with
  | Err e => simp [metadata.decode_function_section, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
    obtain ⟨count, start⟩ := pair
    have hs := hc.span
    obtain ⟨⟨r, result⟩, hloop, hp⟩ := WP.spec_imp_exists
      (metadata.decode_function_section_loop.spec data env count start hs.2.2 (by omega) (by omega))
    simp [metadata.decode_function_section, hr, core.result.Result.Insts.CoreOpsTry.branch]
    rw [hloop]
    cases r with
    | Err e => simp
    | Ok next =>
      obtain ⟨indices, signatures, hlen, henv, hb, hf, hi⟩ := hp
      exact ⟨indices, ⟨signatures, henv⟩, At.vector hc hb hlen, hf, hi⟩

end Itasca

end

/-! ## Import -/

section

/-!
# Single import parser

Soundness of `metadata.decode_import`. `ImportAdded` says that the environment gains the import
and updates only the index space of its kind, with the limits and memory count checks of
that kind. The decoded bytes are an `ImportEncoding` span and the environment stays `Bounded`.
Completeness is in `Module/Sections/IndexSpacesComplete`.
-/

set_option maxHeartbeats 800000

open Aeneas Aeneas.Std

namespace Itasca.Module.Sections

/-- `result` is `env` with `entry` appended to the imports and to the index space of its kind.
Functions must resolve their type, tables and memories satisfy their limits, and memories
respect the count cap. -/
def ImportAdded (env result : metadata.Env) (entry : metadata.Import) : Prop :=
  result.imports.val = env.imports.val ++ [entry] ∧
  match entry.desc with
  | .Func idx => ∃ ft, Module.Environment.Resolves env.types.val idx ft ∧
      result = { env with imports := result.imports, func_types := result.func_types, num_imported_funcs := result.num_imported_funcs } ∧
      result.func_types.val = env.func_types.val ++ [ft] ∧
      result.num_imported_funcs.val = env.num_imported_funcs.val + 1
  | .Global gt =>
      result = { env with imports := result.imports, global_types := result.global_types, num_imported_globals := result.num_imported_globals } ∧
      result.global_types.val = env.global_types.val ++ [gt] ∧
      result.num_imported_globals.val = env.num_imported_globals.val + 1
  | .Table tt =>
      result = { env with imports := result.imports, table_types := result.table_types } ∧
      result.table_types.val = env.table_types.val ++ [tt] ∧
      Module.Translation.LimitsValid tt.limits (2 ^ 32 - 1)
  | .Memory mt =>
      result = { env with imports := result.imports, mem_types := result.mem_types } ∧
      result.mem_types.val = env.mem_types.val ++ [mt] ∧ result.mem_types.val.length ≤ 1 ∧
      Module.Translation.LimitsValid mt.limits (2 ^ 16)

/-- A module name, an import name and a descriptor span in sequence form an `ImportEncoding`. -/
theorem import_encoded {data start p1 p2 next moduleName nm desc}
    (hm : Binary.At Binary.NameEncoding data start moduleName p1)
    (hn : Binary.At Binary.NameEncoding data p1 nm p2)
    (hd : Binary.At Binary.ImportDescEncoding data p2 desc next) :
    Binary.At Binary.ImportEncoding data start ⟨moduleName, nm, desc⟩ next := by
  obtain ⟨mb, hm, hs⟩ := hm
  obtain ⟨nb, hn, hns⟩ := hn
  obtain ⟨db, hd, hds⟩ := hd
  exact ⟨mb ++ nb ++ db, Binary.ImportEncoding.reader_parts.mpr ⟨mb, nb, db, hm, hn, hd, rfl⟩, (hs.append hns).append hds⟩

end Itasca.Module.Sections

namespace Itasca

open Binary Module.Sections

/-- `metadata.decode_import` adds one import to the environment (`ImportAdded`), the bytes are its
`ImportEncoding` span, and the environment stays within the byte bound. -/
@[step]
theorem metadata.decode_import.spec (data : Slice U8) (pos : Usize) (env : metadata.Env)
    (hbound : Module.Environment.Bounded env pos.val) :
    metadata.decode_import data pos env ⦃ r => match r.1 with
      | .Ok next => ∃ entry, ImportAdded env r.2 entry ∧
          At ImportEncoding data pos (Module.Environment.rawImport entry) next ∧
          Module.Environment.Bounded r.2 next.val
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hm⟩ := WP.spec_imp_exists (metadata.decode_name.spec data pos)
  cases r with
  | Err e => simp [metadata.decode_import, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
    obtain ⟨modname, p1⟩ := pair
    obtain ⟨r, hn, hname⟩ := WP.spec_imp_exists (metadata.decode_name.spec data p1)
    cases r with
    | Err e => simp [metadata.decode_import, hr, hn, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok pair =>
      obtain ⟨nm, p2⟩ := pair
      obtain ⟨r, hk, hkind⟩ := WP.spec_imp_exists (reader.read_byte.module_spec data p2)
      cases r with
      | Err e => simp [metadata.decode_import, hr, hn, hk, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          error.Error.Insts.CoreConvertFromOpError.from]
      | Ok pair =>
        obtain ⟨kind, p3⟩ := pair
        have hspanM := hm.span
        have hspanN := hname.span
        have hspanK := (At.byte hkind).length
        have hspanB := (At.byte hkind).bound
        have hprogress : pos.val < p3.val := by simp only [List.length_singleton] at hspanK; omega
        cases hbound
        simp [metadata.decode_import, hr, hn, hk, core.result.Result.Insts.CoreOpsTry.branch]
        split
        · obtain ⟨r, hd, hdesc⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data p3)
          cases r with
          | Err e => simp [hd,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
              error.Error.Insts.CoreConvertFromOpError.from]
          | Ok pair =>
            obtain ⟨value, next⟩ := pair
            have hspanD := hdesc.span
            obtain ⟨r, ht, hlookup⟩ := WP.spec_imp_exists (metadata.lookup_type.spec env value)
            cases r with
            | Err e => simp [hd, ht,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
            | Ok ft =>
              have hcapacity : env.func_types.val.length < Usize.max := by scalar_tac
              have hcapacityI : env.imports.val.length < Usize.max := by scalar_tac
              have hcapacityN : env.num_imported_funcs.val < Usize.max := by scalar_tac
              simp [hd, ht]
              step
              step
              step
              let entry : metadata.Import := ⟨modname, nm, .Func value⟩
              refine ⟨entry, ?_, ?_, ?_⟩
              · refine ⟨v1_post, ft, hlookup, rfl, v_post, i_post⟩
              · apply import_encoded hm hname
                apply At.prepend (by with_unfolding_all exact hkind) (At.of_u32 hdesc)
                intro bytes hbytes
                exact .func value.val ((Leb128.encoding_iff _ _).mp hbytes)
              · constructor <;> simp only [v_post, v1_post, List.length_append, List.length_singleton] <;> scalar_tac
        · obtain ⟨r, hd, hdesc⟩ := WP.spec_imp_exists (metadata.decode_table_type.spec data p3)
          cases r with
          | Err e => simp [hd,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          | Ok pair =>
            obtain ⟨value, next⟩ := pair
            obtain ⟨hdesc, hlimits⟩ := hdesc
            have hspanD := hdesc.span
            have hcapacity : env.table_types.val.length < Usize.max := by scalar_tac
            have hcapacityI : env.imports.val.length < Usize.max := by scalar_tac
            simp [hd]
            step
            step
            let entry : metadata.Import := ⟨modname, nm, .Table value⟩
            refine ⟨entry, ?_, ?_, ?_⟩
            · refine ⟨v1_post, rfl, v_post, ?_⟩
              simpa [Module.Translation.LimitsValid, Binary.LimitsValid, Option.mem_def, global_simps, U32.rMax] using hlimits
            · apply import_encoded hm hname
              apply At.prepend (by with_unfolding_all exact hkind) hdesc
              intro bytes hbytes
              exact .table _ hbytes
            · constructor <;> simp only [v_post, v1_post, List.length_append, List.length_singleton] <;> scalar_tac
        · obtain ⟨r, hd, hdesc⟩ := WP.spec_imp_exists (metadata.decode_mem_type.spec data p3)
          cases r with
          | Err e => simp [hd,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          | Ok pair =>
            obtain ⟨value, next⟩ := pair
            obtain ⟨hdesc, hlimits⟩ := hdesc
            have hspanD := hdesc.span
            have hcapacity : env.mem_types.val.length < Usize.max := by scalar_tac
            have hcapacityI : env.imports.val.length < Usize.max := by scalar_tac
            simp [hd]
            step
            split
            · simp
            · rename_i hcount
              step
              let entry : metadata.Import := ⟨modname, nm, .Memory value⟩
              refine ⟨entry, ?_, ?_, ?_⟩
              · refine ⟨v1_post, rfl, v_post, ?_, ?_⟩
                · simpa [global_simps] using hcount
                · simpa [Module.Translation.LimitsValid, Binary.LimitsValid, Option.mem_def, global_simps, U32.rMax] using hlimits
              · apply import_encoded hm hname
                apply At.prepend (by with_unfolding_all exact hkind) hdesc
                intro bytes hbytes
                exact .memory _ hbytes
              · constructor <;> simp only [v_post, v1_post, List.length_append, List.length_singleton] <;> scalar_tac
        · obtain ⟨r, hd, hdesc⟩ := WP.spec_imp_exists (metadata.decode_global_type.spec data p3)
          cases r with
          | Err e => simp [hd,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          | Ok pair =>
            obtain ⟨value, next⟩ := pair
            have hspanD := hdesc.span
            have hcapacity : env.global_types.val.length < Usize.max := by scalar_tac
            have hcapacityI : env.imports.val.length < Usize.max := by scalar_tac
            have hcapacityN : env.num_imported_globals.val < Usize.max := by scalar_tac
            simp [hd]
            step
            step
            step
            let entry : metadata.Import := ⟨modname, nm, .Global value⟩
            refine ⟨entry, ?_, ?_, ?_⟩
            · exact ⟨v1_post, rfl, v_post, i_post⟩
            · apply import_encoded hm hname
              apply At.prepend (by with_unfolding_all exact hkind) hdesc
              intro bytes hbytes
              exact .global _ hbytes
            · constructor <;> simp only [v_post, v1_post, List.length_append, List.length_singleton] <;> scalar_tac
        · simp

end Itasca

end

/-! ## Imports -/

section

/-!
# Import section parser

Soundness of `metadata.decode_import_section` and its loop. `ImportsAdded` is the ordered sequence
of `ImportAdded` updates. The
decoded span is a `VecEncoding ImportEncoding` of the raw imports. Completeness is in
`Module/Sections/IndexSpacesComplete`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Module.Sections

/-- `result` is `initial` after adding `entries` one at a time by `ImportAdded`. -/
inductive ImportsAdded (initial : metadata.Env) : List metadata.Import → metadata.Env →
    Prop where
  | nil : ImportsAdded initial [] initial
  | snoc {entries before after entry} : ImportsAdded initial entries before →
      ImportAdded before after entry → ImportsAdded initial (entries ++ [entry]) after

end Itasca.Module.Sections

namespace Itasca

open Binary Module.Sections

/-- The import loop adds `count` imports forming a `Rep ImportEncoding` span. -/
@[step]
theorem metadata.decode_import_section_loop.spec (data : Slice U8) (env : metadata.Env)
    (count : U32) (start : Usize) (hstart : start.val ≤ data.length)
    (hbound : Module.Environment.Bounded env start.val) :
    metadata.decode_import_section_loop data env count start 0#u32 ⦃ r => match r.1 with
      | .Ok next => ∃ entries, entries.length = count.val ∧ ImportsAdded env entries r.2 ∧
          At (Rep ImportEncoding) data start (entries.map Module.Environment.rawImport) next ∧
          Module.Environment.Bounded r.2 next.val
      | .Err _ => True ⦄ := by
  unfold metadata.decode_import_section_loop
  apply loop.spec_decr_nat (fun s => count.val - s.2.2.val)
    (fun s => s.2.2.val ≤ count.val ∧ ∃ entries, entries.length = s.2.2.val ∧
      ImportsAdded env entries s.1 ∧
      At (Rep ImportEncoding) data start (entries.map Module.Environment.rawImport) s.2.1 ∧
      Module.Environment.Bounded s.1 s.2.1.val)
  · rintro ⟨current, pos, i⟩ ⟨hi, entries, hlen, henv, hbytes, hbound⟩
    dsimp only at hi hlen henv hbytes hbound
    unfold metadata.decode_import_section_loop.body
    dsimp only
    split
    · rename_i hstop
      have heq : i.val = count.val := by scalar_tac
      exact ⟨entries, by omega, henv, hbytes, hbound⟩
    · rename_i hmore
      obtain ⟨⟨r, updated⟩, hr, hp⟩ := WP.spec_imp_exists (metadata.decode_import.spec data pos current hbound)
      simp only [hr, bind_ok]
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok next =>
        obtain ⟨entry, hadd, hb, hbound⟩ := hp
        simp [core.result.Result.Insts.CoreOpsTry.branch]
        step
        refine ⟨?_, ⟨entries ++ [entry], ?_, .snoc henv hadd, ?_, hbound⟩, ?_⟩
        · scalar_tac
        · simp only [List.length_append, List.length_singleton]; scalar_tac
        · simpa only [List.map_append, List.map_cons, List.map_nil] using hbytes.snoc hb
        · scalar_tac
  · exact ⟨by simp, [], by simp, .nil,
      ⟨[], .nil, Body.Scalar.BytesAt.nil data start hstart⟩, hbound⟩

/-- `metadata.decode_import_section` adds the imports of a `VecEncoding ImportEncoding` span. -/
@[step]
theorem metadata.decode_import_section.spec (data : Slice U8) (pos : Usize) (env : metadata.Env)
    (hbound : Module.Environment.Bounded env pos.val) :
    metadata.decode_import_section data pos env ⦃ r => match r.1 with
      | .Ok next => ∃ entries, ImportsAdded env entries r.2 ∧
          At (VecEncoding ImportEncoding) data pos (entries.map Module.Environment.rawImport) next ∧
          Module.Environment.Bounded r.2 next.val
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hc⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
  cases r with
  | Err e => simp [metadata.decode_import_section, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
    obtain ⟨count, start⟩ := pair
    have hs := hc.span
    obtain ⟨⟨r, result⟩, hloop, hp⟩ := WP.spec_imp_exists
      (metadata.decode_import_section_loop.spec data env count start hs.2.2 (hbound.mono (by omega)))
    simp [metadata.decode_import_section, hr, core.result.Result.Insts.CoreOpsTry.branch]
    rw [hloop]
    cases r with
    | Err e => simp
    | Ok next =>
      obtain ⟨entries, hlen, henv, hb, hbound⟩ := hp
      exact ⟨entries, henv, At.vector hc hb (by simpa using hlen), hbound⟩

end Itasca

end

/-! ## Element -/

section

/-!
# Element section parser

`metadata.decode_element_section.spec` and its loop connect successful parsing
to `ElementsAdded`: exact vector bytes, valid elements and the corresponding
environment/function-reference additions. Completeness is in
`Module/Sections/DeclarationsComplete`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Module.Sections

/-- `result` is `env` with the elements `added` appended and their function references appended to
the declared functions. Nothing else changes. -/
def ElementsAdded (env result : metadata.Env) (added : List metadata.Element) : Prop :=
  result = { env with elements := result.elements, declared_funcs := result.declared_funcs } ∧
  result.elements.val = env.elements.val ++ added ∧
  result.declared_funcs.val = env.declared_funcs.val ++ added.flatMap Module.References.element

/-- An element is valid in the environment: its table, offset and initializers are valid. -/
abbrev ElementValid := Module.Segments.elementValid

end Itasca.Module.Sections

namespace Itasca

open Binary Module.Sections

private theorem element_valid_caches {env result entry}
    (h : ElementValid result entry)
    (hf : env.func_types = result.func_types) (hg : env.global_types = result.global_types)
    (hn : env.num_imported_globals = result.num_imported_globals)
    (ht : env.table_types = result.table_types) : ElementValid env entry := by
  obtain ⟨hm, hi⟩ := h
  constructor
  · cases hmode : entry.mode with
    | Passive | Declarative => trivial
    | Active index offset =>
      rw [hmode] at hm
      obtain ⟨hb, he, hv⟩ := hm
      exact ⟨by simpa [ht] using hb, by simpa [ht] using he, hv.same_caches hf hg hn⟩
  · intro value hv
    exact (hi value hv).same_caches hf hg hn

/-- The element loop adds `count` elements forming a `Rep` span, each `ElementValid`. -/
@[step]
theorem metadata.decode_element_section_loop.spec (data : Slice U8) (env : metadata.Env)
    (count : U32) (start : Usize) (hstart : start.val ≤ data.length)
    (hsize : env.elements.val.length ≤ start.val) (hrefs : env.declared_funcs.val.length ≤ start.val) :
    metadata.decode_element_section_loop data env count start 0#u32 ⦃ r => match r.1 with
      | .Ok next => ∃ added, added.length = count.val ∧ ElementsAdded env r.2 added ∧
          At (Rep ElementEncoding) data start (added.map Module.Environment.rawElement) next ∧
          (∀ entry ∈ added, ElementValid env entry) ∧ r.2.elements.val.length ≤ next.val ∧
          r.2.declared_funcs.val.length ≤ next.val
      | .Err _ => True ⦄ := by
  unfold metadata.decode_element_section_loop
  apply loop.spec_decr_nat (fun s => count.val - s.2.2.val)
    (fun s => s.2.2.val ≤ count.val ∧ ∃ added, added.length = s.2.2.val ∧
      ElementsAdded env s.1 added ∧
      At (Rep ElementEncoding) data start (added.map Module.Environment.rawElement) s.2.1 ∧
      (∀ entry ∈ added, ElementValid env entry) ∧ s.1.elements.val.length ≤ s.2.1.val ∧
      s.1.declared_funcs.val.length ≤ s.2.1.val)
  · rintro ⟨current, pos, i⟩ ⟨hi, added, hlen, henv, hbytes, hvalid, hsize, hrefs⟩
    dsimp only at hi hlen henv hbytes hvalid hsize hrefs
    unfold metadata.decode_element_section_loop.body
    dsimp only
    split
    · rename_i hstop
      have heq : i.val = count.val := by scalar_tac
      exact ⟨added, by omega, henv, hbytes, hvalid, hsize, hrefs⟩
    · rename_i hmore
      obtain ⟨⟨r, updated⟩, hr, hp⟩ := WP.spec_imp_exists
        (metadata.decode_element.spec data pos current hrefs)
      rw [hr]
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok pair =>
        obtain ⟨entry, next⟩ := pair
        obtain ⟨hb, hadded, hv, hbound, hprogress⟩ := hp
        dsimp only at hadded hbound
        have hspan := hb.span
        have hunchanged : updated.elements = current.elements := by rw [hadded.1]
        have hcapacity : updated.elements.val.length < Usize.max := by
          rw [hunchanged]
          scalar_tac
        have hentry : ElementValid env entry := by
          apply element_valid_caches hv <;> rw [henv.1]
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        step as ⟨elements, helements⟩
        step
        refine ⟨?_, ⟨added ++ [entry], ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
        · scalar_tac
        · simp only [List.length_append, List.length_singleton]; scalar_tac
        · refine ⟨?_, ?_, ?_⟩
          · rw [hadded.1, henv.1]
          · simp only [helements, hunchanged, henv.2.1, List.append_assoc]
          · simp only [hadded.2, henv.2.2, List.flatMap_append, List.flatMap_cons,
              List.flatMap_nil, List.append_nil, List.append_assoc]
        · simpa only [List.map_append, List.map_cons, List.map_nil, Module.Environment.rawElement]
            using hbytes.snoc hb
        · intro value hm
          rcases List.mem_append.mp hm with hm | hm
          · exact hvalid value hm
          · simpa [List.mem_singleton.mp hm] using hentry
        · simp only [helements, hunchanged, List.length_append, List.length_singleton]
          omega
        · exact hbound
        · scalar_tac
  · exact ⟨by simp, [], by simp, ⟨by cases env; rfl, by simp, by simp⟩,
      ⟨[], .nil, Body.Scalar.BytesAt.nil data start hstart⟩, by simp, hsize, hrefs⟩

/-- `metadata.decode_element_section` adds the elements of a `VecEncoding` span, each
`ElementValid`. -/
@[step]
theorem metadata.decode_element_section.spec (data : Slice U8) (pos : Usize) (env : metadata.Env)
    (hsize : env.elements.val.length ≤ pos.val) (hrefs : env.declared_funcs.val.length ≤ pos.val) :
    metadata.decode_element_section data pos env ⦃ r => match r.1 with
      | .Ok next => ∃ added, ElementsAdded env r.2 added ∧
          At (VecEncoding ElementEncoding) data pos (added.map Module.Environment.rawElement) next ∧
          (∀ entry ∈ added, ElementValid env entry) ∧ r.2.elements.val.length ≤ next.val ∧
          r.2.declared_funcs.val.length ≤ next.val
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hc⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
  cases r with
  | Err e => simp [metadata.decode_element_section, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
    obtain ⟨count, start⟩ := pair
    have hs := hc.span
    obtain ⟨⟨r, result⟩, hloop, hp⟩ := WP.spec_imp_exists
      (metadata.decode_element_section_loop.spec data env count start hs.2.2 (by omega) (by omega))
    simp [metadata.decode_element_section, hr, core.result.Result.Insts.CoreOpsTry.branch]
    rw [hloop]
    cases r with
    | Err e => simp
    | Ok next =>
      obtain ⟨added, hlen, henv, hb, ht, hsize, hrefs⟩ := hp
      exact ⟨added, henv, At.vector hc hb (by simpa using hlen), ht, hsize, hrefs⟩

end Itasca

end

/-! ## Tail -/

section

/-!
# Module tail parser

The tail is the input after the code section: custom sections, at most one data section, then
custom sections, running to EOF. `Module.Tail.Encoding` is its independent grammar and `Prefix` the
invariant of the parsing loop. `metadata.validate_tail_with.spec` shows that an accepted tail is an
`Encoding` span to EOF whose segments are valid and agree with the data count, for any visitor
whose custom-section hook returns normally (`HooksTotal`). `metadata.validate_tail.spec` is the
specialization to the empty visitor. Completeness is in `Module/Sections/TailComplete`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Module.Tail

open Binary

/-- Custom section sequences concatenate. -/
theorem customs_append {xs ys} (hx : CustomsEncoding xs) (hy : CustomsEncoding ys) :
    CustomsEncoding (xs ++ ys) := by
  induction hx with
  | nil => simpa using hy
  | cons h _ ih => simpa [List.append_assoc] using WebAssembly.Binary.CustomsEncodingWith.cons h ih

/-- The loop invariant: the bytes so far are custom sections plus at most one data section whose
segments are listed. The flag records whether the data section has occurred. -/
inductive Prefix :
    Bool → List Binary.Data → List U8 → Prop where
  | empty : Prefix false [] []
  | custom {seen segments before bytes} : Prefix seen segments before →
      CustomEncoding bytes → Prefix seen segments (before ++ bytes)
  | data {before bytes segments} : Prefix false [] before →
      SectionEncoding 11#u8 (VecEncoding DataEncoding) segments bytes →
      Prefix true segments (before ++ bytes)

/-- Before the data section, a prefix has no segments and is only custom sections. -/
theorem Prefix.not_seen {seen segments bytes} (h : Prefix seen segments bytes)
    (hs : seen = false) : segments = [] ∧ CustomsEncoding bytes := by
  induction h with
  | empty => exact ⟨rfl, .nil⟩
  | custom _ hc ih =>
    obtain ⟨he, hp⟩ := ih hs
    exact ⟨he, by simpa using customs_append hp (.cons hc .nil)⟩
  | data => cases hs

/-- The independent grammar of the tail: padded data section (custom sections, then an optional
data section) followed by custom sections. -/
def Encoding (segments : List Binary.Data) (bytes : List U8) : Prop :=
  ∃ chunk customs, PaddedEncoding 11#u8 (VecEncoding DataEncoding) [] segments chunk ∧
    CustomsEncoding customs ∧ bytes = chunk ++ customs

/-- A prefix is a tail encoding. -/
theorem Prefix.encoding {seen segments bytes} (h : Prefix seen segments bytes) :
    Encoding segments bytes := by
  induction h with
  | empty => exact ⟨[], [], ⟨[], [], .nil, .absent, rfl⟩, .nil, rfl⟩
  | custom _ hc ih =>
    obtain ⟨chunk, customs, hs, ht, he⟩ := ih
    exact ⟨chunk, _, hs, (by simpa using customs_append ht (.cons hc .nil)), by simp [he, List.append_assoc]⟩
  | data hp hd =>
    exact ⟨_, [], ⟨_, _, (hp.not_seen rfl).2, .present hd, rfl⟩, .nil, by simp⟩

/-- A section header and its payload span form a section encoding. -/
theorem header_payload {α : Type} {R : α → List U8 → Prop} {data start id first last value}
    (hh : SectionHeader data start id first last)
    (hp : At R data first value last) :
    At (SectionEncoding id R) data start value last := by
  obtain ⟨pos, size, hb, hd, he, hend⟩ := hh
  obtain ⟨payload, hp, hs⟩ := hp
  obtain ⟨sizeBytes, hd, hl, hn, hc⟩ := hd
  have hlen : payload.length = size.val := by have := hs.length; omega
  have hsize : Body.Scalar.BytesAt data pos sizeBytes first := ⟨hd, hl, hn⟩
  refine ⟨id :: (sizeBytes ++ payload), ⟨sizeBytes, payload, ?_, hp, rfl⟩, ?_⟩
  · simpa [hlen] using hc
  · simpa using hb.byte.append (hsize.append hs)

/-- A custom section header and a name within it form a `CustomEncoding` span. -/
theorem custom_encoded {data start first last nm} {custom : wasm_types.CustomSection}
    (hh : SectionHeader data start 0#u8 first last)
    (hn : At NameEncoding data first nm custom.payload_start)
    (hp : custom.payload_start.val ≤ last.val) :
    At (fun (_ : Unit) => CustomEncoding) data start () last := by
  obtain ⟨payload, _, hs⟩ := WP.spec_imp_exists
    (metadata.copy_bytes.spec data custom.payload_start last hp hh.span.2.2)
  obtain ⟨nameBytes, hn, hns⟩ := hn
  have hpayload : At (fun (_ : Unit) bs => bs = nameBytes ++ payload.val) data first () last :=
    ⟨nameBytes ++ payload.val, rfl, hns.append hs⟩
  obtain ⟨bytes, he, hb⟩ := header_payload hh hpayload
  exact ⟨bytes, ⟨nm, payload.val, nameBytes, hn, he⟩, hb⟩

/-- A custom section extends a tail prefix. -/
theorem append_custom {seen segments data start pos next}
    (hp : At (fun segments bytes => Prefix seen segments bytes) data start segments pos)
    (hc : At (fun (_ : Unit) => CustomEncoding) data pos () next) :
    At (fun segments bytes => Prefix seen segments bytes) data start segments next := by
  obtain ⟨before, hp, hs⟩ := hp
  obtain ⟨bytes, hc, ht⟩ := hc
  exact ⟨before ++ bytes, .custom hp hc, hs.append ht⟩

/-- A data section extends a prefix that has not seen one. -/
theorem append_data {old segments data start pos next}
    (hp : At (fun segments bytes => Prefix false segments bytes) data start old pos)
    (hd : At (SectionEncoding 11#u8 (VecEncoding DataEncoding)) data pos segments next) :
    At (fun segments bytes => Prefix true segments bytes) data start segments next := by
  obtain ⟨before, hp, hs⟩ := hp
  obtain ⟨bytes, hd, ht⟩ := hd
  have he := (hp.not_seen rfl).1
  subst old
  exact ⟨before ++ bytes, .data hp hd, hs.append ht⟩

/-- The empty module visitor has total hooks. -/
theorem empty_hooks_total : HooksTotal metadata.DefaultModuleVisitor.Insts.ItascaMetadataModuleVisitor := by
  intro v chunk
  exact ⟨(.Ok (), v), rfl⟩

end Itasca.Module.Tail

namespace Itasca

/-- `metadata.validate_tail_with` consumes the input to EOF as custom sections around at most one data
section. An accepted tail is an `Encoding` span with valid segments that agree with the data
count. Hooks may reject. -/
theorem metadata.validate_tail_with.spec {V : Type} (visitor : metadata.ModuleVisitor V)
    (htotal : Module.Tail.HooksTotal visitor) (data : Slice U8) (start : Usize)
    (env : metadata.Env) (v : V) (hstart : start.val ≤ data.length) :
    metadata.validate_tail_with visitor data start env v ⦃ r => match r.1 with
      | .Ok tail => Binary.At (fun segments bytes => Module.Tail.Encoding segments bytes) data start
          (tail.data.val.map Module.Data.raw) (Slice.len data) ∧
          (∀ segment ∈ tail.data.val, Module.Data.Valid env segment) ∧
          ∀ count, env.data_count = some count → count.val = tail.data.val.length
      | .Err _ => True ⦄ := by
  unfold metadata.validate_tail_with metadata.validate_tail_with_loop
  apply loop.spec_decr_nat (fun s => data.length - s.2.2.1.val)
    (fun s => Binary.At (fun segments bytes => Module.Tail.Prefix s.2.2.2 segments bytes) data start
        (s.2.1.val.map Module.Data.raw) s.2.2.1 ∧
      ∀ segment ∈ s.2.1.val, Module.Data.Valid env segment)
  · rintro ⟨state, segments, pos, seen⟩ ⟨hbytes, hvalid⟩
    dsimp only at hbytes hvalid
    have hpos : pos.val ≤ data.length := hbytes.span.2
    unfold metadata.validate_tail_with_loop.body
    dsimp only
    split
    · rename_i hstop
      have heq : pos = Slice.len data := by apply UScalar.eq_of_val_eq; scalar_tac
      obtain ⟨bytes, hp, hs⟩ := hbytes
      cases hcount : env.data_count with
      | none =>
        simp only [WP.spec_ok]
        exact ⟨⟨bytes, hp.encoding, heq ▸ hs⟩, hvalid, by simp⟩
      | some count =>
        step
        split
        · simp
        · simp only [WP.spec_ok]
          refine ⟨⟨bytes, hp.encoding, heq ▸ hs⟩, hvalid, ?_⟩
          intro other ho
          have he : other = count := Option.some.inj ho.symm
          subst other
          scalar_tac
    · rename_i hmore
      have hlt : pos.val < data.length := by scalar_tac
      obtain ⟨r, hr, hh⟩ := WP.spec_imp_exists (metadata.read_section_header.spec data pos)
      rw [hr]
      cases r with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok triple =>
        rcases triple with ⟨id, first, last⟩
        change Binary.SectionHeader data pos id first last at hh
        have hspan := hh.span
        simp [core.result.Result.Insts.CoreOpsTry.branch]
        by_cases hc : id = metadata.SECTION_CUSTOM
        · simp only [hc, ↓reduceIte]
          obtain ⟨r, hcustom, hp⟩ := WP.spec_imp_exists (metadata.decode_custom_section.spec data first last)
          rw [hcustom]
          cases r with
          | Err e =>
            simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          | Ok custom =>
            obtain ⟨nm, hn, hbefore, hend, _⟩ := hp
            have hb := Module.Tail.custom_encoded (by simpa [hc, metadata.SECTION_CUSTOM] using hh) hn hbefore
            obtain ⟨⟨res, state'⟩, hvisit⟩ := htotal state custom
            simp [hvisit]
            cases res with
            | Err e => simp
            | Ok u =>
              exact ⟨Module.Tail.append_custom hbytes hb, hvalid, by scalar_tac⟩
        · simp only [hc, ↓reduceIte]
          by_cases hd : id = metadata.SECTION_DATA
          · subst id
            simp only [↓reduceIte]
            cases seen with
            | true => simp
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte]
              obtain ⟨r, hdata, hp⟩ := WP.spec_imp_exists (metadata.decode_data_section.spec data first env)
              rw [hdata]
              cases r with
              | Err e =>
                simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
              | Ok pair =>
                rcases pair with ⟨decoded, next⟩
                obtain ⟨hencoded, htyped⟩ := hp
                simp
                by_cases he : next = last
                · subst next
                  simp only [↓reduceIte, WP.spec_ok]
                  have hb := Module.Tail.header_payload hh hencoded
                  exact ⟨Module.Tail.append_data hbytes (by simpa [metadata.SECTION_DATA] using hb), htyped, by scalar_tac⟩
                · have hn : next.val ≠ last.val := fun h => he (UScalar.eq_of_val_eq h)
                  simp [hn]
          · have hn : id.val ≠ metadata.SECTION_DATA.val := fun h => hd (UScalar.eq_of_val_eq h)
            simp [hn]
  · refine ⟨?_, by simp [alloc.vec.Vec.new]⟩
    exact ⟨[], .empty, Body.Scalar.BytesAt.nil data start hstart⟩

/-- `metadata.validate_tail` satisfies the same specification as `metadata.validate_tail_with`. -/
theorem metadata.validate_tail.spec (data : Slice U8) (start : Usize) (env : metadata.Env)
    (hstart : start.val ≤ data.length) :
    metadata.validate_tail data start env ⦃ r => match r with
      | .Ok tail => Binary.At (fun segments bytes => Module.Tail.Encoding segments bytes) data start
          (tail.data.val.map Module.Data.raw) (Slice.len data) ∧
          (∀ segment ∈ tail.data.val, Module.Data.Valid env segment) ∧
          ∀ count, env.data_count = some count → count.val = tail.data.val.length
      | .Err _ => True ⦄ := by
  obtain ⟨⟨r, state⟩, hr, hp⟩ := WP.spec_imp_exists
    (metadata.validate_tail_with.spec metadata.DefaultModuleVisitor.Insts.ItascaMetadataModuleVisitor
      Module.Tail.empty_hooks_total data start env () hstart)
  simpa [metadata.validate_tail, hr] using hp

end Itasca

end

end
