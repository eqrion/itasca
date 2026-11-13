import Itasca.Module.Env.Declarations
import Itasca.Module.Sections.ElementHeader
import Itasca.Module.Readers.TypesComplete
import Itasca.Module.Elab.SegmentTyping
import Itasca.Module.Readers.Types
import Itasca.Module.Const.Parser
import Itasca.Module.Readers.Utf8

/-!
Sections, each formerly its own module: Export, Memory, Table, Data.
-/

/-! ## Export -/

section

/-!
# Export and start section parsers

Soundness of `metadata.decode_export_section` and `metadata.decode_start_section`. `ExportsAdded` says
the environment gains the exports in order, each with a fresh name, an in-range index and the
function references it declares. The decoded span is a `VecEncoding ExportEncoding`. An accepted
start section names a function without parameters or results. Completeness is in
`Module/Sections/ExportComplete`.
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

namespace Itasca.ModuleSections

/-- `result` is `env` with `entry` appended to the exports, under a fresh name with a resolvable
descriptor, and its function references appended to the declared functions. Nothing else
changes. -/
def ExportAdded (env result : metadata.Env) (entry : metadata.Export) : Prop :=
  result = { env with exports := result.exports, declared_funcs := result.declared_funcs } ∧
  result.exports.val = env.exports.val ++ [entry] ∧
  entry.name.val ∉ env.exports.val.map (fun e => e.name.val) ∧
  (∃ xt, ModuleExternals.ExportResolves env entry xt) ∧
  result.declared_funcs.val = env.declared_funcs.val ++ ModuleReferences.exportIndices entry

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
    ∃ xt, ModuleExternals.ExportResolves env ⟨nm, desc⟩ xt := by
  cases desc with
  | Func idx => exact ⟨.Func env.func_types.val[idx.val], h, rfl⟩
  | Table idx => exact ⟨.Table env.table_types.val[idx.val], h, rfl⟩
  | Memory idx => exact ⟨.Memory env.mem_types.val[idx.val], h, rfl⟩
  | Global idx => exact ⟨.Global env.global_types.val[idx.val], h, rfl⟩

/-- A kind byte followed by the index encoding is an `ExportDescEncoding`. -/
theorem exportDesc_encoded (desc : metadata.ExportDesc) {bytes}
    (h : ModuleBinary.IndexEncoding (descIndex desc) bytes) :
    ModuleBinary.ExportDescEncoding desc (descByte desc :: bytes) := by
  cases desc with
  | Func idx => exact .func idx h
  | Table idx => exact .table idx h
  | Memory idx => exact .memory idx h
  | Global idx => exact .global idx h

/-- A name, a kind byte and an index in sequence form an `ExportEncoding`. -/
theorem export_encoded {data start p1 p2 next nm kind idx desc}
    (hn : ModuleBinary.At ModuleBinary.NameEncoding data start nm p1)
    (hk : ModuleBinary.At ModuleBinary.ByteEncoding data p1 kind p2)
    (hd : Leb128.Decoded data p2 idx next)
    (hkind : kind = descByte desc) (hindex : idx = descIndex desc) :
    ModuleBinary.At ModuleBinary.ExportEncoding data start ⟨nm, desc⟩ next := by
  obtain ⟨nameBytes, hname, hs⟩ := hn
  obtain ⟨indexBytes, hs', hl', hb', hidx⟩ := hd
  have he : ModuleBinary.ExportDescEncoding desc (kind :: indexBytes) := by
    rw [hkind]
    exact exportDesc_encoded desc (by simpa [ModuleBinary.IndexEncoding, hindex] using hidx)
  exact ⟨nameBytes ++ (kind :: indexBytes),
    ⟨nameBytes, kind :: indexBytes, hname, he, rfl⟩,
    hs.append (by simpa using (ModuleBinary.At.byte hk).append ⟨hs', hl', hb'⟩)⟩

end Itasca.ModuleSections

namespace Itasca

open ModuleSections

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
      | .Ok next => ∃ idx, ModuleBinary.At ModuleBinary.StartEncoding data start (some idx) next ∧
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

open ModuleBinary ModuleSections

attribute [local simp] core.result.Result.Insts.CoreOpsTry.branch
  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
  error.Error.Insts.CoreConvertFromOpError.from

private theorem export_step (data : Slice U8) (count : U32) (env : metadata.Env)
    (pos : Usize) (i : U32) (hi : i.val < count.val) (hbound : ModuleEnv.Bounded env pos.val) :
    metadata.decode_export_section_loop.body data count env pos i ⦃ r => match r with
      | .done (.Err _, _) => True
      | .done (.Ok _, _) => False
      | .cont (result, next, j) => ∃ entry, ExportAdded env result entry ∧
          At ExportEncoding data pos (ModuleEnv.rawExport entry) next ∧
          ModuleEnv.Bounded result next.val ∧ j.val = i.val + 1 ⦄ := by
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
                        · simp_all only [ModuleReferences.exportIndices, List.append_nil]
                        · cases hbound
                          constructor <;>
                            simp_all only [List.length_append, List.length_singleton] <;> omega
                        · scalar_tac

/-- The export loop adds `count` exports forming a `Rep ExportEncoding` span, each with a fresh
name and valid descriptor. -/
theorem metadata.decode_export_section_loop.spec (data : Slice U8) (env : metadata.Env)
    (count : U32) (start : Usize) (hstart : start.val ≤ data.length)
    (hbound : ModuleEnv.Bounded env start.val) :
    metadata.decode_export_section_loop data env count start 0#u32 ⦃ r => match r.1 with
      | .Ok next => ∃ entries, entries.length = count.val ∧ ExportsAdded env entries r.2 ∧
          At (Rep ExportEncoding) data start (entries.map ModuleEnv.rawExport) next ∧
          ModuleEnv.Bounded r.2 next.val
      | .Err _ => True ⦄ := by
  unfold metadata.decode_export_section_loop
  apply loop.spec_decr_nat (fun s => count.val - s.2.2.val)
    (fun s => s.2.2.val ≤ count.val ∧ ∃ entries, entries.length = s.2.2.val ∧
      ExportsAdded env entries s.1 ∧
      At (Rep ExportEncoding) data start (entries.map ModuleEnv.rawExport) s.2.1 ∧
      ModuleEnv.Bounded s.1 s.2.1.val)
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
  · exact ⟨by simp, [], by simp, .nil, ⟨[], .nil, Wasm1.BytesAt.nil data start hstart⟩, hbound⟩

/-- `metadata.decode_export_section` adds the exports of a `VecEncoding ExportEncoding` span, each
with a fresh name and valid descriptor. -/
@[step]
theorem metadata.decode_export_section.spec (data : Slice U8) (start : Usize) (env : metadata.Env)
    (hbound : ModuleEnv.Bounded env start.val) :
    metadata.decode_export_section data start env ⦃ r => match r.1 with
      | .Ok next => ∃ entries, ExportsAdded env entries r.2 ∧
          At (VecEncoding ExportEncoding) data start (entries.map ModuleEnv.rawExport) next ∧
          ModuleEnv.Bounded r.2 next.val
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
Completeness is in `Module/Sections/MemoryComplete`.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleBinary

/-- A memory type encoding consumes at least one byte. -/
theorem At.memType_progress {data start ty next} (h : At MemTypeEncoding data start ty next) :
    start.val < next.val := by
  obtain ⟨bytes, he, hs⟩ := h
  change LimitsEncoding ty.limits bytes at he
  generalize ty.limits = lim at he
  cases he <;> have := hs.length <;> simp only [List.length_cons, List.length_append] at this <;> omega

end Itasca.ModuleBinary

namespace Itasca.ModuleSections

/-- `result` is `env` with the memory types `added` appended and nothing else changed. -/
def MemoriesAdded (env result : metadata.Env) (added : List wasm_types.MemType) : Prop :=
  result = { env with mem_types := result.mem_types } ∧ result.mem_types.val = env.mem_types.val ++ added

end Itasca.ModuleSections

namespace Itasca

open ModuleBinary ModuleSections

/-- The memory loop adds `count` memory types forming a `Rep MemTypeEncoding` span with valid
limits. -/
@[step]
theorem metadata.decode_memory_section_loop.spec (data : Slice U8) (env : metadata.Env)
    (count : U32) (start : Usize) (hstart : start.val ≤ data.length)
    (hsize : env.mem_types.val.length ≤ start.val) :
    metadata.decode_memory_section_loop data env count start 0#u32 ⦃ r => match r.1 with
      | .Ok next => ∃ added, added.length = count.val ∧ MemoriesAdded env r.2 added ∧
          At (Rep MemTypeEncoding) data start added next ∧
          (∀ ft ∈ added, ModuleTranslation.LimitsValid ft.limits (2 ^ 16)) ∧ r.2.mem_types.val.length ≤ next.val ∧
          r.2.mem_types.val.length ≤ max env.mem_types.val.length 1
      | .Err _ => True ⦄ := by
  unfold metadata.decode_memory_section_loop
  apply loop.spec_decr_nat (fun s => count.val - s.2.2.val)
    (fun s => s.2.2.val ≤ count.val ∧ ∃ added, added.length = s.2.2.val ∧
      MemoriesAdded env s.1 added ∧ At (Rep MemTypeEncoding) data start added s.2.1 ∧
      (∀ ft ∈ added, ModuleTranslation.LimitsValid ft.limits (2 ^ 16)) ∧ s.1.mem_types.val.length ≤ s.2.1.val ∧
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
        have hprogress := hb.memType_progress
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
            · simpa [List.mem_singleton.mp hm, ModuleTranslation.LimitsValid, ModuleBinary.LimitsValid,
                Option.mem_def, global_simps, U32.rMax] using ht
          · simp only [r_post, List.length_append, List.length_singleton]; omega
          · have hx : r.val.length ≤ 1 := by simpa [global_simps] using hmax
            exact hx.trans (Nat.le_max_right _ _)
          · scalar_tac
  · exact ⟨by simp, [], by simp, ⟨by cases env; rfl, by simp⟩,
      ⟨[], .nil, Wasm1.BytesAt.nil data start hstart⟩, by simp, hsize, Nat.le_max_left _ _⟩

/-- `metadata.decode_memory_section` adds the memory types of a `VecEncoding MemTypeEncoding` span
with valid limits. -/
@[step]
theorem metadata.decode_memory_section.spec (data : Slice U8) (pos : Usize) (env : metadata.Env)
    (hsize : env.mem_types.val.length ≤ pos.val) :
    metadata.decode_memory_section data pos env ⦃ r => match r.1 with
      | .Ok next => ∃ added, MemoriesAdded env r.2 added ∧
          At (VecEncoding MemTypeEncoding) data pos added next ∧
          (∀ ft ∈ added, ModuleTranslation.LimitsValid ft.limits (2 ^ 16)) ∧ r.2.mem_types.val.length ≤ next.val ∧
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
within the table cap. Completeness is in `Module/Sections/TableComplete`.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleBinary

/-- A table type encoding consumes at least one byte. -/
theorem At.tableType_progress {data start ty next} (h : At TableTypeEncoding data start ty next) :
    start.val < next.val := by
  obtain ⟨bytes, he, hs⟩ := h
  obtain ⟨limits, _, rfl⟩ := he
  have := hs.length
  simp only [List.length_cons] at this
  omega

end Itasca.ModuleBinary

namespace Itasca.ModuleSections

/-- `result` is `env` with the table types `added` appended and nothing else changed. -/
def TablesAdded (env result : metadata.Env) (added : List wasm_types.TableType) : Prop :=
  result = { env with table_types := result.table_types } ∧ result.table_types.val = env.table_types.val ++ added

end Itasca.ModuleSections

namespace Itasca

open ModuleBinary ModuleSections

/-- The table loop adds `count` table types forming a `Rep TableTypeEncoding` span, with valid
limits. -/
@[step]
theorem metadata.decode_table_section_loop.spec (data : Slice U8) (env : metadata.Env)
    (count : U32) (start : Usize) (hstart : start.val ≤ data.length)
    (hsize : env.table_types.val.length ≤ start.val) :
    metadata.decode_table_section_loop data env count start 0#u32 ⦃ r => match r.1 with
      | .Ok next => ∃ added, added.length = count.val ∧ TablesAdded env r.2 added ∧
          At (Rep TableTypeEncoding) data start added next ∧
          (∀ ft ∈ added, ModuleTranslation.LimitsValid ft.limits (2 ^ 32 - 1)) ∧ r.2.table_types.val.length ≤ next.val
      | .Err _ => True ⦄ := by
  unfold metadata.decode_table_section_loop
  apply loop.spec_decr_nat (fun s => count.val - s.2.2.val)
    (fun s => s.2.2.val ≤ count.val ∧ ∃ added, added.length = s.2.2.val ∧
      TablesAdded env s.1 added ∧ At (Rep TableTypeEncoding) data start added s.2.1 ∧
      (∀ ft ∈ added, ModuleTranslation.LimitsValid ft.limits (2 ^ 32 - 1)) ∧ s.1.table_types.val.length ≤ s.2.1.val)
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
        have hprogress := hb.tableType_progress
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
          · simpa [List.mem_singleton.mp hm, ModuleTranslation.LimitsValid, ModuleBinary.LimitsValid,
              Option.mem_def, global_simps, U32.rMax] using ht
        · simp only [r_post, List.length_append, List.length_singleton]; omega
        · scalar_tac
  · exact ⟨by simp, [], by simp, ⟨by cases env; rfl, by simp⟩,
      ⟨[], .nil, Wasm1.BytesAt.nil data start hstart⟩, by simp, hsize⟩

/-- `metadata.decode_table_section` adds the table types of a `VecEncoding TableTypeEncoding` span,
with valid limits. -/
@[step]
theorem metadata.decode_table_section.spec (data : Slice U8) (pos : Usize) (env : metadata.Env)
    (hsize : env.table_types.val.length ≤ pos.val) :
    metadata.decode_table_section data pos env ⦃ r => match r.1 with
      | .Ok next => ∃ added, TablesAdded env r.2 added ∧
          At (VecEncoding TableTypeEncoding) data pos added next ∧
          (∀ ft ∈ added, ModuleTranslation.LimitsValid ft.limits (2 ^ 32 - 1)) ∧ r.2.table_types.val.length ≤ next.val
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
(`DataEncodingFor`) and satisfy `ModuleData.Valid`,
which covers the memory index and the offset initializer of active segments. Completeness is in `Module/Sections/DataComplete`.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleData

/-- A repetition span extends by one segment at its end. -/
theorem at_snoc {R : ModuleBinary.Data → List U8 → Prop} {data start pos next values value}
    (h : ModuleBinary.At (ModuleBinary.Rep R) data start values pos)
    (h' : ModuleBinary.At R data pos value next) :
    ModuleBinary.At (ModuleBinary.Rep R) data start (values ++ [value]) next := by
  obtain ⟨bytes, hr, hs⟩ := h
  obtain ⟨last, he, ht⟩ := h'
  exact ⟨bytes ++ last, hr.snoc he, hs.append ht⟩

/-- Like `encoded`: a flag word and the index encoding give an active
`DataEncodingFor`. -/
theorem profile_encoded {data start first p1 p2 p3 next flags memory explicit offset count init}
    (hf : Leb128.Decoded data start flags first)
    (hm : ModuleBinary.At (fun pair => ModuleBinary.SegmentIndexEncoding flags pair.1 pair.2)
      data first (memory, explicit) p1)
    (ho : ModuleBinary.At ModuleBinary.ConstEncoding data p1 offset p2)
    (hc : Leb128.Decoded data p2 count p3)
    (hi : Wasm1.BytesAt data p3 init next) (hlen : init.length = count.val) :
    ModuleBinary.At (ModuleBinary.DataEncodingFor) data start
      ⟨.Active memory offset, init⟩ next := by
  obtain ⟨fb, hf, hfs⟩ := ModuleBinary.At.of_u32 hf
  obtain ⟨mb, hm, hms⟩ := hm
  obtain ⟨ob, ho, hos⟩ := ho
  obtain ⟨cb, hcs, hcl, hcb, hc⟩ := hc
  have hspan : Wasm1.BytesAt data p2 cb p3 := ⟨hcs, hcl, hcb⟩
  refine ⟨fb ++ mb ++ ob ++ (cb ++ init), ?_, ?_⟩
  · apply ModuleBinary.DataEncodingFor.of_parts hf hm ho
    exact ModuleBinary.ByteVecEncoding.iff.mpr ⟨cb, by simpa [hlen] using hc, rfl⟩
  · exact ((hfs.append hms).append hos).append (hspan.append hi)

/-- Flag `1` followed by a counted byte string is a passive Wasm 2.0 data segment. -/
theorem passive_encoded {data start first content next count init}
    (hf : Leb128.Decoded data start 1#u32 first)
    (hc : Leb128.Decoded data first count content)
    (hi : Wasm1.BytesAt data content init next) (hlen : init.length = count.val) :
    ModuleBinary.At (ModuleBinary.DataEncodingFor) data start ⟨.Passive, init⟩ next := by
  obtain ⟨fb, hf, hfs⟩ := ModuleBinary.At.of_u32 hf
  obtain ⟨cb, hcs, hcl, hcb, hc⟩ := hc
  have hcount : Wasm1.BytesAt data first cb content := ⟨hcs, hcl, hcb⟩
  exact ⟨fb ++ (cb ++ init), .passive hf
    (ModuleBinary.ByteVecEncoding.iff.mpr ⟨cb, by simpa [hlen] using hc, rfl⟩),
    hfs.append (hcount.append hi)⟩

end Itasca.ModuleData

namespace Itasca

/-- An accepted `metadata.decode_data_segment` is a `DataEncodingFor` span and its segment
is `ModuleData.Valid`. -/
@[step]
theorem metadata.decode_data_segment.profile_spec (data : Slice U8) (pos : Usize) (env : metadata.Env) :
    metadata.decode_data_segment data pos env ⦃ r => match r with
      | .Ok (segment, next) =>
          ModuleBinary.At (ModuleBinary.DataEncodingFor) data pos (ModuleData.raw segment) next ∧
          ModuleData.Valid env segment
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hm⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
  cases r with
  | Err e =>
    simp [metadata.decode_data_segment, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
    rcases pair with ⟨flags, first⟩
    change Leb128.Decoded data pos flags first at hm
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
          refine ⟨ModuleData.passive_encoded hm hc init_post ?_, trivial⟩
          have hl := init_post.length
          scalar_tac
    ·
      obtain ⟨r, hseg, hindex⟩ := WP.spec_imp_exists
        (metadata.decode_segment_index.profile_spec data first flags hm.span.2.2)
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
              change ModuleBinary.At ModuleBinary.ConstEncoding data p1 offset p2 ∧
                ModuleConstants.Valid env offset .I32 at ho
              obtain ⟨r, hlen, hc⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data p2)
              cases r with
              | Err e =>
                simp [hr, hlen, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                  error.Error.Insts.CoreConvertFromOpError.from]
              | Ok pair =>
                rcases pair with ⟨count, p3⟩
                change Leb128.Decoded data p2 count p3 at hc
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
                  refine ⟨ModuleData.profile_encoded hm hindex ho.1 hc init_post ?_, hmem, ho.2⟩
                  have hl := init_post.length
                  scalar_tac

/-- The data loop returns `count` segments forming a `Rep` span, all valid. -/
@[step]
theorem metadata.decode_data_section_loop.profile_spec (data : Slice U8) (env : metadata.Env)
    (count : U32) (start : Usize) (hstart : start.val ≤ data.length) :
    metadata.decode_data_section_loop data env count (alloc.vec.Vec.new _) start 0#u32 ⦃ r =>
      match r with
      | .Ok (segments, next) => segments.val.length = count.val ∧
          ModuleBinary.At (ModuleBinary.Rep (ModuleBinary.DataEncodingFor))
            data start (segments.val.map ModuleData.raw) next ∧
          ∀ segment ∈ segments.val, ModuleData.Valid env segment
      | .Err _ => True ⦄ := by
  unfold metadata.decode_data_section_loop
  apply loop.spec_decr_nat (fun s => count.val - s.2.2.val)
    (fun s => s.2.2.val ≤ count.val ∧ s.1.val.length = s.2.2.val ∧
      ModuleBinary.At (ModuleBinary.Rep (ModuleBinary.DataEncodingFor))
        data start (s.1.val.map ModuleData.raw) s.2.1 ∧
      ∀ segment ∈ s.1.val, ModuleData.Valid env segment)
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
      obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (metadata.decode_data_segment.profile_spec data pos env)
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
        · simpa [out1_post, List.map_append] using ModuleData.at_snoc hbytes hb
        · intro entry he
          rw [out1_post] at he
          rcases List.mem_append.mp he with he | he
          · exact hvalid entry he
          · simpa [List.mem_singleton.mp he] using ht
        · scalar_tac
  · refine ⟨by simp, by simp, ?_, by simp [alloc.vec.Vec.new]⟩
    exact ⟨[], .nil, Wasm1.BytesAt.nil data start hstart⟩

/-- An accepted `metadata.decode_data_section` returns segments forming a `VecEncoding` span, all
valid. -/
@[step]
theorem metadata.decode_data_section.profile_spec (data : Slice U8) (pos : Usize) (env : metadata.Env) :
    metadata.decode_data_section data pos env ⦃ r => match r with
      | .Ok (segments, next) =>
          ModuleBinary.At (ModuleBinary.VecEncoding (ModuleBinary.DataEncodingFor))
            data pos (segments.val.map ModuleData.raw) next ∧
          ∀ segment ∈ segments.val, ModuleData.Valid env segment
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hc⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
  cases r with
  | Err e =>
    simp [metadata.decode_data_section, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
    rcases pair with ⟨count, start⟩
    change Leb128.Decoded data pos count start at hc
    obtain ⟨r, hloop, hp⟩ := WP.spec_imp_exists
      (metadata.decode_data_section_loop.profile_spec data env count start hc.span.2.2)
    simp [metadata.decode_data_section, hr, core.result.Result.Insts.CoreOpsTry.branch]
    rw [hloop]
    cases r with
    | Err e => simp
    | Ok pair =>
      rcases pair with ⟨segments, next⟩
      obtain ⟨hlen, hbytes, hvalid⟩ := hp
      obtain ⟨bytes, he, hs⟩ := hbytes
      obtain ⟨countBytes, hcs, hcl, hcb, hce⟩ := hc
      have hcspan : Wasm1.BytesAt data pos countBytes start := ⟨hcs, hcl, hcb⟩
      refine ⟨⟨countBytes ++ bytes, ?_, hcspan.append hs⟩, hvalid⟩
      exact ⟨countBytes, bytes, by simpa [hlen] using hce, he, rfl⟩

end Itasca

end
