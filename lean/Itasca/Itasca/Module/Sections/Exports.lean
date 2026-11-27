import Itasca.Module.Sections.Headers
import Itasca.Module.Readers.Completeness

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
theorem metadata.export_name_taken.spec (env : metadata.ModuleMetadata metadata.CodeMetadata) (nm : Slice U8) :
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

/-- The named descriptor is the only descriptor changed by marking an export. -/
def Marked (env after : metadata.CodeMetadata) : metadata.ExportDesc → Prop
  | .Func idx => ∃ d, env.funcs.val[idx.val]? = some d ∧
      after = { env with funcs := env.funcs.set (UScalar.cast .Usize idx) { d with can_ref_func := true, eager := true } }
  | .Table idx => ∃ d, env.tables.val[idx.val]? = some d ∧
      after = { env with tables := env.tables.set (UScalar.cast .Usize idx) { d with is_exported := true } }
  | .Memory idx => ∃ d, env.memories.val[idx.val]? = some d ∧
      after = { env with memories := env.memories.set (UScalar.cast .Usize idx) { d with is_exported := true } }
  | .Global idx => ∃ d, env.globals.val[idx.val]? = some d ∧
      after = { env with globals := env.globals.set (UScalar.cast .Usize idx) { d with is_exported := true } }

def ExportAdded (env result : metadata.ModuleMetadata metadata.CodeMetadata) (entry : metadata.Export) : Prop :=
  result = { env with code := result.code, exports := result.exports } ∧
  result.exports.val = env.exports.val ++ [entry] ∧
  entry.name.val ∉ env.exports.val.map (fun e => e.name.val) ∧ Marked env.code result.code entry.desc

/-- `result` is `initial` after adding `entries` one at a time by `ExportAdded`. -/
inductive ExportsAdded (initial : metadata.ModuleMetadata metadata.CodeMetadata) : List metadata.Export → metadata.ModuleMetadata metadata.CodeMetadata → Prop where
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
    result = { env with exports := result.exports, code := result.code } := by
  induction h with
  | nil => cases env; rfl
  | snoc _ ha ih => rw [ha.1, ih]

/-- The binary kind byte of an export descriptor. -/
def descByte : metadata.ExportDesc → U8
  | .Func _ => 0#u8 | .Table _ => 1#u8 | .Memory _ => 2#u8 | .Global _ => 3#u8

/-- The index of an export descriptor. -/
def descIndex : metadata.ExportDesc → U32
  | .Func idx | .Table idx | .Memory idx | .Global idx => idx

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

/-- The kind and index identify the marked descriptor. -/
@[step] theorem metadata.mark_exported.spec (env : metadata.CodeMetadata) (kind : U8) (idx : U32) :
    metadata.mark_exported env kind idx ⦃ r => match r.1 with
      | .Ok desc => kind = descByte desc ∧ idx = descIndex desc ∧ Marked env r.2 desc
      | .Err _ => True ⦄ := by
  unfold metadata.mark_exported
  step as ⟨i, hi⟩
  subst i
  split <;> step* <;> simp_all [descByte, descIndex, Marked, alloc.vec.Vec.set,
    List.getElem?_eq_getElem, List.set_set, List.getElem_set]
  all_goals first | scalar_tac | exact ⟨rfl, _, List.getElem?_eq_getElem (by scalar_tac), rfl⟩

/-- The start section marks its nullary, result-free function as eager. -/
@[step] theorem metadata.decode_start_section.spec (data : Slice U8) (start : Usize) (env : metadata.CodeMetadata)
    (valid : ∀ d ∈ env.funcs.val, d.type_index.val < env.types.val.length) :
    metadata.decode_start_section data start env ⦃ r => match r.1 with
      | .Ok next => ∃ idx d ft, Binary.At Binary.StartEncoding data start (some idx) next ∧
          env.funcs.val[idx.val]? = some d ∧ env.types.val[d.type_index.val]? = some ft ∧
          ft.params.val = [] ∧ ft.results.val = [] ∧
          r.2 = { env with start := some idx, funcs := env.funcs.set (UScalar.cast .Usize idx) {d with eager := true} }
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hd⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data start)
  cases r with
  | Err e => simp [metadata.decode_start_section, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
    obtain ⟨idx,next⟩ := pair
    simp [metadata.decode_start_section, hr, core.result.Result.Insts.CoreOpsTry.branch, lift]
    split
    · simp
    · have hi : idx.val < env.funcs.val.length := by scalar_tac
      have ht := valid _ (List.getElem_mem hi)
      step as ⟨d,hd'⟩
      have htype : d.type_index.val < env.types.val.length := by simpa [hd'] using ht
      step as ⟨ft,hft⟩
      simp [alloc.vec.Vec.is_empty]
      split_ifs <;> try simp
      step*
      obtain ⟨bytes, hs, hl, hb, he⟩ := hd
      refine ⟨idx, ⟨bytes, ⟨idx,rfl,he⟩, hs,hl,hb⟩, d, ?_, ft, ?_⟩
      all_goals simp_all [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem htype, alloc.vec.Vec.set]

end Itasca

namespace Itasca

open Binary Module.Sections

attribute [local simp] core.result.Result.Insts.CoreOpsTry.branch
  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
  error.Error.Insts.CoreConvertFromOpError.from

private theorem export_step (data : Slice U8) (count : U32) (env : metadata.ModuleMetadata metadata.CodeMetadata)
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
                  obtain ⟨⟨r, cm⟩, hd, hdesc⟩ := WP.spec_imp_exists (metadata.mark_exported.spec env.code kind idx)
                  cases r with
                  | Err e => simp [metadata.decode_export_section_loop.body, hmore, hn, ht, hk, hu, hd]
                  | Ok desc =>
                      obtain ⟨hbyte, hidx, marked⟩ := hdesc
                      have he := export_encoded hname hkind hindex hbyte hidx
                      have hs := hname.span
                      have hs' := hkind.span
                      have hs'' := hindex.span
                      have hsize := hbound.exports
                      have hcapacity : env.exports.val.length < Usize.max := by scalar_tac
                      simp [metadata.decode_export_section_loop.body, hmore, hn, ht, hk, hu, hd]
                      step as ⟨exports, hpush⟩
                      step as ⟨j,hj⟩
                      refine ⟨⟨nm,desc⟩, ⟨rfl,hpush,hfresh,marked⟩, he, ?_, hj⟩
                      cases desc <;> obtain ⟨d, _, rfl⟩ := marked <;>
                        cases hbound <;> constructor <;> simp [hpush, alloc.vec.Vec.set] <;> omega

/-- The export loop adds `count` exports forming a `Rep ExportEncoding` span, each with a fresh
name and valid descriptor. -/
theorem metadata.decode_export_section_loop.spec (data : Slice U8) (env : metadata.ModuleMetadata metadata.CodeMetadata)
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
theorem metadata.decode_export_section.spec (data : Slice U8) (start : Usize) (env : metadata.ModuleMetadata metadata.CodeMetadata)
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
