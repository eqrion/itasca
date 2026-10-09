import Itasca.ModuleDeclarations
import Itasca.ModuleSections
import Itasca.ModuleNames

open Aeneas Aeneas.Std

namespace Itasca

private theorem names_equal_loop_spec (a b : Slice U8) (i : Usize)
    (hlen : a.length = b.length) (hi : i.val ≤ a.length)
    (hprefix : a.val.take i.val = b.val.take i.val) :
    module.names_equal_loop a b i ⦃ result => result = true ↔ a.val = b.val ⦄ := by
  unfold module.names_equal_loop
  apply loop.spec_decr_nat (fun pos => a.length - pos.val)
    (fun pos => pos.val ≤ a.length ∧ a.val.take pos.val = b.val.take pos.val)
  · intro pos hp
    obtain ⟨hpos, heq⟩ := hp
    unfold module.names_equal_loop.body
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

/-- The byte-name comparison terminates and computes actual list equality. -/
@[step]
theorem module.names_equal.spec (a b : Slice U8) :
    module.names_equal a b ⦃ result => result = true ↔ a.val = b.val ⦄ := by
  unfold module.names_equal
  dsimp only
  split
  · rename_i hne
    simp only [WP.spec_ok, Bool.false_eq_true, false_iff]
    intro heq
    have hlen : a.length = b.length := congrArg List.length heq
    simp [hlen] at hne
  · rename_i heq
    exact names_equal_loop_spec a b 0#usize (by scalar_tac) (by simp) (by simp)

@[step]
theorem module.export_name_taken.spec (env : module.Env) (nm : Slice U8) :
    module.export_name_taken env nm ⦃ result =>
      result = true ↔ nm.val ∈ env.exports.val.map (fun entry => entry.name.val) ⦄ := by
  unfold module.export_name_taken module.export_name_taken_loop
  apply loop.spec_decr_nat (fun pos => env.exports.val.length - pos.val)
    (fun pos => pos.val ≤ env.exports.val.length ∧
      ∀ j (hj : j < env.exports.val.length), j < pos.val → env.exports.val[j].name.val ≠ nm.val)
  · intro pos hp
    obtain ⟨hpos, hprefix⟩ := hp
    unfold module.export_name_taken_loop.body
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

def ExportAdded (env result : module.Env) (entry : module.Export) : Prop :=
  result = { env with exports := result.exports } ∧
  result.exports.val = env.exports.val ++ [entry] ∧
  entry.name.val ∉ env.exports.val.map (fun e => e.name.val) ∧
  ∃ xt, ModuleExternals.ExportResolves env entry xt

inductive ExportsAdded (initial : module.Env) : List module.Export → module.Env → Prop where
  | nil : ExportsAdded initial [] initial
  | snoc {entries before after entry} : ExportsAdded initial entries before →
      ExportAdded before after entry → ExportsAdded initial (entries ++ [entry]) after

theorem ExportsAdded.exports {env entries result} (h : ExportsAdded env entries result) :
    result.exports.val = env.exports.val ++ entries := by
  induction h with
  | nil => simp
  | snoc _ ha ih => simpa [ih, List.append_assoc] using ha.2.1

theorem ExportsAdded.unchanged {env entries result} (h : ExportsAdded env entries result) :
    result = { env with exports := result.exports } := by
  induction h with
  | nil => cases env; rfl
  | snoc _ ha ih => rw [ha.1, ih]

def descByte : module.ExportDesc → U8
  | .Func _ => 0#u8 | .Table _ => 1#u8 | .Memory _ => 2#u8 | .Global _ => 3#u8

def descIndex : module.ExportDesc → U32
  | .Func idx | .Table idx | .Memory idx | .Global idx => idx

def ExportDescValid (env : module.Env) : module.ExportDesc → Prop
  | .Func idx => idx.val < env.func_types.val.length
  | .Table idx => idx.val < env.table_types.val.length
  | .Memory idx => idx.val < env.mem_types.val.length
  | .Global idx => idx.val < env.global_types.val.length

theorem ExportDescValid.resolves {env desc} (h : ExportDescValid env desc) (nm : alloc.vec.Vec U8) :
    ∃ xt, ModuleExternals.ExportResolves env ⟨nm, desc⟩ xt := by
  cases desc with
  | Func idx => exact ⟨.Func env.func_types.val[idx.val], h, rfl⟩
  | Table idx => exact ⟨.Table env.table_types.val[idx.val], h, rfl⟩
  | Memory idx => exact ⟨.Memory env.mem_types.val[idx.val], h, rfl⟩
  | Global idx => exact ⟨.Global env.global_types.val[idx.val], h, rfl⟩

theorem exportDesc_encoded (desc : module.ExportDesc) {bytes}
    (h : ModuleBinary.IndexEncoding (descIndex desc) bytes) :
    ModuleBinary.ExportDescEncoding desc (descByte desc :: bytes) := by
  cases desc with
  | Func idx => exact .func idx h
  | Table idx => exact .table idx h
  | Memory idx => exact .memory idx h
  | Global idx => exact .global idx h

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

@[step]
theorem module.export_desc.spec (env : module.Env) (kind : U8) (idx : U32) :
    module.export_desc env kind idx ⦃ r => match r with
      | .Ok desc => kind = descByte desc ∧ idx = descIndex desc ∧ ExportDescValid env desc
      | .Err _ => True ⦄ := by
  unfold module.export_desc
  step
  split <;> step* <;> simp_all [descByte, descIndex, ExportDescValid]
  all_goals with_unfolding_all rfl

/-- A successful start declaration names a nullary function with no result. -/
@[step]
theorem module.decode_start_section.spec (data : Slice U8) (start : Usize) (env : module.Env) :
    module.decode_start_section data start env ⦃ r => match r.1 with
      | .Ok next => ∃ idx, ModuleBinary.At ModuleBinary.StartEncoding data start (some idx) next ∧
          r.2 = { env with start := some idx } ∧
          ∃ hi : idx.val < env.func_types.val.length,
            env.func_types.val[idx.val].params.val = [] ∧ env.func_types.val[idx.val].results.val = []
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hd⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data start)
  cases r with
  | Err e =>
      simp [module.decode_start_section, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
      obtain ⟨idx, next⟩ := pair
      simp [module.decode_start_section, hr, core.result.Result.Insts.CoreOpsTry.branch]
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

private theorem export_step (data : Slice U8) (count : U32) (env : module.Env)
    (pos : Usize) (i : U32) (hi : i.val < count.val) (hbound : ModuleEnv.Bounded env pos.val) :
    module.decode_export_section_loop.body data count env pos i ⦃ r => match r with
      | .done (.Err _, _) => True
      | .done (.Ok _, _) => False
      | .cont (result, next, j) => ∃ entry, ExportAdded env result entry ∧
          At ExportEncoding data pos (ModuleEnv.rawExport entry) next ∧
          ModuleEnv.Bounded result next.val ∧ j.val = i.val + 1 ⦄ := by
  have hmore : ¬i ≥ count := by scalar_tac
  obtain ⟨r, hn, hname⟩ := WP.spec_imp_exists (module.decode_name.spec data pos)
  cases r with
  | Err e => simp [module.decode_export_section_loop.body, hmore, hn]
  | Ok pair =>
      obtain ⟨nm, p1⟩ := pair
      obtain ⟨taken, ht, htaken⟩ := WP.spec_imp_exists
        (module.export_name_taken.spec env (alloc.vec.Vec.deref nm))
      cases taken with
      | true => simp [module.decode_export_section_loop.body, hmore, hn, ht]
      | false =>
          have hfresh : nm.val ∉ env.exports.val.map (fun entry => entry.name.val) := by
            simpa [alloc.vec.Vec.deref] using htaken
          obtain ⟨r, hk, hkind⟩ := WP.spec_imp_exists (reader.read_byte.module_spec data p1)
          cases r with
          | Err e => simp [module.decode_export_section_loop.body, hmore, hn, ht, hk]
          | Ok pair =>
              obtain ⟨kind, p2⟩ := pair
              obtain ⟨r, hu, hindex⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data p2)
              cases r with
              | Err e => simp [module.decode_export_section_loop.body, hmore, hn, ht, hk, hu]
              | Ok pair =>
                  obtain ⟨idx, next⟩ := pair
                  obtain ⟨r, hd, hdesc⟩ := WP.spec_imp_exists (module.export_desc.spec env kind idx)
                  cases r with
                  | Err e => simp [module.decode_export_section_loop.body, hmore, hn, ht, hk, hu, hd]
                  | Ok desc =>
                      obtain ⟨hbyte, hidx, hvalid⟩ := hdesc
                      have he := export_encoded hname hkind hindex hbyte hidx
                      have hs := hname.span
                      have hs' := hkind.span
                      have hs'' := hindex.span
                      have hprogress : pos.val < next.val := by omega
                      have hsize := hbound.exports
                      have hcapacity : env.exports.val.length < Usize.max := by scalar_tac
                      simp [module.decode_export_section_loop.body, hmore, hn, ht, hk, hu, hd]
                      step*
                      refine ⟨⟨nm, desc⟩, ⟨rfl, ?_, hfresh, hvalid.resolves nm⟩, he, ?_, ?_⟩
                      · exact v_post
                      · cases hbound
                        constructor <;> simp only [v_post, List.length_append, List.length_singleton] <;> omega
                      · scalar_tac

theorem module.decode_export_section_loop.spec (data : Slice U8) (env : module.Env)
    (count : U32) (start : Usize) (hstart : start.val ≤ data.length)
    (hbound : ModuleEnv.Bounded env start.val) :
    module.decode_export_section_loop data env count start 0#u32 ⦃ r => match r.1 with
      | .Ok next => ∃ entries, entries.length = count.val ∧ ExportsAdded env entries r.2 ∧
          At (Rep ExportEncoding) data start (entries.map ModuleEnv.rawExport) next ∧
          ModuleEnv.Bounded r.2 next.val
      | .Err _ => True ⦄ := by
  unfold module.decode_export_section_loop
  apply loop.spec_decr_nat (fun s => count.val - s.2.2.val)
    (fun s => s.2.2.val ≤ count.val ∧ ∃ entries, entries.length = s.2.2.val ∧
      ExportsAdded env entries s.1 ∧
      At (Rep ExportEncoding) data start (entries.map ModuleEnv.rawExport) s.2.1 ∧
      ModuleEnv.Bounded s.1 s.2.1.val)
  · rintro ⟨current, pos, i⟩ ⟨hi, entries, hlen, hhistory, hbytes, hbound⟩
    dsimp only at *
    by_cases hdone : count.val ≤ i.val
    · have he : i ≥ count := by scalar_tac
      simp [module.decode_export_section_loop.body, he]
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
  · exact ⟨by simp, [], by simp, .nil, ⟨[], .nil, Wasm.BytesAt.nil data start hstart⟩, hbound⟩

/-- The export section enforces fresh names and valid indices as it appends
entries, while preserving their independent binary representations. -/
@[step]
theorem module.decode_export_section.spec (data : Slice U8) (start : Usize) (env : module.Env)
    (hbound : ModuleEnv.Bounded env start.val) :
    module.decode_export_section data start env ⦃ r => match r.1 with
      | .Ok next => ∃ entries, ExportsAdded env entries r.2 ∧
          At (VecEncoding ExportEncoding) data start (entries.map ModuleEnv.rawExport) next ∧
          ModuleEnv.Bounded r.2 next.val
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hd⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data start)
  cases r with
  | Err e => simp [module.decode_export_section, hr]
  | Ok pair =>
      obtain ⟨count, pos⟩ := pair
      obtain ⟨⟨r, final⟩, hl, hp⟩ := WP.spec_imp_exists
        (module.decode_export_section_loop.spec data env count pos hd.span.2.2
          (hbound.mono (Nat.le_of_lt hd.span.1)))
      cases r with
      | Err e => simp [module.decode_export_section, hr, hl]
      | Ok next =>
          obtain ⟨entries, hlen, hhistory, hbytes, hb⟩ := hp
          simp [module.decode_export_section, hr, hl]
          exact ⟨entries, hhistory, At.vector hd hbytes (by simpa using hlen), hb⟩

end Itasca
