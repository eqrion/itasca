import Itasca.Module.Sections.Export
import Itasca.Module.Readers.NamesComplete
import Mathlib.Data.List.Nodup

open Aeneas Aeneas.Std

namespace Itasca.ModuleSections

theorem ExportsAdded.append {env middle result first rest}
    (hfirst : ExportsAdded env first middle) (hrest : ExportsAdded middle rest result) :
    ExportsAdded env (first ++ rest) result := by
  induction hrest with
  | nil => simpa using hfirst
  | snoc _ ha ih => simpa only [List.append_assoc] using ExportsAdded.snoc ih ha

end Itasca.ModuleSections

namespace Itasca.ModuleBinary
open ModuleSections

theorem At.export_desc_split {data pos desc next}
    (h : At ExportDescEncoding data pos desc next) :
    ∃ middle, At ByteEncoding data pos (descByte desc) middle ∧
      At IndexEncoding data middle (descIndex desc) next := by
  obtain ⟨bytes, he, hs⟩ := h
  cases he <;> rename_i idx indexBytes hi
  all_goals
    obtain ⟨middle, htag, hindex⟩ :=
      (show Wasm.BytesAt data pos ([_] ++ indexBytes) next from hs).split
    exact ⟨middle, ⟨_, rfl, htag⟩, ⟨indexBytes, hi, hindex⟩⟩

theorem At.export_split {data pos entry next}
    (h : At ExportEncoding data pos entry next) :
    ∃ first middle, At NameEncoding data pos entry.name first ∧
      At ByteEncoding data first (descByte entry.desc) middle ∧
      At IndexEncoding data middle (descIndex entry.desc) next := by
  obtain ⟨bytes, ⟨nameBytes, descBytes, hn, hd, rfl⟩, hs⟩ := h
  obtain ⟨first, hname, hdesc⟩ := hs.split
  obtain ⟨middle, htag, hindex⟩ :=
    (show At ExportDescEncoding data first entry.desc next from ⟨descBytes, hd, hdesc⟩).export_desc_split
  exact ⟨first, middle, ⟨nameBytes, hn, hname⟩, htag, hindex⟩

end Itasca.ModuleBinary

namespace Itasca
open ModuleBinary ModuleSections

theorem module.export_name_taken.fresh (env : module.Env) (nm : Slice U8)
    (h : nm.val ∉ env.exports.val.map (fun e => e.name.val)) :
    module.export_name_taken env nm = .ok false := by
  obtain ⟨taken, hr, ht⟩ := WP.spec_imp_exists (module.export_name_taken.spec env nm)
  cases taken with
  | false => exact hr
  | true => exact False.elim (h (ht.mp rfl))

theorem module.export_name_taken.duplicate (env : module.Env) (nm : Slice U8)
    (h : nm.val ∈ env.exports.val.map (fun e => e.name.val)) :
    module.export_name_taken env nm = .ok true := by
  obtain ⟨taken, hr, ht⟩ := WP.spec_imp_exists (module.export_name_taken.spec env nm)
  simpa [ht.mpr h] using hr

theorem module.export_desc.complete (env : module.Env) (desc : module.ExportDesc)
    (h : ExportDescValid env desc) :
    module.export_desc env (descByte desc) (descIndex desc) = .ok (.Ok desc) := by
  have hs : module.export_desc env (descByte desc) (descIndex desc) ⦃ r => r = .Ok desc ⦄ := by
    cases desc <;> simp only [descByte, descIndex, ExportDescValid] at *
    all_goals unfold module.export_desc
    all_goals step
    all_goals simp
    all_goals step*
  obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists hs
  exact hr

theorem module.decode_start_section.complete (data : Slice U8) (pos : Usize)
    (env : module.Env) (idx : U32) (next : Usize)
    (h : At StartEncoding data pos (some idx) next)
    (hi : idx.val < env.func_types.val.length)
    (hparams : env.func_types.val[idx.val].params.val = [])
    (hresults : env.func_types.val[idx.val].results.val = []) :
    module.decode_start_section data pos env = .ok (.Ok next, { env with start := some idx }) := by
  obtain ⟨bytes, ⟨index, hindex, he⟩, hs⟩ := h
  have hei : index = idx := Option.some.inj hindex.symm
  subst index
  have hr := hs.read_u32 idx he
  have hp : module.decode_start_section data pos env ⦃ r =>
      r = (.Ok next, { env with start := some idx }) ⦄ := by
    simp [module.decode_start_section, hr, core.result.Result.Insts.CoreOpsTry.branch]
    step*
    simp_all [alloc.vec.Vec.is_empty]
  obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists hp
  exact hr


/-- Distinct names across the old prefix and remaining raw declarations ensure
that each duplicate-name check takes the accepting branch. -/
theorem module.decode_export_section_loop.complete
    (data : Slice U8) (env : module.Env) (count : U32) (pos : Usize) (i : U32)
    (raw : List ModuleBinary.Export) (next : Usize)
    (hb : At (Rep ExportEncoding) data pos raw next)
    (hc : i.val + raw.length = count.val)
    (hnames : (env.exports.val.map (fun e => e.name.val) ++ raw.map (fun e => e.name)).Nodup)
    (hvalid : ∀ entry ∈ raw, ExportDescValid env entry.desc)
    (hsize : env.exports.val.length ≤ pos.val)
    (hrefs : env.declared_funcs.val.length ≤ pos.val) :
    ∃ result entries, module.decode_export_section_loop data env count pos i = .ok (.Ok next, result) ∧
      ExportsAdded env entries result ∧ entries.map ModuleEnv.rawExport = raw := by
  induction raw generalizing env pos i with
  | nil =>
      have he := hb.rep_nil
      have hstop : i ≥ count := by simp only [List.length_nil, Nat.add_zero] at hc; scalar_tac
      refine ⟨env, [], ?_, .nil, rfl⟩
      unfold module.decode_export_section_loop
      rw [loop]
      simp [module.decode_export_section_loop.body, hstop, he]
  | cons entry raw ih =>
      obtain ⟨endEntry, hentry, hrest⟩ := hb.rep_cons
      obtain ⟨first, middle, hnameBytes, htag, hindex⟩ := hentry.export_split
      obtain ⟨nm, hname, hnm⟩ := module.decode_name.complete_raw data pos entry.name first hnameBytes
      have hfresh : entry.name ∉ env.exports.val.map (fun e => e.name.val) := by
        have hh := List.nodup_cons.mp (List.nodup_middle.mp
          (show (env.exports.val.map (fun e => e.name.val) ++ entry.name :: raw.map (fun e => e.name)).Nodup from
            by simpa using hnames))
        intro hm
        exact hh.1 (List.mem_append_left _ hm)
      have htaken := module.export_name_taken.fresh env (alloc.vec.Vec.deref nm)
        (by simpa [alloc.vec.Vec.deref, hnm] using hfresh)
      have hdesc := module.export_desc.complete env entry.desc (hvalid entry (by simp))
      have hmore : ¬i ≥ count := by simp only [List.length_cons] at hc; scalar_tac
      have hprogress : pos.val < endEntry.val := by
        have := hnameBytes.span
        have := htag.span
        have := hindex.index_decoded.span
        omega
      have hbound := hentry.span.2
      let actual : module.Export := ⟨nm, entry.desc⟩
      have hraw : ModuleEnv.rawExport actual = entry := by cases entry; simp_all [ModuleEnv.rawExport, actual]
      have hdeclares : (match entry.desc with
          | .Func index => do
              let v ← alloc.vec.Vec.push env.declared_funcs index
              Result.ok {env with declared_funcs := v}
          | .Table _ => Result.ok env
          | .Memory _ => Result.ok env
          | .Global _ => Result.ok env) ⦃ result =>
          ModuleReferences.Added env result (ModuleReferences.exportIndices actual) ⦄ := by
        cases hdescCase : entry.desc <;> simp only
        · step
          exact ⟨rfl, by simpa [ModuleReferences.exportIndices, actual, hdescCase] using v_post⟩
        all_goals exact ⟨by cases env; rfl, by simp [ModuleReferences.exportIndices, actual, hdescCase]⟩
      obtain ⟨declared, hdeclare, hdeclared⟩ := WP.spec_imp_exists hdeclares
      have hnewRefs : declared.declared_funcs.val.length ≤ endEntry.val := by
        rw [hdeclared.2, List.length_append]
        have : (ModuleReferences.exportIndices actual).length ≤ 1 := by
          cases h : entry.desc <;> simp [ModuleReferences.exportIndices, actual, h]
        omega
      obtain ⟨exports, hpush, hexports⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.push_spec env.exports actual (by scalar_tac))
      obtain ⟨j, hj, hjval⟩ := WP.spec_imp_exists
        (U32.add_spec (x := i) (y := 1#u32) (by scalar_tac))
      let updated := {env with exports := exports, declared_funcs := declared.declared_funcs}
      have hadded : ExportAdded env updated actual :=
        ⟨rfl, hexports, by simpa only [actual, hnm] using hfresh,
          (hvalid entry (by simp)).resolves nm, hdeclared.2⟩
      obtain ⟨result, entries, hloop, hhistory, hentries⟩ := ih updated endEntry j hrest
        (by simp only [List.length_cons] at hc; scalar_tac)
        (by simpa [updated, hexports, actual, hnm, List.append_assoc] using hnames)
        (by intro e he; exact hvalid e (by simp [he]))
        (by simp only [updated, hexports, List.length_append, List.length_singleton]; omega)
        hnewRefs
      refine ⟨result, actual :: entries, ?_, ?_, by simp [hraw, hentries]⟩
      · unfold module.decode_export_section_loop
        rw [loop]
        simp [module.decode_export_section_loop.body, hmore,
          hname, htaken, htag.read_byte, hindex.read_index, hdesc,
          core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        cases hdescCase : entry.desc <;> simp only [hdescCase] at hdeclare ⊢
        all_goals
          rw [hdeclare]
          simp only [bind_ok]
          rw [hdeclared.1]
          have hpush' := hpush
          simp only [actual, hdescCase] at hpush'
          simpa [hpush', hj, module.decode_export_section_loop,
            module.decode_export_section_loop.body, actual, updated, hdescCase,
            core.result.Result.Insts.CoreOpsTry.branch] using hloop
      · simpa using (ExportsAdded.snoc ExportsAdded.nil hadded).append hhistory

theorem module.decode_export_section.complete (data : Slice U8) (pos : Usize)
    (env : module.Env) (raw : List ModuleBinary.Export) (next : Usize)
    (hb : At (VecEncoding ExportEncoding) data pos raw next)
    (hempty : env.exports.val = []) (hnames : (raw.map (fun e => e.name)).Nodup)
    (hvalid : ∀ entry ∈ raw, ExportDescValid env entry.desc)
    (hrefs : env.declared_funcs.val.length ≤ pos.val) :
    ∃ result entries, module.decode_export_section data pos env = .ok (.Ok next, result) ∧
      ExportsAdded env entries result ∧ entries.map ModuleEnv.rawExport = raw := by
  obtain ⟨count, middle, hc, hcount, hentries⟩ := hb.vector_split
  obtain ⟨result, entries, hr, hp, he⟩ := module.decode_export_section_loop.complete
    data env count middle 0#u32 raw next hentries (by simpa using hc.symm)
    (by simpa [hempty] using hnames) hvalid (by simp [hempty])
    (by have := hcount.span; omega)
  refine ⟨result, entries, ?_, hp, he⟩
  simp [module.decode_export_section, reader.read_u32_leb.complete data pos count middle hcount,
    core.result.Result.Insts.CoreOpsTry.branch, hr]

end Itasca
