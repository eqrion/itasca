import Itasca.Module.ModuleEnvRequirements
import Itasca.Module.ModuleFunctionsComplete
import Itasca.Module.ModuleImportSection
import Itasca.Module.ModuleNamesComplete
import Itasca.Module.ModuleTypesComplete

open Aeneas Aeneas.Std



namespace Itasca.ModuleSections

theorem ImportsAdded.trans {env middle result first rest}
    (h : ImportsAdded env first middle) (h' : ImportsAdded middle rest result) :
    ImportsAdded env (first ++ rest) result := by
  induction h' with
  | nil => simpa using h
  | snoc previous current ih => simpa [List.append_assoc] using ImportsAdded.snoc ih current

end Itasca.ModuleSections

namespace Itasca

open ModuleBinary ModuleSections

/-- Independently encoded, well-typed import names and descriptors make the
actual decoder append exactly that import and its resolved cache entry. -/
theorem module.decode_import.complete (data : Slice U8) (pos : Usize)
    (env : module.Env) (entry : ModuleBinary.Import) (next : Usize)
    (hb : At ImportEncoding data pos entry next)
    (hv : ImportValid env entry.desc) (hbound : ModuleEnv.Bounded env pos.val) :
    ∃ result actual, module.decode_import data pos env = .ok (.Ok next, result) ∧
      ModuleEnv.rawImport actual = entry ∧ ImportAdded env result actual := by
  rcases entry with ⟨moduleName, rawName, desc⟩
  obtain ⟨bs, ⟨modBytes, nameBytes, descBytes, hm, hn, hd, rfl⟩, hs⟩ := hb
  obtain ⟨p1, hmbytes, hremain⟩ :=
    (show Wasm.BytesAt data pos (modBytes ++ (nameBytes ++ descBytes)) next from
      by simpa [List.append_assoc] using hs).split
  obtain ⟨p2, hnbytes, hdbytes⟩ := hremain.split
  obtain ⟨modName, hmod, hmodval⟩ := module.decode_name.complete_raw data pos moduleName p1 ⟨_, hm, hmbytes⟩
  obtain ⟨nm, hname, hnameval⟩ := module.decode_name.complete_raw data p1 rawName p2 ⟨_, hn, hnbytes⟩
  have hpos1 := hmbytes.length
  have hpos2 := hnbytes.length
  cases hd with
  | func idx he =>
    obtain ⟨p3, htag, hidx⟩ := (show Wasm.BytesAt data p2 ([0#u8] ++ _) next from hdbytes).split
    have hprogress := htag.length
    have hspan := hidx.u32_decoded idx he |>.span
    have hidxvalid : idx.val < env.types.val.length := hv
    have hlookup := module.lookup_type.complete env idx hidxvalid
    obtain ⟨funcs, hpush, hfuncs⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec env.func_types env.types.val[idx.val] (by have := hbound.funcs; scalar_tac))
    obtain ⟨num, hnum, hnumval⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := env.num_imported_funcs) (y := 1#usize) (by have := hbound.numFuncs; scalar_tac))
    let actual : module.Import := ⟨modName, nm, .Func idx⟩
    obtain ⟨imports, hpushimport, himports⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec env.imports actual (by have := hbound.imports; scalar_tac))
    let result := {env with imports := imports, func_types := funcs, num_imported_funcs := num}
    refine ⟨result, actual, ?_, ?_, himports, ?_⟩
    · simp [module.decode_import, hmod, hname, htag.read_byte, hidx.read_u32 idx he,
        hlookup, hpush, hnum, hpushimport, actual, result, core.result.Result.Insts.CoreOpsTry.branch]
    · simp_all [ModuleEnv.rawImport, actual]
    · exact ⟨env.types.val[idx.val], ⟨hidxvalid, rfl⟩, rfl, hfuncs, hnumval⟩
  | table tt he =>
    obtain ⟨p3, htag, hty⟩ := (show Wasm.BytesAt data p2 ([1#u8] ++ _) next from hdbytes).split
    have hprogress := htag.length
    have hnext := hty.bound
    have hv' : ModuleBinary.LimitsValid tt.limits limits.MAX_TABLE_ELEMS ∧ env.table_types.val.length + 1 ≤ 1 := hv
    have hread := module.decode_table_type.complete data p3 tt next ⟨_, he, hty⟩ hv'.1
    obtain ⟨tables, hpush, htables⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec env.table_types tt (by scalar_tac))
    have hlen : tables.val.length ≤ 1 := by
      simpa only [htables, List.length_append, List.length_singleton] using hv'.2
    have hmax : ¬ limits.MAX_TABLES.val < tables.val.length := by
      simpa [limits.MAX_TABLES] using hlen
    let actual : module.Import := ⟨modName, nm, .Table tt⟩
    obtain ⟨imports, hpushimport, himports⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec env.imports actual (by have := hbound.imports; scalar_tac))
    let result := {env with imports := imports, table_types := tables}
    refine ⟨result, actual, ?_, ?_, himports, rfl, htables, ?_, ?_⟩
    · simp [module.decode_import, hmod, hname, htag.read_byte, hread,
        hpush, hmax, hpushimport, actual, result, core.result.Result.Insts.CoreOpsTry.branch]
    · simp_all [ModuleEnv.rawImport, actual]
    · simpa [result, htables] using hv'.2
    · simpa [ModuleTranslation.LimitsValid, ModuleBinary.LimitsValid,
        Option.mem_def, global_simps, U32.rMax] using hv'.1
  | memory mt he =>
    obtain ⟨p3, htag, hty⟩ := (show Wasm.BytesAt data p2 ([2#u8] ++ _) next from hdbytes).split
    have hprogress := htag.length
    have hnext := hty.bound
    have hv' : ModuleBinary.LimitsValid mt.limits limits.MAX_MEMORY_PAGES ∧ env.mem_types.val.length + 1 ≤ 1 := hv
    have hread := module.decode_mem_type.complete data p3 mt next ⟨_, he, hty⟩ hv'.1
    obtain ⟨memories, hpush, hmemories⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec env.mem_types mt (by scalar_tac))
    have hlen : memories.val.length ≤ 1 := by
      simpa only [hmemories, List.length_append, List.length_singleton] using hv'.2
    have hmax : ¬ limits.MAX_MEMORIES.val < memories.val.length := by
      simpa [limits.MAX_MEMORIES] using hlen
    let actual : module.Import := ⟨modName, nm, .Memory mt⟩
    obtain ⟨imports, hpushimport, himports⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec env.imports actual (by have := hbound.imports; scalar_tac))
    let result := {env with imports := imports, mem_types := memories}
    refine ⟨result, actual, ?_, ?_, himports, rfl, hmemories, ?_, ?_⟩
    · simp [module.decode_import, hmod, hname, htag.read_byte, hread,
        hpush, hmax, hpushimport, actual, result, core.result.Result.Insts.CoreOpsTry.branch]
    · simp_all [ModuleEnv.rawImport, actual]
    · simpa [result, hmemories] using hv'.2
    · simpa [ModuleTranslation.LimitsValid, ModuleBinary.LimitsValid,
        Option.mem_def, global_simps] using hv'.1
  | global gt he =>
    obtain ⟨p3, htag, hty⟩ := (show Wasm.BytesAt data p2 ([3#u8] ++ _) next from hdbytes).split
    have hprogress := htag.length
    have hnext := hty.bound
    have hread := module.decode_global_type.complete data p3 gt next ⟨_, he, hty⟩
    obtain ⟨globals, hpush, hglobals⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec env.global_types gt (by have := hbound.globalTypes; scalar_tac))
    obtain ⟨num, hnum, hnumval⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := env.num_imported_globals) (y := 1#usize) (by have := hbound.numGlobals; scalar_tac))
    let actual : module.Import := ⟨modName, nm, .Global gt⟩
    obtain ⟨imports, hpushimport, himports⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec env.imports actual (by have := hbound.imports; scalar_tac))
    let result := {env with imports := imports, global_types := globals, num_imported_globals := num}
    refine ⟨result, actual, ?_, ?_, himports, rfl, hglobals, hnumval⟩
    · simp [module.decode_import, hmod, hname, htag.read_byte, hread,
        hpush, hnum, hpushimport, actual, result, core.result.Result.Insts.CoreOpsTry.branch]
    · simp_all [ModuleEnv.rawImport, actual]


theorem module.decode_import_section_loop.complete
    (data : Slice U8) (env : module.Env) (count : U32) (pos : Usize) (i : U32)
    (entries : List ModuleBinary.Import) (next : Usize)
    (hb : At (Rep ImportEncoding) data pos entries next)
    (hc : i.val + entries.length = count.val)
    (hv : ImportsValid env entries) (hbound : ModuleEnv.Bounded env pos.val) :
    ∃ result actual, module.decode_import_section_loop data env count pos i = .ok (.Ok next, result) ∧
      actual.map ModuleEnv.rawImport = entries ∧ ImportsAdded env actual result := by
  induction entries generalizing env pos i with
  | nil =>
    have he := hb.rep_nil
    have hstop : i ≥ count := by simp only [List.length_nil, Nat.add_zero] at hc; scalar_tac
    refine ⟨env, [], ?_, rfl, .nil⟩
    unfold module.decode_import_section_loop
    rw [loop]
    simp [module.decode_import_section_loop.body, hstop, he]
  | cons entry entries ih =>
    obtain ⟨middle, hfirst, hrest⟩ := hb.rep_cons
    have hmore : ¬ i ≥ count := by simp only [List.length_cons] at hc; scalar_tac
    obtain ⟨updated, current, hread, hraw, hadded⟩ := module.decode_import.complete
      data pos env entry middle hfirst hv.head hbound
    have hbound' : ModuleEnv.Bounded updated middle.val := by
      have hs := module.decode_import.spec data pos env hbound
      simp only [hread, WP.spec_ok] at hs
      exact hs.choose_spec.2.2
    obtain ⟨j, hj, hjval⟩ := WP.spec_imp_exists
      (U32.add_spec (x := i) (y := 1#u32) (by scalar_tac))
    have hv' : ImportsValid updated entries := by
      rw [← hraw] at hv
      exact hv.tail hadded
    obtain ⟨result, actual, hloop, hraws, hhistory⟩ := ih updated middle j hrest
      (by simp only [List.length_cons] at hc; scalar_tac) hv' hbound'
    refine ⟨result, current :: actual, ?_, by simp [hraw, hraws], ?_⟩
    · unfold module.decode_import_section_loop at hloop ⊢
      rw [loop]
      simpa [module.decode_import_section_loop.body, hmore, hread, hj,
        core.result.Result.Insts.CoreOpsTry.branch] using hloop
    · simpa using (ImportsAdded.snoc ImportsAdded.nil hadded).trans hhistory

theorem module.decode_import_section.complete (data : Slice U8) (pos : Usize)
    (env : module.Env) (entries : List ModuleBinary.Import) (next : Usize)
    (hb : At (VecEncoding ImportEncoding) data pos entries next)
    (hv : ImportsValid env entries) (hbound : ModuleEnv.Bounded env pos.val) :
    ∃ result actual, module.decode_import_section data pos env = .ok (.Ok next, result) ∧
      actual.map ModuleEnv.rawImport = entries ∧ ImportsAdded env actual result := by
  obtain ⟨count, middle, hc, hcount, hentries⟩ := hb.vector_split
  obtain ⟨result, actual, hr, hp⟩ := module.decode_import_section_loop.complete
    data env count middle 0#u32 entries next hentries (by simpa using hc.symm) hv
    (hbound.mono (by have := hcount.span; omega))
  refine ⟨result, actual, ?_, hp⟩
  simp [module.decode_import_section, reader.read_u32_leb.complete data pos count middle hcount,
    core.result.Result.Insts.CoreOpsTry.branch, hr]

end Itasca
