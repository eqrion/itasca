import Itasca.Module.Env.Requirements
import Itasca.Module.Sections.GlobalComplete
import Itasca.Module.Sections.Tail
import Itasca.Module.Readers.TypesComplete
import Itasca.Module.Sections.Data
import Itasca.Module.Sections.ElementHeader

/-!
Sections, each formerly its own module: ImportsComplete, MemoryComplete, TableComplete, TypeComplete.
-/

/-! ## ImportsComplete -/

section

/-!
# Completeness of the import section parser

`metadata.decode_import_section.complete`: an independently encoded vector of imports that are
`ImportsValid` in the environment is accepted, and the environment
gains the corresponding entries (`ImportsAdded`). Soundness is in `Module/Sections/Imports`.
-/

open Aeneas Aeneas.Std



namespace Itasca.ModuleSections

/-- Import additions compose. -/
theorem ImportsAdded.trans {env middle result first rest}
    (h : ImportsAdded env first middle) (h' : ImportsAdded middle rest result) :
    ImportsAdded env (first ++ rest) result := by
  induction h' with
  | nil => simpa using h
  | snoc previous current ih => simpa [List.append_assoc] using ImportsAdded.snoc ih current

end Itasca.ModuleSections

namespace Itasca

open ModuleBinary ModuleSections

/-- `metadata.decode_import` accepts a valid `ImportEncoding` span and adds that import and
its cache entry to the environment. -/
theorem metadata.decode_import.complete (data : Slice U8) (pos : Usize)
    (env : metadata.Env) (entry : ModuleBinary.Import) (next : Usize)
    (hb : At ImportEncoding data pos entry next)
    (hv : ImportValid env entry.desc)
    (hbound : ModuleEnv.Bounded env pos.val) :
    ∃ result actual, metadata.decode_import data pos env = .ok (.Ok next, result) ∧
      ModuleEnv.rawImport actual = entry ∧ ImportAdded env result actual := by
  rcases entry with ⟨moduleName, rawName, desc⟩
  obtain ⟨bs, ⟨modBytes, nameBytes, descBytes, hm, hn, hd, rfl⟩, hs⟩ := hb
  obtain ⟨p1, hmbytes, hremain⟩ :=
    (show Wasm1.BytesAt data pos (modBytes ++ (nameBytes ++ descBytes)) next from
      by simpa [List.append_assoc] using hs).split
  obtain ⟨p2, hnbytes, hdbytes⟩ := hremain.split
  obtain ⟨modName, hmod, hmodval⟩ := metadata.decode_name.complete_raw data pos moduleName p1 ⟨_, hm, hmbytes⟩
  obtain ⟨nm, hname, hnameval⟩ := metadata.decode_name.complete_raw data p1 rawName p2 ⟨_, hn, hnbytes⟩
  have hpos1 := hmbytes.length
  have hpos2 := hnbytes.length
  cases hd with
  | func idx he =>
    obtain ⟨p3, htag, hidx⟩ := (show Wasm1.BytesAt data p2 ([0#u8] ++ _) next from hdbytes).split
    have hprogress := htag.length
    have hspan := hidx.u32_decoded idx he |>.span
    have hidxvalid : idx.val < env.types.val.length := hv
    have hlookup := metadata.lookup_type.complete env idx hidxvalid
    obtain ⟨funcs, hpush, hfuncs⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec env.func_types env.types.val[idx.val] (by have := hbound.funcs; scalar_tac))
    obtain ⟨num, hnum, hnumval⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := env.num_imported_funcs) (y := 1#usize) (by have := hbound.numFuncs; scalar_tac))
    let actual : metadata.Import := ⟨modName, nm, .Func idx⟩
    obtain ⟨imports, hpushimport, himports⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec env.imports actual (by have := hbound.imports; scalar_tac))
    let result := {env with imports := imports, func_types := funcs, num_imported_funcs := num}
    refine ⟨result, actual, ?_, ?_, himports, ?_⟩
    · simp [metadata.decode_import, hmod, hname, htag.read_byte, hidx.read_u32 idx he,
        hlookup, hpush, hnum, hpushimport, actual, result, core.result.Result.Insts.CoreOpsTry.branch]
    · simp_all [ModuleEnv.rawImport, actual]
    · exact ⟨env.types.val[idx.val], ⟨hidxvalid, rfl⟩, rfl, hfuncs, hnumval⟩
  | table tt he =>
    obtain ⟨p3, htag, hty⟩ := (show Wasm1.BytesAt data p2 ([1#u8] ++ _) next from hdbytes).split
    have hprogress := htag.length
    have hnext := hty.bound
    have hv' : ModuleBinary.LimitsValid tt.limits limits.MAX_TABLE_ELEMS := hv
    have hread := metadata.decode_table_type.complete data p3 tt next ⟨_, he, hty⟩ hv'
    obtain ⟨tables, hpush, htables⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec env.table_types tt (by have := hbound.tables; scalar_tac))
    let actual : metadata.Import := ⟨modName, nm, .Table tt⟩
    obtain ⟨imports, hpushimport, himports⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec env.imports actual (by have := hbound.imports; scalar_tac))
    let result := {env with imports := imports, table_types := tables}
    refine ⟨result, actual, ?_, ?_, himports, rfl, htables, ?_⟩
    · simp [metadata.decode_import, hmod, hname, htag.read_byte, hread,
        hpush, hpushimport, actual, result, core.result.Result.Insts.CoreOpsTry.branch]
    · simp_all [ModuleEnv.rawImport, actual]
    · simpa [ModuleTranslation.LimitsValid, ModuleBinary.LimitsValid,
        Option.mem_def, global_simps, U32.rMax] using hv'
  | memory mt he =>
    obtain ⟨p3, htag, hty⟩ := (show Wasm1.BytesAt data p2 ([2#u8] ++ _) next from hdbytes).split
    have hprogress := htag.length
    have hnext := hty.bound
    have hv' : ModuleBinary.LimitsValid mt.limits limits.MAX_MEMORY_PAGES ∧ env.mem_types.val.length + 1 ≤ 1 := hv
    have hread := metadata.decode_mem_type.complete data p3 mt next ⟨_, he, hty⟩ hv'.1
    obtain ⟨memories, hpush, hmemories⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec env.mem_types mt (by scalar_tac))
    have hlen : memories.val.length ≤ 1 := by
      simpa only [hmemories, List.length_append, List.length_singleton] using hv'.2
    have hmax : ¬ limits.MAX_MEMORIES.val < memories.val.length := by
      simpa [limits.MAX_MEMORIES] using hlen
    let actual : metadata.Import := ⟨modName, nm, .Memory mt⟩
    obtain ⟨imports, hpushimport, himports⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec env.imports actual (by have := hbound.imports; scalar_tac))
    let result := {env with imports := imports, mem_types := memories}
    refine ⟨result, actual, ?_, ?_, himports, rfl, hmemories, ?_, ?_⟩
    · simp [metadata.decode_import, hmod, hname, htag.read_byte, hread,
        hpush, hmax, hpushimport, actual, result, core.result.Result.Insts.CoreOpsTry.branch]
    · simp_all [ModuleEnv.rawImport, actual]
    · simpa [result, hmemories] using hv'.2
    · simpa [ModuleTranslation.LimitsValid, ModuleBinary.LimitsValid,
        Option.mem_def, global_simps] using hv'.1
  | global gt he =>
    obtain ⟨p3, htag, hty⟩ := (show Wasm1.BytesAt data p2 ([3#u8] ++ _) next from hdbytes).split
    have hprogress := htag.length
    have hnext := hty.bound
    have hread := metadata.decode_global_type.complete data p3 gt next ⟨_, he, hty⟩
    obtain ⟨globals, hpush, hglobals⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec env.global_types gt (by have := hbound.globalTypes; scalar_tac))
    obtain ⟨num, hnum, hnumval⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := env.num_imported_globals) (y := 1#usize) (by have := hbound.numGlobals; scalar_tac))
    let actual : metadata.Import := ⟨modName, nm, .Global gt⟩
    obtain ⟨imports, hpushimport, himports⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec env.imports actual (by have := hbound.imports; scalar_tac))
    let result := {env with imports := imports, global_types := globals, num_imported_globals := num}
    refine ⟨result, actual, ?_, ?_, himports, rfl, hglobals, hnumval⟩
    · simp [metadata.decode_import, hmod, hname, htag.read_byte, hread,
        hpush, hnum, hpushimport, actual, result, core.result.Result.Insts.CoreOpsTry.branch]
    · simp_all [ModuleEnv.rawImport, actual]


/-- The import loop accepts the remaining valid imports of a repetition span. -/
theorem metadata.decode_import_section_loop.complete
    (data : Slice U8) (env : metadata.Env) (count : U32) (pos : Usize) (i : U32)
    (entries : List ModuleBinary.Import) (next : Usize)
    (hb : At (Rep ImportEncoding) data pos entries next)
    (hc : i.val + entries.length = count.val)
    (hv : ImportsValid env entries)
    (hbound : ModuleEnv.Bounded env pos.val) :
    ∃ result actual, metadata.decode_import_section_loop data env count pos i = .ok (.Ok next, result) ∧
      actual.map ModuleEnv.rawImport = entries ∧ ImportsAdded env actual result := by
  induction entries generalizing env pos i with
  | nil =>
    have he := hb.rep_nil
    have hstop : i ≥ count := by simp only [List.length_nil, Nat.add_zero] at hc; scalar_tac
    refine ⟨env, [], ?_, rfl, .nil⟩
    unfold metadata.decode_import_section_loop
    rw [loop]
    simp [metadata.decode_import_section_loop.body, hstop, he]
  | cons entry entries ih =>
    obtain ⟨middle, hfirst, hrest⟩ := hb.rep_cons
    have hmore : ¬ i ≥ count := by simp only [List.length_cons] at hc; scalar_tac
    obtain ⟨updated, current, hread, hraw, hadded⟩ := metadata.decode_import.complete
      data pos env entry middle hfirst hv.head hbound
    have hbound' : ModuleEnv.Bounded updated middle.val := by
      have hs := metadata.decode_import.spec data pos env hbound
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
    · unfold metadata.decode_import_section_loop at hloop ⊢
      rw [loop]
      simpa [metadata.decode_import_section_loop.body, hmore, hread, hj,
        core.result.Result.Insts.CoreOpsTry.branch] using hloop
    · simpa using (ImportsAdded.snoc ImportsAdded.nil hadded).trans hhistory

/-- `metadata.decode_import_section` accepts a vector span of valid imports. -/
theorem metadata.decode_import_section.complete (data : Slice U8) (pos : Usize)
    (env : metadata.Env) (entries : List ModuleBinary.Import) (next : Usize)
    (hb : At (VecEncoding ImportEncoding) data pos entries next)
    (hv : ImportsValid env entries)
    (hbound : ModuleEnv.Bounded env pos.val) :
    ∃ result actual, metadata.decode_import_section data pos env = .ok (.Ok next, result) ∧
      actual.map ModuleEnv.rawImport = entries ∧ ImportsAdded env actual result := by
  obtain ⟨count, middle, hc, hcount, hentries⟩ := hb.vector_split
  obtain ⟨result, actual, hr, hp⟩ := metadata.decode_import_section_loop.complete
    data env count middle 0#u32 entries next hentries (by simpa using hc.symm) hv
    (hbound.mono (by have := hcount.span; omega))
  refine ⟨result, actual, ?_, hp⟩
  simp [metadata.decode_import_section, reader.read_u32_leb.complete data pos count middle hcount,
    core.result.Result.Insts.CoreOpsTry.branch, hr]

end Itasca

end

/-! ## MemoryComplete -/

section

/-!
# Completeness of the memory section parser

`metadata.decode_memory_section.complete`: an independently encoded vector of memory types with
limits within `limits.MAX_MEMORY_PAGES`, at most one memory in total, is accepted and the
environment gains those memories (`MemoriesAdded`). Soundness is in `Module/Sections/Memory`.
-/

open Aeneas Aeneas.Std

namespace Itasca

open ModuleBinary ModuleSections

/-- The memory loop accepts the remaining valid memory types of a repetition span and adds them. -/
theorem metadata.decode_memory_section_loop.complete
    (data : Slice U8) (env : metadata.Env) (count : U32) (pos : Usize) (i : U32)
    (added : List wasm_types.MemType) (next : Usize)
    (hb : At (Rep MemTypeEncoding) data pos added next)
    (hc : i.val + added.length = count.val)
    (hv : ∀ ty ∈ added, ModuleBinary.LimitsValid ty.limits limits.MAX_MEMORY_PAGES)
    (hsize : env.mem_types.val.length + added.length ≤ 1) :
    ∃ result, metadata.decode_memory_section_loop data env count pos i = .ok (.Ok next, result) ∧
      MemoriesAdded env result added := by
  induction added generalizing env pos i with
  | nil =>
    have he := hb.rep_nil
    have hstop : i ≥ count := by simp only [List.length_nil, Nat.add_zero] at hc; scalar_tac
    refine ⟨env, ?_, by exact ⟨by cases env; rfl, by simp⟩⟩
    unfold metadata.decode_memory_section_loop
    rw [loop]
    simp [metadata.decode_memory_section_loop.body, hstop, he]
  | cons ty added ih =>
    obtain ⟨middle, hfirst, hrest⟩ := hb.rep_cons
    have hmore : ¬ i ≥ count := by simp only [List.length_cons] at hc; scalar_tac
    have hread := metadata.decode_mem_type.complete data pos ty middle hfirst (hv ty (by simp))
    obtain ⟨updatedTypes, hpush, htypes⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec env.mem_types ty (by simp only [List.length_cons] at hsize; scalar_tac))
    have hlen : updatedTypes.val.length = env.mem_types.val.length + 1 := by simp [htypes]
    have hzero : env.mem_types.val.length = 0 := by simp only [List.length_cons] at hsize; omega
    have hmax : ¬ alloc.vec.Vec.len updatedTypes > limits.MAX_MEMORIES := by
      simp [alloc.vec.Vec.len, limits.MAX_MEMORIES, hlen, hzero]
    obtain ⟨j, hj, hjval⟩ := WP.spec_imp_exists
      (U32.add_spec (x := i) (y := 1#u32) (by scalar_tac))
    let updated := {env with mem_types := updatedTypes}
    obtain ⟨result, hloop, hadded⟩ := ih updated middle j hrest
      (by simp only [List.length_cons] at hc; scalar_tac)
      (by intro ft hx; exact hv ft (by simp [hx]))
      (by change updatedTypes.val.length + added.length ≤ 1; simp only [List.length_cons] at hsize; omega)
    refine ⟨result, ?_, ?_⟩
    · unfold metadata.decode_memory_section_loop at hloop ⊢
      rw [loop]
      simpa [metadata.decode_memory_section_loop.body, hmore, hread,
        hpush, hj, core.result.Result.Insts.CoreOpsTry.branch,
        alloc.vec.Vec.len, limits.MAX_MEMORIES, hlen, hzero] using hloop
    · refine ⟨?_, ?_⟩
      · rw [hadded.1]
      · simpa [updated, htypes, List.append_assoc] using hadded.2

/-- `metadata.decode_memory_section` accepts a vector span of valid memory types and adds them. -/
theorem metadata.decode_memory_section.complete (data : Slice U8) (pos : Usize)
    (env : metadata.Env) (added : List wasm_types.MemType) (next : Usize)
    (hb : At (VecEncoding MemTypeEncoding) data pos added next)
    (hv : ∀ ty ∈ added, ModuleBinary.LimitsValid ty.limits limits.MAX_MEMORY_PAGES)
    (hsize : env.mem_types.val.length + added.length ≤ 1) :
    ∃ result, metadata.decode_memory_section data pos env = .ok (.Ok next, result) ∧
      MemoriesAdded env result added := by
  obtain ⟨count, middle, hc, hcount, hentries⟩ := hb.vector_split
  obtain ⟨result, hr, hp⟩ := metadata.decode_memory_section_loop.complete
    data env count middle 0#u32 added next hentries (by simpa using hc.symm) hv hsize
  refine ⟨result, ?_, hp⟩
  simp [metadata.decode_memory_section, reader.read_u32_leb.complete data pos count middle hcount,
    core.result.Result.Insts.CoreOpsTry.branch, hr]

end Itasca

end

/-! ## TableComplete -/

section

/-!
# Completeness of the table section parser

`metadata.decode_table_section.complete`: an independently encoded vector of table types with
limits within the table cap is accepted, and the environment
gains those tables (`TablesAdded`).
Soundness is in `Module/Sections/Table`.
-/

open Aeneas Aeneas.Std

namespace Itasca

open ModuleBinary ModuleSections

/-- The table loop accepts the remaining valid table types of a repetition span and adds them. -/
theorem metadata.decode_table_section_loop.complete
    (data : Slice U8) (env : metadata.Env) (count : U32) (pos : Usize) (i : U32)
    (added : List wasm_types.TableType) (next : Usize)
    (hb : At (Rep TableTypeEncoding) data pos added next)
    (hc : i.val + added.length = count.val)
    (hv : ∀ ty ∈ added, ModuleBinary.LimitsValid ty.limits limits.MAX_TABLE_ELEMS)
    (hbound : env.table_types.val.length ≤ pos.val) :
    ∃ result, metadata.decode_table_section_loop data env count pos i = .ok (.Ok next, result) ∧
      TablesAdded env result added := by
  induction added generalizing env pos i with
  | nil =>
    have he := hb.rep_nil
    have hstop : i ≥ count := by simp only [List.length_nil, Nat.add_zero] at hc; scalar_tac
    refine ⟨env, ?_, by exact ⟨by cases env; rfl, by simp⟩⟩
    unfold metadata.decode_table_section_loop
    rw [loop]
    simp [metadata.decode_table_section_loop.body, hstop, he]
  | cons ty added ih =>
    obtain ⟨middle, hfirst, hrest⟩ := hb.rep_cons
    have hmore : ¬ i ≥ count := by simp only [List.length_cons] at hc; scalar_tac
    have hread := metadata.decode_table_type.complete data pos ty middle hfirst (hv ty (by simp))
    have hprogress := hfirst.tableType_progress
    have hnext := hfirst.span.2
    obtain ⟨updatedTypes, hpush, htypes⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec env.table_types ty (by scalar_tac))
    have hlen : updatedTypes.val.length = env.table_types.val.length + 1 := by simp [htypes]
    obtain ⟨j, hj, hjval⟩ := WP.spec_imp_exists
      (U32.add_spec (x := i) (y := 1#u32) (by scalar_tac))
    let updated := {env with table_types := updatedTypes}
    obtain ⟨result, hloop, hadded⟩ := ih updated middle j hrest
      (by simp only [List.length_cons] at hc; scalar_tac)
      (by intro ft hx; exact hv ft (by simp [hx]))
      (by change updatedTypes.val.length ≤ middle.val; omega)
    refine ⟨result, ?_, ?_⟩
    · unfold metadata.decode_table_section_loop at hloop ⊢
      rw [loop]
      simpa [metadata.decode_table_section_loop.body, hmore, hread,
        hpush, hj, core.result.Result.Insts.CoreOpsTry.branch] using hloop
    · refine ⟨?_, ?_⟩
      · rw [hadded.1]
      · simpa [updated, htypes, List.append_assoc] using hadded.2

/-- `metadata.decode_table_section` accepts a vector span of valid table types and adds them. -/
theorem metadata.decode_table_section.complete (data : Slice U8) (pos : Usize)
    (env : metadata.Env) (added : List wasm_types.TableType) (next : Usize)
    (hb : At (VecEncoding TableTypeEncoding) data pos added next)
    (hv : ∀ ty ∈ added, ModuleBinary.LimitsValid ty.limits limits.MAX_TABLE_ELEMS)
    (hbound : env.table_types.val.length ≤ pos.val) :
    ∃ result, metadata.decode_table_section data pos env = .ok (.Ok next, result) ∧
      TablesAdded env result added := by
  obtain ⟨count, middle, hc, hcount, hentries⟩ := hb.vector_split
  obtain ⟨result, hr, hp⟩ := metadata.decode_table_section_loop.complete
    data env count middle 0#u32 added next hentries (by simpa using hc.symm) hv
    (by have := hcount.span; omega)
  refine ⟨result, ?_, hp⟩
  simp [metadata.decode_table_section, reader.read_u32_leb.complete data pos count middle hcount,
    core.result.Result.Insts.CoreOpsTry.branch, hr]

end Itasca

end

/-! ## TypeComplete -/

section

/-!
# Completeness of the type section parser

`metadata.decode_type_section.profile_complete`: an independently
encoded vector of signatures that satisfy the completeness caps
is accepted, and the environment gains exactly those signatures (`TypesAdded`). The loop versions
carry a count and the signatures remaining. Soundness is in `Module/Sections/Type`.
-/

open Aeneas Aeneas.Std

namespace Itasca

open ModuleBinary ModuleSections

/-- The type loop accepts the remaining signatures of a repetition span and adds them. -/
theorem metadata.decode_type_section_loop.profile_complete
    (data : Slice U8) (env : metadata.Env) (count : U32) (pos : Usize) (i : U32)
    (types : List wasm_types.FuncType) (next : Usize)
    (hb : At (Rep FuncTypeEncoding) data pos types next)
    (hc : i.val + types.length = count.val)
    (ht : ∀ ft ∈ types, Profile.FuncTypeWithinLimits ft)
    (hsize : env.types.val.length ≤ pos.val) :
    ∃ result, metadata.decode_type_section_loop data env count pos i = .ok (.Ok next, result) ∧
      TypesAdded env result types := by
  induction types generalizing env pos i with
  | nil =>
    have he := hb.rep_nil
    have hstop : i ≥ count := by simp only [List.length_nil, Nat.add_zero] at hc; scalar_tac
    refine ⟨env, ?_, by exact ⟨by cases env; rfl, by simp⟩⟩
    unfold metadata.decode_type_section_loop
    rw [loop]
    simp [metadata.decode_type_section_loop.body, hstop, he]
  | cons ft types ih =>
    obtain ⟨middle, hfirst, hrest⟩ := hb.rep_cons
    have hprogress := hfirst.funcType_progress
    have hbound := hfirst.span.2
    have hmore : ¬ i ≥ count := by simp only [List.length_cons] at hc; scalar_tac
    have hread := metadata.decode_func_type.profile_complete data pos ft middle hfirst
      (ht ft (by simp))
    obtain ⟨updatedTypes, hpush, htypes⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec env.types ft (by scalar_tac))
    obtain ⟨j, hj, hjval⟩ := WP.spec_imp_exists
      (U32.add_spec (x := i) (y := 1#u32) (by scalar_tac))
    let updated := {env with types := updatedTypes}
    obtain ⟨result, hloop, hadded⟩ := ih updated middle j hrest
      (by simp only [List.length_cons] at hc; scalar_tac)
      (by intro ft hx; exact ht ft (by simp [hx]))
      (by simp only [updated, htypes, List.length_append, List.length_singleton]; omega)
    refine ⟨result, ?_, ?_⟩
    · unfold metadata.decode_type_section_loop
      rw [loop]
      simp [metadata.decode_type_section_loop.body, hmore, hread,
        hpush, hj, core.result.Result.Insts.CoreOpsTry.branch]
      exact hloop
    · refine ⟨?_, ?_⟩
      · rw [hadded.1]
      · simpa [updated, htypes, List.append_assoc] using hadded.2

/-- `metadata.decode_type_section` accepts a vector span of admissible signatures and adds them. -/
theorem metadata.decode_type_section.profile_complete (data : Slice U8) (pos : Usize)
    (env : metadata.Env) (types : List wasm_types.FuncType) (next : Usize)
    (hb : At (VecEncoding FuncTypeEncoding) data pos types next)
    (ht : ∀ ft ∈ types, Profile.FuncTypeWithinLimits ft)
    (hsize : env.types.val.length ≤ pos.val) :
    ∃ result, metadata.decode_type_section data pos env = .ok (.Ok next, result) ∧
      TypesAdded env result types := by
  obtain ⟨count, middle, hc, hcount, hentries⟩ := hb.vector_split
  obtain ⟨result, hr, hp⟩ := metadata.decode_type_section_loop.profile_complete
    data env count middle 0#u32 types next hentries (by simpa using hc.symm) ht
    (by have := hcount.span; omega)
  refine ⟨result, ?_, hp⟩
  simp [metadata.decode_type_section, reader.read_u32_leb.complete data pos count middle hcount,
    core.result.Result.Insts.CoreOpsTry.branch, hr]

end Itasca

end
