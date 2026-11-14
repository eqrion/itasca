import Itasca.Module.Env.Encoding
import Itasca.Module.Sections.Tail
import Itasca.Module.Sections.Data
import Itasca.Module.Sections.ElementHeader

/-!
Sections, each formerly its own module: Preservation, Validity, Semantics, Requirements.
-/

/-! ## Preservation -/

section

/-!
# Preservation along section runs

`Effect.represents` and `Run.represents` show that decoding sections keeps `Represents` between
the environment and the ghost declarations. `Effect.signatureBounded` and `Run.signatureBounded`
keep the signature bounds. `metadata.Env.new.profile_declarations` shows that the empty environment
starts all of these invariants, and `ImportsAdded.represents` covers the import section.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- The extracted initial environment represents the empty declaration prefix, is valid and
bounded, and has phase `0`. -/
theorem metadata.Env.new.profile_declarations : metadata.Env.new ⦃ env =>
    ModuleEnv.Represents env {} ∧ ModuleEnv.Valid env ∧
    ModuleEnv.SignatureBounded env 0 ∧ ModuleEnv.Bounded env 0 ∧ ModuleEnv.Phase 0 {} ⦄ := by
  unfold metadata.Env.new
  simp only [WP.spec_ok]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · constructor <;> try rfl
    constructor <;> simp [ModuleEnv.importedFuncs, ModuleEnv.importedGlobals,
      ModuleEnv.importedTables, ModuleEnv.importedMems]
  · constructor <;> simp [ModuleReferences.Coherent, ModuleReferences.collected]
  · simp [ModuleEnv.SignatureBounded]
  · constructor <;> simp
  · simp [ModuleEnv.Phase]

end Itasca

namespace Itasca.ModuleSections

theorem ImportsAdded.types {env entries result} (h : ImportsAdded env entries result) :
    result.types = env.types := by
  induction h with
  | nil => rfl
  | @snoc entries before after entry hp ha ih =>
      obtain ⟨_, ha⟩ := ha
      cases hd : entry.desc <;> simp only [hd] at ha
      · obtain ⟨_, _, he, _⟩ := ha
        have ht := congrArg metadata.Env.types he
        change after.types = before.types at ht
        exact ht.trans ih
      · have ht := congrArg metadata.Env.types ha.1
        change after.types = before.types at ht
        exact ht.trans ih
      · have ht := congrArg metadata.Env.types ha.1
        change after.types = before.types at ht
        exact ht.trans ih
      · have ht := congrArg metadata.Env.types ha.1
        change after.types = before.types at ht
        exact ht.trans ih


open ModuleEnv

/-- Adding one import appends it to the declared imports and keeps the environment representing
the declarations, provided no functions, globals, tables or memories are declared yet. -/
theorem ImportAdded.represents {env result entry decls}
    (h : ImportAdded env result entry) (hr : Represents env decls)
    (hf : decls.functions = []) (hg : decls.globals = [])
    (ht : decls.tables = []) (hm : decls.memories = []) :
    Represents result { decls with imports := decls.imports ++ [rawImport entry] } := by
  have hidx : env.func_type_indices.val = [] := hr.functions.symm.trans hf
  have hglobals : env.globals.val = [] := hr.globals.symm.trans hg
  obtain ⟨hi, hd⟩ := h
  cases he : entry.desc <;> simp only [he] at hd
  · obtain ⟨ft, hresolve, henv, hfuncs, hnum⟩ := hd
    rw [henv]
    refine ⟨hr.types, ?_, hr.functions, hr.globals, hr.exports, hr.start, hr.elements, hr.dataCount, ?_⟩
    · simp only [hi, List.map_append, List.map_cons, List.map_nil, hr.imports]
    · constructor
      · simpa [importedFuncs, hi, he, hidx, hfuncs] using
          List.rel_append hr.cache.funcs (List.Forall₂.cons hresolve .nil)
      · simpa [importedFuncs, hi, he, hnum] using hr.cache.numFuncs
      · simpa [importedGlobals, hi, he] using hr.cache.globals
      · simpa [importedGlobals, hi, he] using hr.cache.numGlobals
      · simpa [importedTables, hi, he] using hr.cache.tables
      · simpa [importedMems, hi, he] using hr.cache.memories
  · rename_i tt
    obtain ⟨henv, htables, _⟩ := hd
    rw [henv]
    refine ⟨hr.types, ?_, hr.functions, hr.globals, hr.exports, hr.start, hr.elements, hr.dataCount, ?_⟩
    · simp only [hi, List.map_append, List.map_cons, List.map_nil, hr.imports]
    · constructor
      · simpa [importedFuncs, hi, he] using hr.cache.funcs
      · simpa [importedFuncs, hi, he] using hr.cache.numFuncs
      · simpa [importedGlobals, hi, he] using hr.cache.globals
      · simpa [importedGlobals, hi, he] using hr.cache.numGlobals
      · simpa [importedTables, hi, he, htables, ht] using congrArg (· ++ [tt]) hr.cache.tables
      · simpa [importedMems, hi, he] using hr.cache.memories
  · rename_i mt
    obtain ⟨henv, hmemories, _, _⟩ := hd
    rw [henv]
    refine ⟨hr.types, ?_, hr.functions, hr.globals, hr.exports, hr.start, hr.elements, hr.dataCount, ?_⟩
    · simp only [hi, List.map_append, List.map_cons, List.map_nil, hr.imports]
    · constructor
      · simpa [importedFuncs, hi, he] using hr.cache.funcs
      · simpa [importedFuncs, hi, he] using hr.cache.numFuncs
      · simpa [importedGlobals, hi, he] using hr.cache.globals
      · simpa [importedGlobals, hi, he] using hr.cache.numGlobals
      · simpa [importedTables, hi, he] using hr.cache.tables
      · simpa [importedMems, hi, he, hmemories, hm] using congrArg (· ++ [mt]) hr.cache.memories
  · rename_i gt
    obtain ⟨henv, htypes, hnum⟩ := hd
    rw [henv]
    refine ⟨hr.types, ?_, hr.functions, hr.globals, hr.exports, hr.start, hr.elements, hr.dataCount, ?_⟩
    · simp only [hi, List.map_append, List.map_cons, List.map_nil, hr.imports]
    · constructor
      · simpa [importedFuncs, hi, he] using hr.cache.funcs
      · simpa [importedFuncs, hi, he] using hr.cache.numFuncs
      · simpa [importedGlobals, hi, he, hglobals, htypes] using congrArg (· ++ [gt]) hr.cache.globals
      · simpa [importedGlobals, hi, he, hnum] using hr.cache.numGlobals
      · simpa [importedTables, hi, he] using hr.cache.tables
      · simpa [importedMems, hi, he] using hr.cache.memories

/-- Adding a vector of imports appends them to the declared imports and keeps the environment
representing the declarations. -/
theorem ImportsAdded.represents {env result entries decls}
    (h : ImportsAdded env entries result) (hr : Represents env decls)
    (hf : decls.functions = []) (hg : decls.globals = [])
    (ht : decls.tables = []) (hm : decls.memories = []) :
    Represents result { decls with imports := decls.imports ++ entries.map rawImport } := by
  induction h generalizing decls with
  | nil => simpa using hr
  | snoc hp ha ih =>
    have hr' := ih hr hf hg ht hm
    have hr'' := ha.represents hr' hf hg ht hm
    simpa only [List.map_append, List.map_cons, List.map_nil, List.append_assoc] using hr''

end Itasca.ModuleSections

namespace Itasca.ModuleEnv

open ModuleBinary ModuleSections

/-- Every section preserves the bound on nested parameter vectors. Newly declared signatures obtain
their bound from their own byte span. -/
theorem Effect.signatureBounded {data pos env before id next result after}
    (h : Effect data pos env before id next result after) (hs : SignatureBounded env pos.val) :
    SignatureBounded result next.val := by
  have hspan := h.span
  have hm := hs.mono hspan.1
  cases h with
  | types ha hb hv => exact hs.of_types_added ha hb
  | imports ha hb => simpa only [SignatureBounded, ha.types] using hm
  | functions ha hb =>
      have ht := congrArg metadata.Env.types ha.1
      change result.types = env.types at ht
      simpa only [SignatureBounded, ht] using hm
  | tables ha hb hv =>
      have ht := congrArg metadata.Env.types ha.1
      change result.types = env.types at ht
      simpa only [SignatureBounded, ht] using hm
  | memories ha hb hv hc =>
      have ht := congrArg metadata.Env.types ha.1
      change result.types = env.types at ht
      simpa only [SignatureBounded, ht] using hm
  | globals ha hb hv =>
      have ht := congrArg metadata.Env.types ha.1
      change result.types = env.types at ht
      simpa only [SignatureBounded, ht] using hm
  | exports ha hb =>
      have ht := congrArg metadata.Env.types ha.unchanged
      change result.types = env.types at ht
      simpa only [SignatureBounded, ht] using hm
  | start he hb hv => simpa only [SignatureBounded, he] using hm
  | elements ha hb hv =>
      have ht := congrArg metadata.Env.types ha.1
      change result.types = env.types at ht
      simpa only [SignatureBounded, ht] using hm

  | dataCount he hb => simpa only [SignatureBounded, he] using hm


/-- A section update in increasing section order keeps the environment representing the
declarations, including the merged index-space caches. -/
theorem Effect.represents {data pos env before id next result after last}
    (h : Effect data pos env before id next result after) (hr : Represents env before)
    (hp : Phase last before) (horder : last < (sectionRank id).val) : Represents result after := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hp
  cases h with
  | types ha hb hv =>
    change last < 1 at horder
    have ht := h1 (by simpa using horder)
    have hi : env.imports.val = [] := by
      have he := hr.imports.symm.trans (h2 (by scalar_tac))
      simpa using he
    have hidx : env.func_type_indices.val = [] := hr.functions.symm.trans (h3 (by scalar_tac))
    have hfuncs : env.func_types.val = [] := by
      have hl := hr.cache.funcs.length_eq
      simpa [importedFuncs, hi, hidx] using hl.symm
    rw [ha.1]
    refine ⟨?_, hr.imports, hr.functions, hr.globals, hr.exports, hr.start, hr.elements, hr.dataCount, ?_⟩
    · dsimp only
      rw [ha.2, ← hr.types, ht, List.nil_append]
    · constructor
      · simp [importedFuncs, hi, hidx, hfuncs]
      · exact hr.cache.numFuncs
      · exact hr.cache.globals
      · exact hr.cache.numGlobals
      · exact hr.cache.tables
      · exact hr.cache.memories
  | imports ha hb =>
    change last < 2 at horder
    have hi := ha.represents hr (h3 (by scalar_tac)) (h6 (by scalar_tac))
      (h4 (by scalar_tac)) (h5 (by scalar_tac))
    simpa only [h2 (by scalar_tac), List.nil_append] using hi
  | functions ha hb =>
    change last < 3 at horder
    have hf := h3 (by simpa using horder)
    rw [ha.1]
    refine ⟨hr.types, hr.imports, ?_, hr.globals, hr.exports, hr.start, hr.elements, hr.dataCount, ?_⟩
    · dsimp only
      rw [ha.2.1, ← hr.functions, hf, List.nil_append]
    · constructor
      · simpa only [ha.2.1, ha.2.2.1, List.append_assoc] using
          List.rel_append hr.cache.funcs ha.2.2.2
      · exact hr.cache.numFuncs
      · exact hr.cache.globals
      · exact hr.cache.numGlobals
      · exact hr.cache.tables
      · exact hr.cache.memories
  | tables ha hb hv =>
    change last < 4 at horder
    have ht := h4 (by simpa using horder)
    rw [ha.1]
    refine ⟨hr.types, hr.imports, hr.functions, hr.globals, hr.exports, hr.start, hr.elements, hr.dataCount, ?_⟩
    constructor
    · exact hr.cache.funcs
    · exact hr.cache.numFuncs
    · exact hr.cache.globals
    · exact hr.cache.numGlobals
    · dsimp only
      rw [ha.2, hr.cache.tables, ht, List.append_nil]
    · exact hr.cache.memories
  | memories ha hb hv hc =>
    change last < 5 at horder
    have hm := h5 (by simpa using horder)
    rw [ha.1]
    refine ⟨hr.types, hr.imports, hr.functions, hr.globals, hr.exports, hr.start, hr.elements, hr.dataCount, ?_⟩
    constructor
    · exact hr.cache.funcs
    · exact hr.cache.numFuncs
    · exact hr.cache.globals
    · exact hr.cache.numGlobals
    · exact hr.cache.tables
    · dsimp only
      rw [ha.2, hr.cache.memories, hm, List.append_nil]
  | globals ha hb hv =>
    change last < 6 at horder
    have hg := h6 (by simpa using horder)
    rw [ha.1]
    refine ⟨hr.types, hr.imports, hr.functions, ?_, hr.exports, hr.start, hr.elements, hr.dataCount, ?_⟩
    · dsimp only
      rw [ha.2.1, ← hr.globals, hg, List.nil_append]
    · constructor
      · exact hr.cache.funcs
      · exact hr.cache.numFuncs
      · dsimp only
        rw [ha.2.1, ha.2.2.1, hr.cache.globals, List.map_append, List.append_assoc]
      · exact hr.cache.numGlobals
      · exact hr.cache.tables
      · exact hr.cache.memories
  | exports ha hb =>
    change last < 7 at horder
    have he := h7 (by simpa using horder)
    rw [ha.unchanged]
    refine ⟨hr.types, hr.imports, hr.functions, hr.globals, ?_, hr.start, hr.elements, hr.dataCount, ?_⟩
    · dsimp only
      rw [ha.exports, List.map_append, ← hr.exports, he, List.nil_append]
    · exact ⟨hr.cache.funcs, hr.cache.numFuncs, hr.cache.globals, hr.cache.numGlobals, hr.cache.tables, hr.cache.memories⟩
  | start he hb hv =>
    change last < 8 at horder
    rw [he]
    exact ⟨hr.types, hr.imports, hr.functions, hr.globals, hr.exports, rfl, hr.elements, hr.dataCount, ⟨hr.cache.funcs, hr.cache.numFuncs, hr.cache.globals, hr.cache.numGlobals, hr.cache.tables, hr.cache.memories⟩⟩
  | elements ha hb hv =>
    change last < 9 at horder
    have he := h9 (by simpa using horder)
    rw [ha.1]
    refine ⟨hr.types, hr.imports, hr.functions, hr.globals, hr.exports, hr.start, ?_, hr.dataCount, ?_⟩
    · dsimp only
      rw [ha.2.1, List.map_append, ← hr.elements, he, List.nil_append]
    · exact ⟨hr.cache.funcs, hr.cache.numFuncs, hr.cache.globals, hr.cache.numGlobals, hr.cache.tables, hr.cache.memories⟩

  | dataCount he hb =>
    rw [he]
    exact ⟨hr.types, hr.imports, hr.functions, hr.globals, hr.exports, hr.start,
      hr.elements, rfl, ⟨hr.cache.funcs, hr.cache.numFuncs, hr.cache.globals,
      hr.cache.numGlobals, hr.cache.tables, hr.cache.memories⟩⟩


/-- A run of sections keeps the environment representing the declarations. -/
theorem Run.represents {data initial decls start initialId after afterDecls next id}
    (h : Run data initial decls start initialId after afterDecls next id)
    (hr : Represents initial decls) (hp : Phase initialId.val decls) :
    Represents after afterDecls := by
  induction h with
  | nil => exact hr
  | custom _ _ ih => exact ih
  | step previous horder hh he ih => exact he.represents ih (previous.phase hp) horder

/-- A run of sections keeps the signature bound. -/
theorem Run.signatureBounded {data initial decls start initialId after afterDecls next id}
    (h : Run data initial decls start initialId after afterDecls next id)
    (hs : SignatureBounded initial start.val) : SignatureBounded after next.val := by
  induction h with
  | nil => exact hs
  | custom _ hb ih => exact ih.mono hb.span.1
  | step _ horder hh he ih => exact he.signatureBounded (ih.mono (Nat.le_of_lt hh.span.1))

end Itasca.ModuleEnv

end

/-! ## Validity -/

section

/-!
# Validity of decoded environments

`Effect.valid` shows that each section effect, applied in increasing section order, preserves
`Valid`. The per-section steps are `ImportsAdded.valid` and `ExportsAdded.valid`, and the
helpers `Early` and `SameCore` capture which parts of the environment a section leaves alone.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleEnv

open ModuleBinary ModuleSections

/-- Before globals, all consumers of the cached index spaces are absent. -/
structure Early (env : metadata.Env) : Prop where
  globals : env.globals.val = []
  exports : env.exports.val = []
  start : env.start = none
  elements : env.elements.val = []

theorem Early.of_phase {env decls last} (hr : Represents env decls)
    (hp : Phase last decls) (hl : last < 6) : Early env := by
  rcases hp with ⟨_, _, _, _, _, hg, he, hs, hm, _⟩
  refine ⟨hr.globals.symm.trans (hg hl), ?_, hr.start.symm.trans (hs (by omega)), ?_⟩
  · have h := hr.exports.symm.trans (he (by omega))
    exact List.map_eq_nil_iff.mp h
  · have h := hr.elements.symm.trans (hm (by omega))
    exact List.map_eq_nil_iff.mp h

theorem Early.valid {env} (h : Early env)
    (ht : ∀ ft ∈ env.types.val, Profile.FuncTypeAdmissible ft)
    (htt : ∀ tt ∈ env.table_types.val, ModuleTranslation.LimitsValid tt.limits (2 ^ 32 - 1))
    (hmt : ∀ mt ∈ env.mem_types.val, ModuleTranslation.LimitsValid mt.limits (2 ^ 16))
    (hmc : env.mem_types.val.length ≤ 1)
    (hi : ∀ entry ∈ env.imports.val, Utf8 entry.module.val ∧ Utf8 entry.name.val)
    (href : ModuleReferences.Coherent env) : Valid env := by
  refine ⟨ht, htt, hmt, hmc, ?_, hi, ?_, ?_, ?_, ?_, ?_, href⟩
  all_goals simp [h.globals, h.exports, h.start, h.elements]

end Itasca.ModuleEnv

namespace Itasca.ModuleSections

open ModuleEnv ModuleBinary

theorem ImportAdded.early {env result entry} (h : ImportAdded env result entry)
    (he : Early env) : Early result := by
  obtain ⟨_, h⟩ := h
  cases hd : entry.desc <;> simp only [hd] at h
  · obtain ⟨_, _, h, _⟩ := h
    rw [h]; exact ⟨he.globals, he.exports, he.start, he.elements⟩
  all_goals rw [h.1]; exact ⟨he.globals, he.exports, he.start, he.elements⟩

theorem ImportAdded.valid {env result entry} (h : ImportAdded env result entry)
    (hv : Valid env) (he : Early env)
    (hn : Utf8 entry.module.val ∧ Utf8 entry.name.val) : Valid result := by
  have her := h.early he
  obtain ⟨hi, ha⟩ := h
  have hnames : ∀ e ∈ result.imports.val, Utf8 e.module.val ∧ Utf8 e.name.val := by
    simp only [hi, List.mem_append, List.mem_singleton]
    intro e hm
    rcases hm with hm | rfl
    · exact hv.imports e hm
    · exact hn
  cases hd : entry.desc <;> simp only [hd] at ha
  · obtain ⟨ft, hft, heq, hfs, hnum⟩ := ha
    apply her.valid <;> first | exact hnames | (rw [heq]; exact hv.types) |
      (rw [heq]; exact hv.tables) | (rw [heq]; exact hv.memories) |
      (rw [heq]; exact hv.memoryCount) |
      (rw [heq]; exact hv.references)
  · obtain ⟨heq, hts, hlim⟩ := ha
    apply her.valid
    · (rw [heq]; exact hv.types)
    · intro tt hm
      rw [hts] at hm
      rcases List.mem_append.mp hm with hm | hm
      · exact hv.tables _ hm
      · simpa using (List.mem_singleton.mp hm ▸ hlim)
    · (rw [heq]; exact hv.memories)
    · (rw [heq]; exact hv.memoryCount)
    · exact hnames
    · rw [heq]; exact hv.references
  · obtain ⟨heq, hms, hcount, hlim⟩ := ha
    apply her.valid
    · (rw [heq]; exact hv.types)
    · (rw [heq]; exact hv.tables)
    · intro mt hm
      rw [hms] at hm
      rcases List.mem_append.mp hm with hm | hm
      · exact hv.memories _ hm
      · simpa using (List.mem_singleton.mp hm ▸ hlim)
    · exact hcount
    · exact hnames
    · rw [heq]; exact hv.references
  · obtain ⟨heq, hgs, hnum⟩ := ha
    apply her.valid <;> first | exact hnames | (rw [heq]; exact hv.types) |
      (rw [heq]; exact hv.tables) | (rw [heq]; exact hv.memories) |
      (rw [heq]; exact hv.memoryCount) |
      (rw [heq]; exact hv.references)

theorem ImportsAdded.early {env entries result} (h : ImportsAdded env entries result)
    (he : Early env) : Early result := by
  induction h with
  | nil => exact he
  | snoc hp ha ih => exact ha.early ih

theorem ImportsAdded.valid {env entries result} (h : ImportsAdded env entries result)
    (hv : Valid env) (he : Early env)
    (hn : ∀ e ∈ entries, Utf8 e.module.val ∧ Utf8 e.name.val) : Valid result := by
  induction h with
  | nil => exact hv
  | snoc hp ha ih =>
    exact ha.valid (ih (by intro e hm; exact hn e (by simp [hm])))
      (hp.early he) (hn _ (by simp))

end Itasca.ModuleSections

namespace Itasca.ModuleEnv

/-- Later sections leave the function, table, memory and global index spaces unchanged. -/
structure SameCore (env result : metadata.Env) : Prop where
  funcs : result.func_types = env.func_types
  tables : result.table_types = env.table_types
  memories : result.mem_types = env.mem_types
  globals : result.global_types = env.global_types
  numGlobals : result.num_imported_globals = env.num_imported_globals

theorem SameCore.constant {env result e t} (h : SameCore env result)
    (hv : ModuleConstants.Valid env e t) : ModuleConstants.Valid result e t := by
  cases hv with
  | i32 value => exact .i32 value
  | i64 value => exact .i64 value
  | f32 value => exact .f32 value
  | f64 value => exact .f64 value
  | v128 low high => exact .v128 low high
  | refNull ty => exact .refNull ty
  | refFunc idx hi => exact .refFunc idx (by simpa [h.funcs] using hi)
  | globalGet idx gt hi hgt himp hc =>
    exact .globalGet idx gt (by simpa [h.globals] using hi)
      (by simpa [h.globals] using hgt) (by simpa [h.numGlobals] using himp) hc

theorem SameCore.export {env result e xt} (h : SameCore env result)
    (hv : ModuleExternals.ExportResolves env e xt) : ModuleExternals.ExportResolves result e xt := by
  cases hd : e.desc <;> simpa only [ModuleExternals.ExportResolves, hd,
    h.funcs, h.tables, h.memories, h.globals] using hv

theorem SameCore.element {env result entry} (h : SameCore env result)
    (hv : ModuleSections.ElementValid env entry) : ModuleSections.ElementValid result entry := by
  refine ⟨?_, fun e hm => h.constant (hv.2 e hm)⟩
  cases hm : entry.mode with
  | Passive => trivial
  | Declarative => trivial
  | Active idx offset =>
    obtain ⟨hi, ht, ho⟩ := (show ∃ hi : idx.val < env.table_types.val.length,
      env.table_types.val[idx.val].elem = entry.elem ∧ ModuleConstants.Valid env offset .I32 from by simpa [hm] using hv.1)
    exact ⟨by simpa [h.tables] using hi, by simpa [h.tables] using ht, h.constant ho⟩

theorem SameCore.start {env result} {idx : U32} (h : SameCore env result)
    (hv : ∃ hi : idx.val < env.func_types.val.length,
      env.func_types.val[idx.val].params.val = [] ∧ env.func_types.val[idx.val].results.val = []) :
    ∃ hi : idx.val < result.func_types.val.length,
      result.func_types.val[idx.val].params.val = [] ∧ result.func_types.val[idx.val].results.val = [] := by
  simpa only [h.funcs] using hv

end Itasca.ModuleEnv

namespace Itasca.ModuleSections

open ModuleEnv ModuleBinary

theorem ExportAdded.valid {env result entry} (h : ExportAdded env result entry)
    (hv : Valid env) (helements : env.elements.val = []) (hn : Utf8 entry.name.val) : Valid result := by
  obtain ⟨he, hexports, hnew, hresolve, href⟩ := h
  have hc : SameCore env result := by constructor <;> rw [he]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [he]; exact hv.types
  · rw [he]; exact hv.tables
  · rw [he]; exact hv.memories
  · rw [he]; exact hv.memoryCount
  · intro g hg
    have hg' : g ∈ env.globals.val := by simpa only [congrArg metadata.Env.globals he] using hg
    exact hc.constant (hv.globals g hg')
  · rw [he]; exact hv.imports
  · intro e hm
    rw [hexports] at hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hv.exportNames _ hm
    · exact List.mem_singleton.mp hm ▸ hn
  · rw [hexports, List.map_append, List.map_singleton]
    exact List.Nodup.append hv.distinctExports (by simp) (by simpa using hnew)
  · intro e hm
    rw [hexports] at hm
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨xt, hx⟩ := hv.exports _ hm
      exact ⟨xt, hc.export hx⟩
    · obtain rfl := List.mem_singleton.mp hm
      obtain ⟨xt, hx⟩ := hresolve
      exact ⟨xt, hc.export hx⟩
  · intro idx hs
    have hs' : env.start = some idx := by simpa only [congrArg metadata.Env.start he] using hs
    exact hc.start (hv.start idx hs')
  · intro e hm
    have hm' : e ∈ env.elements.val := by simpa only [congrArg metadata.Env.elements he] using hm
    exact hc.element (hv.elements _ hm')
  · have hrefold := hv.references
    unfold ModuleReferences.Coherent ModuleReferences.collected at hrefold ⊢
    rw [href, hrefold]
    rw [he]
    dsimp only
    simp only [hexports, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    simp [helements, List.append_assoc]

theorem ExportsAdded.valid {env entries result} (h : ExportsAdded env entries result)
    (hv : Valid env) (helements : env.elements.val = []) (hn : ∀ e ∈ entries, Utf8 e.name.val) : Valid result := by
  induction h with
  | nil => exact hv
  | snoc hp ha ih =>
    exact ha.valid (ih (by intro e hm; exact hn e (by simp [hm])))
      (by rw [hp.unchanged]; exact helements) (hn _ (by simp))

end Itasca.ModuleSections

namespace Itasca.ModuleEnv

open ModuleBinary ModuleSections

/-- A section effect in increasing section order preserves `Valid`, including name well-formedness,
export uniqueness and initializer validity. -/
theorem Effect.valid {data pos env before id next result after last}
    (h : Effect data pos env before id next result after)
    (hr : Represents env before) (hv : Valid env)
    (hp : Phase last before) (ho : last < (sectionRank id).val) : Valid result := by
  cases h with
  | types ha hb ht =>
    have hearly := Early.of_phase hr hp (by change last < 1 at ho; omega)
    obtain ⟨he, hts⟩ := ha
    have her : Early result := by rw [he]; exact ⟨hearly.globals, hearly.exports, hearly.start, hearly.elements⟩
    apply her.valid
    · intro ft hm
      rw [hts] at hm
      rcases List.mem_append.mp hm with hm | hm
      · exact hv.types _ hm
      · exact ht _ hm
    · rw [he]; exact hv.tables
    · rw [he]; exact hv.memories
    · rw [he]; exact hv.memoryCount
    · rw [he]; exact hv.imports
    · rw [he]; exact hv.references
  | imports ha hb =>
    apply ha.valid hv (Early.of_phase hr hp (by change last < 2 at ho; omega))
    intro entry hm
    obtain ⟨bytes, hbytes, _⟩ := hb
    obtain ⟨bs, he⟩ := hbytes.member (List.mem_map.mpr ⟨entry, hm, rfl⟩)
    obtain ⟨_, _, _, hm, hn, _, _⟩ := he
    exact ⟨hm.2, hn.2⟩
  | functions ha hb =>
    have hearly := Early.of_phase hr hp (by change last < 3 at ho; omega)
    obtain ⟨he, hindices, hfuncs, hresolve⟩ := ha
    have her : Early result := by rw [he]; exact ⟨hearly.globals, hearly.exports, hearly.start, hearly.elements⟩
    apply her.valid <;> first | (rw [he]; exact hv.types) |
      (rw [he]; exact hv.tables) | (rw [he]; exact hv.memories) |
      (rw [he]; exact hv.memoryCount) |
      (rw [he]; exact hv.imports) |
      (rw [he]; exact hv.references)
  | tables ha hb ht =>
    have hearly := Early.of_phase hr hp (by change last < 4 at ho; omega)
    obtain ⟨he, hts⟩ := ha
    have her : Early result := by rw [he]; exact ⟨hearly.globals, hearly.exports, hearly.start, hearly.elements⟩
    apply her.valid
    · rw [he]; exact hv.types
    · intro tt hm
      rw [hts] at hm
      rcases List.mem_append.mp hm with hm | hm
      · exact hv.tables _ hm
      · exact ht _ hm
    · rw [he]; exact hv.memories
    · rw [he]; exact hv.memoryCount
    · rw [he]; exact hv.imports
    · rw [he]; exact hv.references
  | memories ha hb ht hcount =>
    have hearly := Early.of_phase hr hp (by change last < 5 at ho; omega)
    obtain ⟨he, hms⟩ := ha
    have her : Early result := by rw [he]; exact ⟨hearly.globals, hearly.exports, hearly.start, hearly.elements⟩
    apply her.valid
    · rw [he]; exact hv.types
    · rw [he]; exact hv.tables
    · intro mt hm
      rw [hms] at hm
      rcases List.mem_append.mp hm with hm | hm
      · exact hv.memories _ hm
      · exact ht _ hm
    · simpa [max_eq_right hv.memoryCount] using hcount
    · rw [he]; exact hv.imports
    · rw [he]; exact hv.references
  | globals ha hb hg =>
    have hearly := Early.of_phase hr hp (by change last < 6 at ho; exact ho)
    obtain ⟨he, hgs, htypes, href⟩ := ha
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [he]; exact hv.types
    · rw [he]; exact hv.tables
    · rw [he]; exact hv.memories
    · rw [he]; exact hv.memoryCount
    · intro g hm
      exact hg _ (by simpa [hgs, hearly.globals] using hm)
    · rw [he]; exact hv.imports
    all_goals try (rw [he]; simp [hearly.exports, hearly.start, hearly.elements]; done)
    · unfold ModuleReferences.Coherent ModuleReferences.collected
      rw [he]
      dsimp only
      rw [href, hgs]
      have hold := hv.references
      unfold ModuleReferences.Coherent ModuleReferences.collected at hold
      simp [hearly.globals, hearly.exports, hearly.elements] at hold
      simp [hold, hearly.globals, hearly.exports, hearly.elements]
  | exports ha hb =>
    apply ha.valid hv
    · have he := hp.2.2.2.2.2.2.2.2.1 (by change last < 7 at ho; omega)
      exact List.map_eq_nil_iff.mp (hr.elements.symm.trans he)
    intro entry hm
    obtain ⟨bytes, hbytes, _⟩ := hb
    obtain ⟨bs, he⟩ := hbytes.member (List.mem_map.mpr ⟨entry, hm, rfl⟩)
    obtain ⟨_, _, hn, _, _⟩ := he
    exact hn.2
  | start he hb hstart =>
    have hc : SameCore env result := by constructor <;> rw [he]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [he]; exact hv.types
    · rw [he]; exact hv.tables
    · rw [he]; exact hv.memories
    · rw [he]; exact hv.memoryCount
    · intro g hg
      exact hc.constant (hv.globals g (by simpa only [congrArg metadata.Env.globals he] using hg))
    · rw [he]; exact hv.imports
    · rw [he]; exact hv.exportNames
    · rw [he]; exact hv.distinctExports
    · intro e hm
      obtain ⟨xt, hx⟩ := hv.exports e (by simpa only [congrArg metadata.Env.exports he] using hm)
      exact ⟨xt, hc.export hx⟩
    · intro idx hs
      rw [he] at hs
      cases Option.some.inj hs
      exact hc.start hstart
    · intro e hm
      exact hc.element (hv.elements e (by simpa only [congrArg metadata.Env.elements he] using hm))
    · rw [he]; exact hv.references
  | elements ha hb ht =>
    obtain ⟨he, hes, href⟩ := ha
    have hc : SameCore env result := by constructor <;> rw [he]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [he]; exact hv.types
    · rw [he]; exact hv.tables
    · rw [he]; exact hv.memories
    · rw [he]; exact hv.memoryCount
    · intro g hg
      exact hc.constant (hv.globals g (by simpa only [congrArg metadata.Env.globals he] using hg))
    · rw [he]; exact hv.imports
    · rw [he]; exact hv.exportNames
    · rw [he]; exact hv.distinctExports
    · intro e hm
      obtain ⟨xt, hx⟩ := hv.exports e (by simpa only [congrArg metadata.Env.exports he] using hm)
      exact ⟨xt, hc.export hx⟩
    · intro idx hs
      exact hc.start (hv.start idx (by simpa only [congrArg metadata.Env.start he] using hs))
    · intro e hm
      rw [hes] at hm
      rcases List.mem_append.mp hm with hm | hm
      · exact hc.element (hv.elements e hm)
      · exact hc.element (ht e hm)
    · have hrefold := hv.references
      unfold ModuleReferences.Coherent ModuleReferences.collected at hrefold ⊢
      rw [href, hrefold]
      rw [he]
      dsimp only
      simp only [hes, List.flatMap_append, List.append_assoc]
  | dataCount he hbytes =>
    have hc : SameCore env result := by constructor <;> rw [he]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [he]; exact hv.types
    · rw [he]; exact hv.tables
    · rw [he]; exact hv.memories
    · rw [he]; exact hv.memoryCount
    · intro g hg
      exact hc.constant (hv.globals g (by simpa only [congrArg metadata.Env.globals he] using hg))
    · rw [he]; exact hv.imports
    · rw [he]; exact hv.exportNames
    · rw [he]; exact hv.distinctExports
    · intro e hm
      obtain ⟨xt, hx⟩ := hv.exports e (by simpa only [congrArg metadata.Env.exports he] using hm)
      exact ⟨xt, hc.export hx⟩
    · intro idx hs
      exact hc.start (hv.start idx (by simpa only [congrArg metadata.Env.start he] using hs))
    · intro e hm
      exact hc.element (hv.elements e (by simpa only [congrArg metadata.Env.elements he] using hm))
    · rw [he]; exact hv.references

end Itasca.ModuleEnv

end

/-! ## Semantics -/

section

/-!
# Semantic contract of the environment parser

`metadata.validate_env.profile_semantic_spec` shows that for arbitrary bytes, `metadata.validate_env`
either rejects or returns an environment with `SemanticPostWith`. That is a `Represents`
declaration record, `Valid`, signature and size bounds, and an independent `PrefixEncoding` of the
consumed bytes. The same holds for `metadata.validate_env_with` with total custom-section hooks.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleEnv

/-- Validity follows a run of sections, alongside the raw declaration representation. -/
theorem Run.valid {data initial decls start initialId after afterDecls next id}
    (h : Run data initial decls start initialId after afterDecls next id)
    (hr : Represents initial decls) (hv : Valid initial) (hp : Phase initialId.val decls) :
    Valid after := by
  induction h with
  | nil => exact hv
  | custom _ _ ih => exact ih
  | step previous horder hh he ih =>
      exact he.valid (previous.represents hr hp) ih (previous.phase hp) horder

/-- An accepted environment comes with a declaration record that represents it, its semantic
checks, the signature and size bounds needed by the code and data parsers, and the independent byte
encoding of the consumed prefix. -/
def SemanticPostWith (data : Slice U8) : core.result.Result (metadata.Env × Usize) error.Error → Prop
  | .Err _ => True
  | .Ok (env, next) => ∃ decls, Represents env decls ∧ Valid env ∧
      SignatureBounded env next.val ∧ Bounded env next.val ∧
      ModuleBinary.At (fun ds bs => PrefixEncoding ds bs) data 0#usize decls next

/-- The run-based postcondition implies the semantic one. -/
theorem PostWith.semantic {data result} (h : PostWith data result) : SemanticPostWith data result := by
  cases result with
  | Err _ => trivial
  | Ok pair =>
      obtain ⟨env, next⟩ := pair
      obtain ⟨initial, start, decls, last, hinit, hheader, hrun, hbound⟩ := h
      have hi := metadata.Env.new.profile_declarations
      rw [hinit] at hi
      simp only [WP.spec_ok] at hi
      obtain ⟨hr, hv, hs, _, hp⟩ := hi
      exact ⟨decls, hrun.represents hr hp, hrun.valid hr hv hp,
        hrun.signatureBounded (hs.mono (Nat.zero_le _)), hbound, hrun.encoding hheader⟩

end Itasca.ModuleEnv

namespace Itasca

/-- Arbitrary bytes either make `metadata.validate_env` reject or yield an independently encoded,
semantically valid declaration prefix with consistent caches. -/
theorem metadata.validate_env.profile_semantic_spec (data : Slice U8) :
    metadata.validate_env data ⦃ ModuleEnv.SemanticPostWith data ⦄ := by
  obtain ⟨result, hr, hp⟩ := WP.spec_imp_exists (metadata.validate_env.profile_spec data)
  rw [hr]
  simpa only [WP.spec_ok] using ModuleEnv.PostWith.semantic hp

end Itasca

end

/-! ## Requirements -/

section

/-!
# Declarative requirements of the environment

`SectionValid` states the semantic requirements of each declaration section against the
environment built so far. `Ready` says all slots through a given rank are complete, and
`Requirements` collects `SectionValid` for every section reached from a ready state. The
requirements contain no parser execution, so completeness can start from them. `StopAt` describes
where the greedy section scan ends.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleSections

/-- The semantic requirements for one import against the index spaces built so far. -/
def ImportValid (env : metadata.Env) (desc : metadata.ImportDesc) : Prop :=
  match desc with
  | .Func idx => idx.val < env.types.val.length
  | .Table tt => ModuleBinary.LimitsValid tt.limits limits.MAX_TABLE_ELEMS
  | .Memory mt => ModuleBinary.LimitsValid mt.limits limits.MAX_MEMORY_PAGES ∧
      env.mem_types.val.length + 1 ≤ 1
  | .Global _ => True

/-- The table types among the raw imports. -/
def rawTables (entries : List ModuleBinary.Import) : List wasm_types.TableType :=
  entries.filterMap (fun e => match e.desc with | .Table tt => some tt | _ => none)

/-- The memory types among the raw imports. -/
def rawMemories (entries : List ModuleBinary.Import) : List wasm_types.MemType :=
  entries.filterMap (fun e => match e.desc with | .Memory mt => some mt | _ => none)

/-- The imports are valid against `env`. Descriptor checks are separate from the cardinality limits
on the merged memory space, so imports can be processed in order. -/
structure ImportsValid (env : metadata.Env) (entries : List ModuleBinary.Import) : Prop where
  descriptors : ∀ e ∈ entries, match e.desc with
    | .Func idx => idx.val < env.types.val.length
    | .Table tt => ModuleBinary.LimitsValid tt.limits limits.MAX_TABLE_ELEMS
    | .Memory mt => ModuleBinary.LimitsValid mt.limits limits.MAX_MEMORY_PAGES
    | .Global _ => True
  memories : env.mem_types.val.length + (rawMemories entries).length ≤ 1

/-- A raw element segment is valid against `env`. An active segment names a table of its element
type with a valid `i32` offset, and every initializer is a valid constant of the element type. -/
def ElementValidRaw (env : metadata.Env) (entry : ModuleBinary.Element) : Prop :=
  (match entry.mode with
    | .Active idx offset => ∃ hi : idx.val < env.table_types.val.length,
        env.table_types.val[idx.val].elem = entry.elem ∧ ModuleConstants.Valid env offset .I32
    | .Passive | .Declarative => True) ∧
  ∀ init ∈ entry.init, ModuleConstants.Valid env init (ModuleConstants.referenceValueType entry.elem)

/-- The first import of a valid list is valid at the current index-space prefix. -/
theorem ImportsValid.head {env entry entries} (h : ImportsValid env (entry :: entries)) :
    ImportValid env entry.desc := by
  have hd := h.descriptors entry (by simp)
  have hm := h.memories
  cases he : entry.desc <;> simp only [he, ImportValid] at hd ⊢
  · exact hd
  · exact hd
  · refine ⟨hd, ?_⟩
    simp [rawMemories, he] at hm
    omega

/-- After the first import is added, the remaining imports are valid against the updated
environment. -/
theorem ImportsValid.tail {env result actual entries}
    (h : ImportsValid env (ModuleEnv.rawImport actual :: entries))
    (ha : ImportAdded env result actual) : ImportsValid result entries := by
  obtain ⟨_, ha⟩ := ha
  have hd : ∀ e ∈ entries, match e.desc with
      | .Func idx => idx.val < env.types.val.length
      | .Table tt => ModuleBinary.LimitsValid tt.limits limits.MAX_TABLE_ELEMS
      | .Memory mt => ModuleBinary.LimitsValid mt.limits limits.MAX_MEMORY_PAGES
      | .Global _ => True := fun e he => h.descriptors e (by simp [he])
  have hm := h.memories
  cases he : actual.desc <;> simp only [he] at ha
  · obtain ⟨_, _, hr, _, _⟩ := ha
    rw [hr]
    exact ⟨hd, by simpa [rawMemories, ModuleEnv.rawImport, he] using hm⟩
  · obtain ⟨hr, _, _⟩ := ha
    rw [hr]
    exact ⟨hd, by simpa [rawMemories, ModuleEnv.rawImport, he] using hm⟩
  · obtain ⟨hr, hs, _, _⟩ := ha
    rw [hr]
    refine ⟨hd, ?_⟩
    simp only
    rw [hs]
    have hl : (rawMemories (ModuleEnv.rawImport actual :: entries)).length = (rawMemories entries).length + 1 := by
      simp [rawMemories, ModuleEnv.rawImport, he]
    rw [hl] at hm
    simp only [List.length_append, List.length_singleton]
    omega
  · obtain ⟨hr, _, _⟩ := ha
    rw [hr]
    exact ⟨hd, by simpa [rawMemories, ModuleEnv.rawImport, he] using hm⟩

end Itasca.ModuleSections

namespace Itasca.ModuleEnv

/-- The greedy environment scan stops only at end of input or at a complete section header for the
code section (`10`) or data section (`11`). -/
def StopAt (data : Slice U8) (pos : Usize) : Prop :=
  pos = Slice.len data ∨ ∃ id first last,
    ModuleBinary.SectionHeader data pos id first last ∧ (id = 10#u8 ∨ id = 11#u8)

/-- All slots through rank `last` are complete in `decls`, including omitted empty sections, and
match the raw module `raw`. The environment `env` represents `decls`. -/
structure Ready (raw : ModuleBinary.Module) (last : Nat) (decls : Declarations)
    (env : metadata.Env) : Prop where
  represents : Represents env decls
  phase : Phase last decls
  types : 1 ≤ last → decls.types = raw.types
  imports : 2 ≤ last → decls.imports = raw.imports
  functions : 3 ≤ last → decls.functions = raw.functions
  tables : 4 ≤ last → decls.tables = raw.tables
  memories : 5 ≤ last → decls.memories = raw.memories
  globals : 6 ≤ last → decls.globals = raw.globals
  exports : 7 ≤ last → decls.exports = raw.exports
  start : 8 ≤ last → decls.start = raw.start
  elements : 9 ≤ last → decls.elements = raw.elements
  dataCount : 10 ≤ last → decls.dataCount = raw.dataCount

/-- The semantic requirements of declaration section rank `id` of `raw` against `env`. Binary
framing, UTF-8 names, and cursor and capacity bounds come separately from the grammar. -/
def SectionValid (raw : ModuleBinary.Module) (id : Nat) (env : metadata.Env) : Prop :=
  match id with
  | 1 => ∀ ft ∈ raw.types, Profile.FuncTypeAdmissible ft
  | 2 => ModuleSections.ImportsValid env raw.imports
  | 3 => ∀ idx ∈ raw.functions, idx.val < env.types.val.length
  | 4 => ∀ tt ∈ raw.tables, ModuleBinary.LimitsValid tt.limits limits.MAX_TABLE_ELEMS
  | 5 => (∀ mt ∈ raw.memories, ModuleBinary.LimitsValid mt.limits limits.MAX_MEMORY_PAGES) ∧
      env.mem_types.val.length + raw.memories.length ≤ 1
  | 6 => ∀ g ∈ raw.globals, ModuleConstants.Valid env g.init g.gtype.valtype
  | 7 => (raw.exports.map ModuleBinary.Export.name).Nodup ∧
      ∀ e ∈ raw.exports, ModuleSections.ExportDescValid env e.desc
  | 8 => ∀ idx, raw.start = some idx → ∃ hi : idx.val < env.func_types.val.length,
      env.func_types.val[idx.val].params.val = [] ∧ env.func_types.val[idx.val].results.val = []
  | 9 => ∀ e ∈ raw.elements, ModuleSections.ElementValidRaw env e
  | 10 => True
  | _ => True

/-- Every declaration section of `raw` meets its requirements whenever the preceding slots are
ready. Declarative assembly discharges this once, and it has no parser-execution or
successful-decoding premise. -/
def Requirements (raw : ModuleBinary.Module) : Prop :=
  ∀ id decls env, 1 ≤ id → id ≤ 10 → Ready raw (id - 1) decls env → SectionValid raw id env

end Itasca.ModuleEnv

end
