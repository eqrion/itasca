import Itasca.Module.ModuleEnvEffects
import Itasca.Module.ModuleNameFacts

open Aeneas Aeneas.Std

namespace Itasca.ModuleEnv

open ModuleBinary ModuleSections

/-- Before globals, all consumers of the cached index spaces are absent. -/
structure Early (env : module.Env) : Prop where
  globals : env.globals.val = []
  exports : env.exports.val = []
  start : env.start = none
  elements : env.elements.val = []

theorem Early.of_phase {env decls last} (hr : Represents env decls)
    (hp : Phase last decls) (hl : last < 6) : Early env := by
  rcases hp with ⟨_, _, _, _, _, hg, he, hs, hm⟩
  refine ⟨hr.globals.symm.trans (hg hl), ?_, hr.start.symm.trans (hs (by omega)), ?_⟩
  · have h := hr.exports.symm.trans (he (by omega))
    exact List.map_eq_nil_iff.mp h
  · have h := hr.elements.symm.trans (hm (by omega))
    exact List.map_eq_nil_iff.mp h

theorem Early.valid {env} (h : Early env)
    (ht : ∀ ft ∈ env.types.val, ft.results.val.length ≤ 1)
    (htt : ∀ tt ∈ env.table_types.val, ModuleTranslation.LimitsValid tt.limits (2 ^ 32 - 1))
    (hmt : ∀ mt ∈ env.mem_types.val, ModuleTranslation.LimitsValid mt.limits (2 ^ 16))
    (htc : env.table_types.val.length ≤ 1) (hmc : env.mem_types.val.length ≤ 1)
    (hi : ∀ entry ∈ env.imports.val, Utf8 entry.module.val ∧ Utf8 entry.name.val) : Valid env := by
  refine ⟨ht, htt, hmt, htc, hmc, ?_, hi, ?_, ?_, ?_, ?_, ?_⟩
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
      (rw [heq]; exact hv.tableCount) | (rw [heq]; exact hv.memoryCount)
  · obtain ⟨heq, hts, hcount, hlim⟩ := ha
    apply her.valid
    · (rw [heq]; exact hv.types)
    · intro tt hm
      rw [hts] at hm
      rcases List.mem_append.mp hm with hm | hm
      · exact hv.tables _ hm
      · simpa using (List.mem_singleton.mp hm ▸ hlim)
    · (rw [heq]; exact hv.memories)
    · exact hcount
    · (rw [heq]; exact hv.memoryCount)
    · exact hnames
  · obtain ⟨heq, hms, hcount, hlim⟩ := ha
    apply her.valid
    · (rw [heq]; exact hv.types)
    · (rw [heq]; exact hv.tables)
    · intro mt hm
      rw [hms] at hm
      rcases List.mem_append.mp hm with hm | hm
      · exact hv.memories _ hm
      · simpa using (List.mem_singleton.mp hm ▸ hlim)
    · (rw [heq]; exact hv.tableCount)
    · exact hcount
    · exact hnames
  · obtain ⟨heq, hgs, hnum⟩ := ha
    apply her.valid <;> first | exact hnames | (rw [heq]; exact hv.types) |
      (rw [heq]; exact hv.tables) | (rw [heq]; exact hv.memories) |
      (rw [heq]; exact hv.tableCount) | (rw [heq]; exact hv.memoryCount)

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

/-- Later metadata sections leave every index-space meaning unchanged. -/
structure SameCore (env result : module.Env) : Prop where
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
  | globalGet idx gt hi hgt himp hc =>
    exact .globalGet idx gt (by simpa [h.globals] using hi)
      (by simpa [h.globals] using hgt) (by simpa [h.numGlobals] using himp) hc

theorem SameCore.export {env result e xt} (h : SameCore env result)
    (hv : ModuleExternals.ExportResolves env e xt) : ModuleExternals.ExportResolves result e xt := by
  cases hd : e.desc <;> simpa only [ModuleExternals.ExportResolves, hd,
    h.funcs, h.tables, h.memories, h.globals] using hv

theorem SameCore.element {env result entry} (h : SameCore env result)
    (hv : ModuleSections.ElementValid env entry) : ModuleSections.ElementValid result entry := by
  exact ⟨by simpa [h.tables] using hv.1, h.constant hv.2.1,
    by simpa [h.funcs] using hv.2.2⟩

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
    (hv : Valid env) (hn : Utf8 entry.name.val) : Valid result := by
  obtain ⟨he, hexports, hnew, hresolve⟩ := h
  have hc : SameCore env result := by constructor <;> rw [he]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [he]; exact hv.types
  · rw [he]; exact hv.tables
  · rw [he]; exact hv.memories
  · rw [he]; exact hv.tableCount
  · rw [he]; exact hv.memoryCount
  · intro g hg
    have hg' : g ∈ env.globals.val := by simpa only [congrArg module.Env.globals he] using hg
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
    have hs' : env.start = some idx := by simpa only [congrArg module.Env.start he] using hs
    exact hc.start (hv.start idx hs')
  · intro e hm
    have hm' : e ∈ env.elements.val := by simpa only [congrArg module.Env.elements he] using hm
    exact hc.element (hv.elements _ hm')

theorem ExportsAdded.valid {env entries result} (h : ExportsAdded env entries result)
    (hv : Valid env) (hn : ∀ e ∈ entries, Utf8 e.name.val) : Valid result := by
  induction h with
  | nil => exact hv
  | snoc hp ha ih =>
    exact ha.valid (ih (by intro e hm; exact hn e (by simp [hm]))) (hn _ (by simp))

end Itasca.ModuleSections

namespace Itasca.ModuleEnv

open ModuleBinary ModuleSections

/-- The semantic checks carried by the ordered section history establish all
stored environment obligations, including names, uniqueness, and initializers. -/
theorem Effect.valid {data pos env before id next result after last}
    (h : Effect data pos env before id next result after)
    (hr : Represents env before) (hv : Valid env)
    (hp : Phase last before) (ho : last < id.val) : Valid result := by
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
    · rw [he]; exact hv.tableCount
    · rw [he]; exact hv.memoryCount
    · rw [he]; exact hv.imports
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
      (rw [he]; exact hv.tableCount) | (rw [he]; exact hv.memoryCount) |
      (rw [he]; exact hv.imports)
  | tables ha hb ht hcount =>
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
    · simpa [max_eq_right hv.tableCount] using hcount
    · rw [he]; exact hv.memoryCount
    · rw [he]; exact hv.imports
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
    · rw [he]; exact hv.tableCount
    · simpa [max_eq_right hv.memoryCount] using hcount
    · rw [he]; exact hv.imports
  | globals ha hb hg =>
    have hearly := Early.of_phase hr hp (by change last < 6 at ho; exact ho)
    obtain ⟨he, hgs, htypes⟩ := ha
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [he]; exact hv.types
    · rw [he]; exact hv.tables
    · rw [he]; exact hv.memories
    · rw [he]; exact hv.tableCount
    · rw [he]; exact hv.memoryCount
    · intro g hm
      exact hg _ (by simpa [hgs, hearly.globals] using hm)
    · rw [he]; exact hv.imports
    all_goals rw [he]; simp [hearly.exports, hearly.start, hearly.elements]
  | exports ha hb =>
    apply ha.valid hv
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
    · rw [he]; exact hv.tableCount
    · rw [he]; exact hv.memoryCount
    · intro g hg
      exact hc.constant (hv.globals g (by simpa only [congrArg module.Env.globals he] using hg))
    · rw [he]; exact hv.imports
    · rw [he]; exact hv.exportNames
    · rw [he]; exact hv.distinctExports
    · intro e hm
      obtain ⟨xt, hx⟩ := hv.exports e (by simpa only [congrArg module.Env.exports he] using hm)
      exact ⟨xt, hc.export hx⟩
    · intro idx hs
      rw [he] at hs
      cases Option.some.inj hs
      exact hc.start hstart
    · intro e hm
      exact hc.element (hv.elements e (by simpa only [congrArg module.Env.elements he] using hm))
  | elements ha hb ht =>
    obtain ⟨he, hes⟩ := ha
    have hc : SameCore env result := by constructor <;> rw [he]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [he]; exact hv.types
    · rw [he]; exact hv.tables
    · rw [he]; exact hv.memories
    · rw [he]; exact hv.tableCount
    · rw [he]; exact hv.memoryCount
    · intro g hg
      exact hc.constant (hv.globals g (by simpa only [congrArg module.Env.globals he] using hg))
    · rw [he]; exact hv.imports
    · rw [he]; exact hv.exportNames
    · rw [he]; exact hv.distinctExports
    · intro e hm
      obtain ⟨xt, hx⟩ := hv.exports e (by simpa only [congrArg module.Env.exports he] using hm)
      exact ⟨xt, hc.export hx⟩
    · intro idx hs
      exact hc.start (hv.start idx (by simpa only [congrArg module.Env.start he] using hs))
    · intro e hm
      rw [hes] at hm
      rcases List.mem_append.mp hm with hm | hm
      · exact hc.element (hv.elements e hm)
      · exact hc.element (ht e hm)

end Itasca.ModuleEnv
