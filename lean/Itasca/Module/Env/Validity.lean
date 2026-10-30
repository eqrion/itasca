import Itasca.Module.Env.Effects
import Itasca.Module.Env.NameFacts

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

theorem Early.valid {profile} {env} (h : Early env)
    (ht : ∀ ft ∈ env.types.val, Profile.FuncTypeAdmissible profile ft)
    (htt : ∀ tt ∈ env.table_types.val, ModuleTranslation.LimitsValid tt.limits (2 ^ 32 - 1))
    (hmt : ∀ mt ∈ env.mem_types.val, ModuleTranslation.LimitsValid mt.limits (2 ^ 16))
    (htc : profile = .Wasm1 → env.table_types.val.length ≤ 1) (hmc : env.mem_types.val.length ≤ 1)
    (hi : ∀ entry ∈ env.imports.val, Utf8 entry.module.val ∧ Utf8 entry.name.val)
    (href : ModuleReferences.Coherent env) : Valid env profile := by
  refine ⟨ht, htt, hmt, htc, hmc, ?_, hi, ?_, ?_, ?_, ?_, ?_, href⟩
  all_goals simp [h.globals, h.exports, h.start, h.elements]

end Itasca.ModuleEnv

namespace Itasca.ModuleSections

open ModuleEnv ModuleBinary

theorem ImportAdded.early {profile} {env result entry} (h : ImportAdded env result entry profile)
    (he : Early env) : Early result := by
  obtain ⟨_, h⟩ := h
  cases hd : entry.desc <;> simp only [hd] at h
  · obtain ⟨_, _, h, _⟩ := h
    rw [h]; exact ⟨he.globals, he.exports, he.start, he.elements⟩
  all_goals rw [h.1]; exact ⟨he.globals, he.exports, he.start, he.elements⟩

theorem ImportAdded.valid {profile} {env result entry} (h : ImportAdded env result entry profile)
    (hv : Valid env profile) (he : Early env)
    (hn : Utf8 entry.module.val ∧ Utf8 entry.name.val) : Valid result profile := by
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
      (rw [heq]; exact hv.tableCount) | (rw [heq]; exact hv.memoryCount) |
      (rw [heq]; exact hv.references)
  · obtain ⟨heq, hts, hcount, hlim, _⟩ := ha
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
    · (rw [heq]; exact hv.tableCount)
    · exact hcount
    · exact hnames
    · rw [heq]; exact hv.references
  · obtain ⟨heq, hgs, hnum, _⟩ := ha
    apply her.valid <;> first | exact hnames | (rw [heq]; exact hv.types) |
      (rw [heq]; exact hv.tables) | (rw [heq]; exact hv.memories) |
      (rw [heq]; exact hv.tableCount) | (rw [heq]; exact hv.memoryCount) |
      (rw [heq]; exact hv.references)

theorem ImportsAdded.early {profile} {env entries result} (h : ImportsAdded env entries result profile)
    (he : Early env) : Early result := by
  induction h with
  | nil => exact he
  | snoc hp ha ih => exact ha.early ih

theorem ImportsAdded.valid {profile} {env entries result} (h : ImportsAdded env entries result profile)
    (hv : Valid env profile) (he : Early env)
    (hn : ∀ e ∈ entries, Utf8 e.module.val ∧ Utf8 e.name.val) : Valid result profile := by
  induction h with
  | nil => exact hv
  | snoc hp ha ih =>
    exact ha.valid (ih hv (by intro e hm; exact hn e (by simp [hm])))
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

theorem ExportAdded.valid {profile} {env result entry} (h : ExportAdded env result entry)
    (hv : Valid env profile) (helements : env.elements.val = []) (hn : Utf8 entry.name.val) : Valid result profile := by
  obtain ⟨he, hexports, hnew, hresolve, href⟩ := h
  have hc : SameCore env result := by constructor <;> rw [he]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [he]; exact hv.types
  · rw [he]; exact hv.tables
  · rw [he]; exact hv.memories
  · rw [he]; exact hv.tableCount
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

theorem ExportsAdded.valid {profile} {env entries result} (h : ExportsAdded env entries result)
    (hv : Valid env profile) (helements : env.elements.val = []) (hn : ∀ e ∈ entries, Utf8 e.name.val) : Valid result profile := by
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
theorem Effect.valid {profile} {data pos env before id next result after last}
    (h : Effect (profile := profile) data pos env before id next result after)
    (hr : Represents env before) (hv : Valid env profile)
    (hp : Phase last before) (ho : last < (sectionRank id).val) : Valid result profile := by
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
      · exact (ht _ hm).1
    · rw [he]; exact hv.tables
    · rw [he]; exact hv.memories
    · rw [he]; exact hv.tableCount
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
      (rw [he]; exact hv.tableCount) | (rw [he]; exact hv.memoryCount) |
      (rw [he]; exact hv.imports) |
      (rw [he]; exact hv.references)
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
      · exact (ht _ hm).1
    · rw [he]; exact hv.memories
    · intro hprofile
      simpa [max_eq_right (hv.tableCount hprofile)] using hcount hprofile
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
    · rw [he]; exact hv.tableCount
    · simpa [max_eq_right hv.memoryCount] using hcount
    · rw [he]; exact hv.imports
    · rw [he]; exact hv.references
  | globals ha hb hg =>
    have hearly := Early.of_phase hr hp (by change last < 6 at ho; exact ho)
    obtain ⟨he, hgs, htypes, href⟩ := ha
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [he]; exact hv.types
    · rw [he]; exact hv.tables
    · rw [he]; exact hv.memories
    · rw [he]; exact hv.tableCount
    · rw [he]; exact hv.memoryCount
    · intro g hm
      exact (hg _ (by simpa [hgs, hearly.globals] using hm)).1
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
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [he]; exact hv.types
    · rw [he]; exact hv.tables
    · rw [he]; exact hv.memories
    · rw [he]; exact hv.tableCount
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
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [he]; exact hv.types
    · rw [he]; exact hv.tables
    · rw [he]; exact hv.memories
    · rw [he]; exact hv.tableCount
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
  | dataCount hprofile he hbytes =>
    have hc : SameCore env result := by constructor <;> rw [he]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [he]; exact hv.types
    · rw [he]; exact hv.tables
    · rw [he]; exact hv.memories
    · rw [he]; exact hv.tableCount
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
