import Itasca.Module.Env.Representation

/-! Import validity and transport of typing evidence across descriptor flag updates. -/

section

/-!
# Validity of decoded environments

Imports extend their corresponding index spaces. Later flag updates preserve the descriptor
projections used by constant expressions, exports, start functions, and element segments.
-/

open Aeneas Aeneas.Std

namespace Itasca.Module.Environment

open Binary Module.Sections

/-- Before the global section, every global descriptor denotes an import. -/
structure Early (env : metadata.ModuleMetadata metadata.CodeMetadata) : Prop where
  globals : ∀ g ∈ env.code.globals.val, g.init = none
  exports : env.exports.val = []
  start : env.code.start = none
  elements : env.elements.val = []

theorem Early.of_phase {env decls last} (hr : Represents env decls)
    (hp : Phase last decls) (hl : last < 6) : Early env := by
  rcases hp with ⟨_, _, _, _, _, hg, he, hs, hm, _⟩
  refine ⟨?_, ?_, hr.start.symm.trans (hs (by omega)), ?_⟩
  · intro g hmem
    have hin := List.mem_map_of_mem (f := fun g : metadata.Global => (g.gtype, g.init)) hmem
    rw [hr.cache.globalEntries, hg hl] at hin
    simp at hin
    exact hin.2.symm
  · exact List.map_eq_nil_iff.mp (hr.exports.symm.trans (he (by omega)))
  · exact List.map_eq_nil_iff.mp (hr.elements.symm.trans (hm (by omega)))

theorem Early.collected {env} (h : Early env) : Module.References.collected env = [] := by
  simp [Module.References.collected, h.exports, h.elements, List.flatMap_eq_nil_iff,
    Module.References.global]
  intro g hg init
  simp [h.globals g hg]

theorem Early.coherent {env} (h : Early env) : Module.References.Coherent env ↔
    ∀ d ∈ env.code.funcs.val, d.can_ref_func = false := by
  simp only [Module.References.Coherent, h.collected, List.not_mem_nil,
    false_and, exists_false, iff_false, Translation.Environment.mem_declaredReferences]
  constructor
  · intro empty d hd
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hd
    cases hf : d.can_ref_func with
    | false => rfl
    | true => exact False.elim (empty i ⟨d, hi, hf⟩)
  · rintro flags i ⟨d, hd, hf⟩
    simp [flags d (List.mem_iff_getElem?.mpr ⟨i,hd⟩)] at hf

theorem Early.valid {env} (h : Early env)
    (ht : ∀ ft ∈ env.code.types.val, CodeEntry.FuncTypeWithinLimits ft)
    (hf : DescriptorIndices env.code)
    (htt : ∀ d ∈ env.code.tables.val, Module.Translation.LimitsValid d.ty.limits (2 ^ 32 - 1))
    (hmt : ∀ d ∈ env.code.memories.val, Module.Translation.LimitsValid d.ty.limits (2 ^ 16))
    (hmc : env.code.memories.val.length ≤ 1)
    (hi : ∀ entry ∈ env.imports.val, Utf8 entry.module.val ∧ Utf8 entry.name.val)
    (href : Module.References.Coherent env) : Valid env := by
  refine ⟨ht, hf, htt, hmt, hmc, ?_, hi, ?_, ?_, ?_, ?_, ?_, href⟩
  · intro g hg init; simp [h.globals g hg]
  all_goals simp [h.exports, h.start, h.elements]

end Itasca.Module.Environment

namespace Itasca.Module.Sections

open Module.Environment Binary

theorem ImportAdded.early {env result entry} (h : ImportAdded env result entry)
    (he : Early env) : Early result := by
  obtain ⟨_, change⟩ := h
  cases hd : entry.desc <;> simp only [hd] at change
  case Func => rw [change.2.1]; exact ⟨he.globals, he.exports, he.start, he.elements⟩
  case Global =>
    rw [change.1]
    refine ⟨?_, he.exports, he.start, he.elements⟩
    intro g hg
    rcases List.mem_append.mp (change.2.1 ▸ hg) with hg | hg
    · exact he.globals _ hg
    · obtain rfl := List.mem_singleton.mp hg; rfl
  all_goals rw [change.1]; exact ⟨he.globals, he.exports, he.start, he.elements⟩

theorem ImportAdded.valid {env result entry} (h : ImportAdded env result entry)
    (hv : Valid env) (he : Early env)
    (hn : Utf8 entry.moduleName ∧ Utf8 entry.name) : Valid result := by
  have her := h.early he
  have hindices := DescriptorIndices.imports hv.funcs (ImportsAdded.snoc .nil h)
  have hflags := he.coherent.mp hv.references
  obtain ⟨⟨actual, imports, record⟩, update⟩ := h
  have hnames : ∀ e ∈ result.imports.val, Utf8 e.module.val ∧ Utf8 e.name.val := by
    intro e hm
    rw [imports] at hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hv.imports _ hm
    · obtain rfl := List.mem_singleton.mp hm
      have hm : e.module.val = entry.moduleName := congrArg Prod.fst record
      have he : e.name.val = entry.name := congrArg (fun p => p.2.1) record
      simpa [hm, he] using hn
  cases hd : entry.desc <;> simp only [hd] at update
  case Func =>
    obtain ⟨_, fields, funcs, count⟩ := update
    refine her.valid ?_ hindices ?_ ?_ ?_ hnames ?_
    · rw [fields]; exact hv.types
    · rw [fields]; exact hv.tables
    · rw [fields]; exact hv.memories
    · rw [fields]; exact hv.memoryCount
    · apply her.coherent.mpr
      intro d hd
      rw [funcs] at hd
      rcases List.mem_append.mp hd with hd | hd
      · exact hflags _ hd
      · obtain rfl := List.mem_singleton.mp hd; rfl
  case Table =>
    obtain ⟨fields, tables, limits⟩ := update
    refine her.valid ?_ hindices ?_ ?_ ?_ hnames ?_
    · rw [fields]; exact hv.types
    · intro d hd
      rw [tables] at hd
      rcases List.mem_append.mp hd with hd | hd
      · exact hv.tables _ hd
      · obtain rfl := List.mem_singleton.mp hd; exact limits
    · rw [fields]; exact hv.memories
    · rw [fields]; exact hv.memoryCount
    · apply her.coherent.mpr; rw [fields]; exact hflags
  case Memory =>
    obtain ⟨fields, memories, count, limits⟩ := update
    refine her.valid ?_ hindices ?_ ?_ count hnames ?_
    · rw [fields]; exact hv.types
    · rw [fields]; exact hv.tables
    · intro d hd
      rw [memories] at hd
      rcases List.mem_append.mp hd with hd | hd
      · exact hv.memories _ hd
      · obtain rfl := List.mem_singleton.mp hd; exact limits
    · apply her.coherent.mpr; rw [fields]; exact hflags
  case Global =>
    refine her.valid ?_ hindices ?_ ?_ ?_ hnames ?_
    · rw [update.1]; exact hv.types
    · rw [update.1]; exact hv.tables
    · rw [update.1]; exact hv.memories
    · rw [update.1]; exact hv.memoryCount
    · apply her.coherent.mpr; rw [update.1]; exact hflags

theorem ImportsAdded.early {env entries result} (h : ImportsAdded env entries result)
    (he : Early env) : Early result := by
  induction h with
  | nil => exact he
  | snoc hp ha ih => exact ha.early ih

theorem ImportsAdded.valid {env entries result} (h : ImportsAdded env entries result)
    (hv : Valid env) (he : Early env)
    (hn : ∀ e ∈ entries, Utf8 e.moduleName ∧ Utf8 e.name) : Valid result := by
  induction h with
  | nil => exact hv
  | snoc hp ha ih =>
    exact ha.valid (ih (by intro e hm; exact hn e (by simp [hm])))
      (hp.early he) (hn _ (by simp))

end Itasca.Module.Sections

namespace Itasca.Module.Environment

/-- Later sections leave the function, table, memory and global index spaces unchanged. -/
structure SameCore (env result : metadata.CodeMetadata) : Prop where
  types : result.types = env.types
  funcs : result.funcs.val.map metadata.FuncDesc.type_index = env.funcs.val.map metadata.FuncDesc.type_index
  tables : result.tables.val.map metadata.TableDesc.ty = env.tables.val.map metadata.TableDesc.ty
  memories : result.memories.val.map metadata.MemoryDesc.ty = env.memories.val.map metadata.MemoryDesc.ty
  globals : result.globals.val.map metadata.Global.gtype = env.globals.val.map metadata.Global.gtype
  numGlobals : result.num_imported_globals = env.num_imported_globals

private theorem projected_length {α β : Type} {f : α → β} {xs ys : List α}
    (h : xs.map f = ys.map f) : xs.length = ys.length := by
  simpa using congrArg List.length h

private theorem projected_at {α β : Type} {f : α → β} {xs ys : List α}
    (h : xs.map f = ys.map f) {i : Nat} (hx : i < xs.length) (hy : i < ys.length) :
    f xs[i] = f ys[i] := by
  have eq := congrArg (fun list : List β => list[i]?) h
  simpa [List.getElem?_map, List.getElem?_eq_getElem hx, List.getElem?_eq_getElem hy] using eq

theorem SameCore.constant {env result e t} (h : SameCore env result)
    (hv : Module.Constants.Valid env e t) : Module.Constants.Valid result e t := by
  cases hv with
  | i32 value => exact .i32 value
  | i64 value => exact .i64 value
  | f32 value => exact .f32 value
  | f64 value => exact .f64 value
  | v128 low high => exact .v128 low high
  | refNull ty => exact .refNull ty
  | refFunc idx hi => exact .refFunc idx (by simpa [projected_length h.funcs] using hi)
  | globalGet idx gt hi hgt himp hc =>
    have bound : idx.val < result.globals.val.length := by simpa [projected_length h.globals] using hi
    exact .globalGet idx gt bound ((projected_at h.globals bound hi).trans hgt)
      (by simpa [h.numGlobals] using himp) hc

theorem SameCore.externalTypeAt {env result} (h : SameCore env result) (desc : metadata.ExportDesc) :
    result.externalTypeAt desc = env.externalTypeAt desc := by
  cases desc with
  | Func idx =>
    have eq := congrArg (fun xs : List U32 => xs[idx.val]?) h.funcs
    simp only [List.getElem?_map] at eq
    have proj := congrArg (fun opt : Option U32 => opt.bind fun i =>
      env.types.val[i.val]?.map wasm_types.ExternType.Func) eq
    simp only [metadata.CodeMetadata.externalTypeAt, h.types]
    simpa [Option.bind_map, Function.comp_def, Option.bind_assoc, Option.map_eq_bind] using proj
  | Table idx =>
    have eq := congrArg (fun xs : List wasm_types.TableType => xs[idx.val]?) h.tables
    simpa [metadata.CodeMetadata.externalTypeAt, List.getElem?_map, Option.map_map, Function.comp_def]
      using congrArg (Option.map wasm_types.ExternType.Table) eq
  | Memory idx =>
    have eq := congrArg (fun xs : List wasm_types.MemType => xs[idx.val]?) h.memories
    simpa [metadata.CodeMetadata.externalTypeAt, List.getElem?_map, Option.map_map, Function.comp_def]
      using congrArg (Option.map wasm_types.ExternType.Memory) eq
  | Global idx =>
    have eq := congrArg (fun xs : List wasm_types.GlobalType => xs[idx.val]?) h.globals
    simpa [metadata.CodeMetadata.externalTypeAt, List.getElem?_map, Option.map_map, Function.comp_def]
      using congrArg (Option.map wasm_types.ExternType.Global) eq

theorem SameCore.export {env result e xt} (h : SameCore env result)
    (hv : Module.Externals.ExportResolves env e xt) : Module.Externals.ExportResolves result e xt := by
  simpa [Module.Externals.ExportResolves, h.externalTypeAt] using hv

theorem SameCore.element {env result entry} (h : SameCore env result)
    (hv : Module.Sections.ElementValid env entry) : Module.Sections.ElementValid result entry := by
  refine ⟨?_, fun e hm => h.constant (hv.2 e hm)⟩
  cases hm : entry.mode with
  | Passive => trivial
  | Declarative => trivial
  | Active idx offset =>
    have hm' := hv.1
    rw [hm] at hm'
    obtain ⟨hi, ht, ho⟩ := hm'
    have bound : idx.val < result.tables.val.length := by simpa [projected_length h.tables] using hi
    exact ⟨bound, (congrArg wasm_types.TableType.elem (projected_at h.tables bound hi)).trans ht,
      h.constant ho⟩

theorem SameCore.start {env result} {idx : U32} (h : SameCore env result)
    (hv : ∃ ft, env.externalTypeAt (.Func idx) = some (.Func ft) ∧
      ft.params.val = [] ∧ ft.results.val = []) :
    ∃ ft, result.externalTypeAt (.Func idx) = some (.Func ft) ∧
      ft.params.val = [] ∧ ft.results.val = [] := by
  simpa only [h.externalTypeAt] using hv

end Itasca.Module.Environment

end
