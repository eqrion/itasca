import Itasca.Module.ModuleConstantTyping
import Itasca.Module.ModuleExternals
import Itasca.Profile.Types

open Aeneas Aeneas.Std

namespace Itasca.ModuleEnv

def importedFuncs (imports : List module.Import) : List U32 :=
  imports.filterMap fun entry => match entry.desc with | .Func idx => some idx | _ => none

def importedGlobals (imports : List module.Import) : List types.GlobalType :=
  imports.filterMap fun entry => match entry.desc with | .Global gt => some gt | _ => none

def importedTables (imports : List module.Import) : List types.TableType :=
  imports.filterMap fun entry => match entry.desc with | .Table tt => some tt | _ => none

def importedMems (imports : List module.Import) : List types.MemType :=
  imports.filterMap fun entry => match entry.desc with | .Memory mt => some mt | _ => none

def Resolves (typeList : List types.FuncType) (idx : U32) (ft : types.FuncType) : Prop :=
  ∃ hi : idx.val < typeList.length, typeList[idx.val] = ft

/-- The environment's caches preserve all imported and declared index spaces.
The table/memory suffixes stay explicit because the runtime cache merges them. -/
structure Cache (env : module.Env) (tables : List types.TableType) (memories : List types.MemType) : Prop where
  funcs : List.Forall₂ (Resolves env.types.val)
    (importedFuncs env.imports.val ++ env.func_type_indices.val) env.func_types.val
  numFuncs : env.num_imported_funcs.val = (importedFuncs env.imports.val).length
  globals : env.global_types.val = importedGlobals env.imports.val ++ env.globals.val.map module.Global.gtype
  numGlobals : env.num_imported_globals.val = (importedGlobals env.imports.val).length
  tables : env.table_types.val = importedTables env.imports.val ++ tables
  memories : env.mem_types.val = importedMems env.imports.val ++ memories

/-- All semantic checks that are stored in, or derivable from, the returned
module environment. Byte-format evidence is kept separately. -/
structure Valid (env : module.Env) (profile : ValidationProfile := .Wasm1) : Prop where
  types : ∀ ft ∈ env.types.val, Profile.FuncTypeAdmissible profile ft
  tables : ∀ tt ∈ env.table_types.val, ModuleTranslation.LimitsValid tt.limits (2 ^ 32 - 1)
  memories : ∀ mt ∈ env.mem_types.val, ModuleTranslation.LimitsValid mt.limits (2 ^ 16)
  tableCount : env.table_types.val.length ≤ 1
  memoryCount : env.mem_types.val.length ≤ 1
  globals : ∀ g ∈ env.globals.val, ModuleConstants.Valid env g.init g.gtype.valtype
  imports : ∀ entry ∈ env.imports.val,
    ModuleBinary.Utf8 entry.module.val ∧ ModuleBinary.Utf8 entry.name.val
  exportNames : ∀ entry ∈ env.exports.val, ModuleBinary.Utf8 entry.name.val
  distinctExports : (env.exports.val.map fun entry => entry.name.val).Nodup
  exports : ∀ entry ∈ env.exports.val, ∃ xt, ModuleExternals.ExportResolves env entry xt
  start : ∀ idx, env.start = some idx → ∃ hi : idx.val < env.func_types.val.length,
    env.func_types.val[idx.val].params.val = [] ∧ env.func_types.val[idx.val].results.val = []
  elements : ∀ entry ∈ env.elements.val,
    entry.table_idx.val < env.table_types.val.length ∧
    ModuleConstants.Valid env entry.offset .I32 ∧
    ∀ idx ∈ entry.init.val, idx.val < env.func_types.val.length

/-- Allocation and counter arithmetic use a separate cursor accounting invariant. -/
structure Bounded (env : module.Env) (pos : Nat) : Prop where
  types : env.types.val.length ≤ pos
  imports : env.imports.val.length ≤ pos
  globals : env.globals.val.length ≤ pos
  exports : env.exports.val.length ≤ pos
  elements : env.elements.val.length ≤ pos
  funcIndices : env.func_type_indices.val.length ≤ pos
  funcs : env.func_types.val.length ≤ pos
  tables : env.table_types.val.length ≤ pos
  memories : env.mem_types.val.length ≤ pos
  globalTypes : env.global_types.val.length ≤ pos
  numFuncs : env.num_imported_funcs.val ≤ pos
  numGlobals : env.num_imported_globals.val ≤ pos

theorem Bounded.mono {env pos next} (h : Bounded env pos) (hle : pos ≤ next) :
    Bounded env next := by
  cases h
  constructor <;> omega

theorem Cache.global_prefix {env tables memories} (h : Cache env tables memories) :
    env.global_types.val.take env.num_imported_globals.val = importedGlobals env.imports.val := by
  rw [h.globals, h.numGlobals, List.take_left]

theorem Cache.func_property {env tables memories} (h : Cache env tables memories)
    {P : types.FuncType → Prop} (ht : ∀ ft ∈ env.types.val, P ft) :
    ∀ ft ∈ env.func_types.val, P ft := by
  intro ft hf
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hf
  have hj' : j < (importedFuncs env.imports.val ++ env.func_type_indices.val).length := by rw [h.funcs.length_eq]; exact hj
  obtain ⟨hi, he⟩ := h.funcs.get hj' hj
  simp only [List.get_eq_getElem] at he
  rw [← he]
  exact ht _ (List.getElem_mem hi)

theorem Cache.func_arity {env tables memories} (h : Cache env tables memories)
    (ht : ∀ ft ∈ env.types.val, ft.results.val.length ≤ 1) :
    ∀ ft ∈ env.func_types.val, ft.results.val.length ≤ 1 := h.func_property ht

theorem Valid.environment {profile env tables memories} (hv : Valid env profile)
    (hc : Cache env tables memories) : Profile.Environment profile env := by
  have ht : ∀ ft ∈ env.types.val, Profile.FuncType profile ft := by
    intro ft hm
    exact ((Profile.funcTypeAdmissible_iff profile ft).mp (hv.types ft hm)).1
  exact ⟨ht, hc.func_property ht⟩

theorem Valid.environmentWithinLimits {profile env tables memories} (hv : Valid env profile)
    (hc : Cache env tables memories) : Profile.EnvironmentWithinLimits profile env := by
  have ht : ∀ ft ∈ env.types.val, Profile.FuncTypeWithinLimits profile ft := by
    intro ft hm
    exact ((Profile.funcTypeAdmissible_iff profile ft).mp (hv.types ft hm)).2
  exact ⟨ht, hc.func_property ht⟩

theorem Cache.import_indices {env tables memories} (h : Cache env tables memories) :
    ∀ idx ∈ importedFuncs env.imports.val, idx.val < env.types.val.length := by
  intro idx hi
  have hm : idx ∈ importedFuncs env.imports.val ++ env.func_type_indices.val := List.mem_append_left _ hi
  obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp hm
  have hj' : j < env.func_types.val.length := by rw [← h.funcs.length_eq]; exact hj
  have hr := h.funcs.get hj hj'
  simp only [List.get_eq_getElem] at hr
  rw [he] at hr
  exact hr.1

theorem Cache.imports_resolve {env tables memories} (h : Cache env tables memories) :
    ∃ xts, List.Forall₂ (ModuleExternals.ImportResolves env) env.imports.val xts := by
  have hb := h.import_indices
  generalize env.imports.val = entries at hb ⊢
  induction entries with
  | nil => exact ⟨[], .nil⟩
  | cons entry entries ih =>
    have hb' : ∀ idx ∈ importedFuncs entries, idx.val < env.types.val.length := by
      intro idx hi
      apply hb idx
      cases entry.desc <;> simp_all [importedFuncs]
    obtain ⟨rest, hr⟩ := ih hb'
    cases hd : entry.desc with
    | Func idx =>
      have hi : idx.val < env.types.val.length := hb idx (by simp [importedFuncs, hd])
      exact ⟨.Func env.types.val[idx.val] :: rest, .cons (by simpa [ModuleExternals.ImportResolves, hd] using (show ∃ hj : idx.val < env.types.val.length, (types.ExternType.Func env.types.val[idx.val]) = .Func env.types.val[idx.val] from ⟨hi, rfl⟩)) hr⟩
    | Table tt => exact ⟨.Table tt :: rest, .cons (by simp [ModuleExternals.ImportResolves, hd]) hr⟩
    | Memory mt => exact ⟨.Memory mt :: rest, .cons (by simp [ModuleExternals.ImportResolves, hd]) hr⟩
    | Global gt => exact ⟨.Global gt :: rest, .cons (by simp [ModuleExternals.ImportResolves, hd]) hr⟩

theorem Valid.exports_resolve {profile env} (h : Valid env profile) :
    ∃ xts, List.Forall₂ (ModuleExternals.ExportResolves env) env.exports.val xts := by
  have he := h.exports
  generalize env.exports.val = entries at he ⊢
  induction entries with
  | nil => exact ⟨[], .nil⟩
  | cons entry entries ih =>
    obtain ⟨xt, ht⟩ := he entry (by simp)
    obtain ⟨xts, hrest⟩ := ih (by intro entry hm; exact he entry (by simp [hm]))
    exact ⟨xt :: xts, .cons ht hrest⟩

end Itasca.ModuleEnv

namespace Itasca

@[step]
theorem module.Env.new.spec : module.Env.new ⦃ env =>
    ModuleEnv.Cache env [] [] ∧ ModuleEnv.Valid env ∧ ModuleEnv.Bounded env 0 ⦄ := by
  unfold module.Env.new
  simp only [WP.spec_ok]
  constructor
  · constructor <;> simp [ModuleEnv.importedFuncs, ModuleEnv.importedGlobals,
      ModuleEnv.importedTables, ModuleEnv.importedMems]
  · constructor
    · constructor <;> simp
    · constructor <;> simp

end Itasca
