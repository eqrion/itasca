import Itasca.Module.ModuleEnvEffects

open Aeneas Aeneas.Std

namespace Itasca.ModuleSections

/-- Semantic requirements for one import at its current index-space prefix. -/
def ImportValid (env : module.Env) : module.ImportDesc → Prop
  | .Func idx => idx.val < env.types.val.length
  | .Table tt => ModuleBinary.LimitsValid tt.limits limits.MAX_TABLE_ELEMS ∧
      env.table_types.val.length + 1 ≤ 1
  | .Memory mt => ModuleBinary.LimitsValid mt.limits limits.MAX_MEMORY_PAGES ∧
      env.mem_types.val.length + 1 ≤ 1
  | .Global _ => True

def rawTables (entries : List ModuleBinary.Import) : List types.TableType :=
  entries.filterMap (fun e => match e.desc with | .Table tt => some tt | _ => none)

def rawMemories (entries : List ModuleBinary.Import) : List types.MemType :=
  entries.filterMap (fun e => match e.desc with | .Memory mt => some mt | _ => none)

/-- Import validity separates descriptor checks from the combined index-space
cardinality restrictions, so a prefix of imports can be processed in order. -/
structure ImportsValid (env : module.Env) (entries : List ModuleBinary.Import) : Prop where
  descriptors : ∀ e ∈ entries, match e.desc with
    | .Func idx => idx.val < env.types.val.length
    | .Table tt => ModuleBinary.LimitsValid tt.limits limits.MAX_TABLE_ELEMS
    | .Memory mt => ModuleBinary.LimitsValid mt.limits limits.MAX_MEMORY_PAGES
    | .Global _ => True
  tables : env.table_types.val.length + (rawTables entries).length ≤ 1
  memories : env.mem_types.val.length + (rawMemories entries).length ≤ 1

def ElementValidRaw (env : module.Env) (entry : ModuleBinary.Element) : Prop :=
  entry.tableIdx.val < env.table_types.val.length ∧
  ModuleConstants.Valid env entry.offset .I32 ∧
  ∀ idx ∈ entry.init, idx.val < env.func_types.val.length


theorem ImportsValid.head {env entry entries} (h : ImportsValid env (entry :: entries)) :
    ImportValid env entry.desc := by
  have hd := h.descriptors entry (by simp)
  have ht := h.tables
  have hm := h.memories
  cases he : entry.desc <;> simp only [he, ImportValid] at hd ⊢
  · exact hd
  · refine ⟨hd, ?_⟩
    simp [rawTables, he] at ht
    omega
  · refine ⟨hd, ?_⟩
    simp [rawMemories, he] at hm
    omega

theorem ImportsValid.tail {env result actual entries}
    (h : ImportsValid env (ModuleEnv.rawImport actual :: entries))
    (ha : ImportAdded env result actual) : ImportsValid result entries := by
  obtain ⟨_, ha⟩ := ha
  have hd : ∀ e ∈ entries, match e.desc with
      | .Func idx => idx.val < env.types.val.length
      | .Table tt => ModuleBinary.LimitsValid tt.limits limits.MAX_TABLE_ELEMS
      | .Memory mt => ModuleBinary.LimitsValid mt.limits limits.MAX_MEMORY_PAGES
      | .Global _ => True := fun e he => h.descriptors e (by simp [he])
  have ht := h.tables
  have hm := h.memories
  cases he : actual.desc <;> simp only [he] at ha
  · obtain ⟨_, _, hr, _, _⟩ := ha
    rw [hr]
    exact ⟨hd, by simpa [rawTables, ModuleEnv.rawImport, he] using ht,
      by simpa [rawMemories, ModuleEnv.rawImport, he] using hm⟩
  · obtain ⟨hr, hs, _, _⟩ := ha
    rw [hr]
    refine ⟨hd, ?_, by simpa [rawMemories, ModuleEnv.rawImport, he] using hm⟩
    simp only
    rw [hs]
    have hl : (rawTables (ModuleEnv.rawImport actual :: entries)).length = (rawTables entries).length + 1 := by
      simp [rawTables, ModuleEnv.rawImport, he]
    rw [hl] at ht
    simp only [List.length_append, List.length_singleton]
    omega
  · obtain ⟨hr, hs, _, _⟩ := ha
    rw [hr]
    refine ⟨hd, by simpa [rawTables, ModuleEnv.rawImport, he] using ht, ?_⟩
    simp only
    rw [hs]
    have hl : (rawMemories (ModuleEnv.rawImport actual :: entries)).length = (rawMemories entries).length + 1 := by
      simp [rawMemories, ModuleEnv.rawImport, he]
    rw [hl] at hm
    simp only [List.length_append, List.length_singleton]
    omega
  · obtain ⟨hr, _, _⟩ := ha
    rw [hr]
    exact ⟨hd, by simpa [rawTables, ModuleEnv.rawImport, he] using ht,
      by simpa [rawMemories, ModuleEnv.rawImport, he] using hm⟩

end Itasca.ModuleSections

namespace Itasca.ModuleEnv

/-- The greedy environment scan stops only at EOF or a fully available section
header belonging to the code/data suffix. -/
def StopAt (data : Slice U8) (pos : Usize) : Prop :=
  pos = Slice.len data ∨ ∃ id first last,
    ModuleBinary.SectionHeader data pos id first last ∧ 10 ≤ id.val

/-- All slots through `last` are complete, including omitted empty sections.
The runtime caches retain their precise relationship to this declaration prefix. -/
structure Ready (raw : ModuleBinary.Module) (last : Nat) (decls : Declarations)
    (env : module.Env) : Prop where
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

/-- Pure semantic requirements of the next declaration section. Binary framing,
UTF-8 names, and cursor/capacity bounds are supplied separately by the grammar. -/
def SectionValid (raw : ModuleBinary.Module) (id : Nat) (env : module.Env)
    (profile : ValidationProfile := .Wasm1) : Prop :=
  match id with
  | 1 => ∀ ft ∈ raw.types, Profile.FuncTypeAdmissible profile ft
  | 2 => ModuleSections.ImportsValid env raw.imports
  | 3 => ∀ idx ∈ raw.functions, idx.val < env.types.val.length
  | 4 => (∀ tt ∈ raw.tables, ModuleBinary.LimitsValid tt.limits limits.MAX_TABLE_ELEMS) ∧
      env.table_types.val.length + raw.tables.length ≤ 1
  | 5 => (∀ mt ∈ raw.memories, ModuleBinary.LimitsValid mt.limits limits.MAX_MEMORY_PAGES) ∧
      env.mem_types.val.length + raw.memories.length ≤ 1
  | 6 => ∀ g ∈ raw.globals, ModuleConstants.Valid env g.init g.gtype.valtype
  | 7 => (raw.exports.map ModuleBinary.Export.name).Nodup ∧
      ∀ e ∈ raw.exports, ModuleSections.ExportDescValid env e.desc
  | 8 => ∀ idx, raw.start = some idx → ∃ hi : idx.val < env.func_types.val.length,
      env.func_types.val[idx.val].params.val = [] ∧ env.func_types.val[idx.val].results.val = []
  | 9 => ∀ e ∈ raw.elements, ModuleSections.ElementValidRaw env e
  | _ => True

/-- Declarative assembly discharges this aggregate once. It contains no parser
execution or successful-decoding premise. -/
def Requirements (raw : ModuleBinary.Module) (profile : ValidationProfile := .Wasm1) : Prop :=
  ∀ id decls env, 1 ≤ id → id ≤ 9 → Ready raw (id - 1) decls env → SectionValid raw id env profile

end Itasca.ModuleEnv
