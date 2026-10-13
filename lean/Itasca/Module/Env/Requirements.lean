import Itasca.Module.Sections.Imports
import Itasca.Module.Sections.Export
import Itasca.Module.Sections.DataCount

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
def ImportValid (env : module.Env) (desc : module.ImportDesc)
    (profile : ValidationProfile := .Wasm1) : Prop :=
  match desc with
  | .Func idx => idx.val < env.types.val.length
  | .Table tt => ModuleBinary.LimitsValid tt.limits limits.MAX_TABLE_ELEMS ∧
      (profile = .Wasm1 → env.table_types.val.length + 1 ≤ 1)
  | .Memory mt => ModuleBinary.LimitsValid mt.limits limits.MAX_MEMORY_PAGES ∧
      env.mem_types.val.length + 1 ≤ 1
  | .Global _ => True

/-- The table types among the raw imports. -/
def rawTables (entries : List ModuleBinary.Import) : List types.TableType :=
  entries.filterMap (fun e => match e.desc with | .Table tt => some tt | _ => none)

/-- The memory types among the raw imports. -/
def rawMemories (entries : List ModuleBinary.Import) : List types.MemType :=
  entries.filterMap (fun e => match e.desc with | .Memory mt => some mt | _ => none)

/-- The imports are valid against `env`. Descriptor checks are separate from the cardinality limits
on the merged table and memory spaces, so imports can be processed in order. -/
structure ImportsValid (env : module.Env) (entries : List ModuleBinary.Import)
    (profile : ValidationProfile := .Wasm1) : Prop where
  descriptors : ∀ e ∈ entries, match e.desc with
    | .Func idx => idx.val < env.types.val.length
    | .Table tt => ModuleBinary.LimitsValid tt.limits limits.MAX_TABLE_ELEMS
    | .Memory mt => ModuleBinary.LimitsValid mt.limits limits.MAX_MEMORY_PAGES
    | .Global _ => True
  tables : profile = .Wasm1 → env.table_types.val.length + (rawTables entries).length ≤ 1
  memories : env.mem_types.val.length + (rawMemories entries).length ≤ 1

/-- A raw element segment is valid against `env`. An active segment names a table of its element
type with a valid `i32` offset, and every initializer is a valid constant of the element type. -/
def ElementValidRaw (env : module.Env) (entry : ModuleBinary.Element) : Prop :=
  (match entry.mode with
    | .Active idx offset => ∃ hi : idx.val < env.table_types.val.length,
        env.table_types.val[idx.val].elem = entry.elem ∧ ModuleConstants.Valid env offset .I32
    | .Passive | .Declarative => True) ∧
  ∀ init ∈ entry.init, ModuleConstants.Valid env init (ModuleConstants.referenceValueType entry.elem)

/-- The first import of a valid list is valid at the current index-space prefix. -/
theorem ImportsValid.head {profile} {env entry entries} (h : ImportsValid env (entry :: entries) profile) :
    ImportValid env entry.desc profile := by
  have hd := h.descriptors entry (by simp)
  have ht := h.tables
  have hm := h.memories
  cases he : entry.desc <;> simp only [he, ImportValid] at hd ⊢
  · exact hd
  · refine ⟨hd, ?_⟩
    intro hprofile
    have ht := ht hprofile
    simp [rawTables, he] at ht
    omega
  · refine ⟨hd, ?_⟩
    simp [rawMemories, he] at hm
    omega

/-- After the first import is added, the remaining imports are valid against the updated
environment. -/
theorem ImportsValid.tail {profile} {env result actual entries}
    (h : ImportsValid env (ModuleEnv.rawImport actual :: entries) profile)
    (ha : ImportAdded env result actual profile) : ImportsValid result entries profile := by
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
    intro hprofile
    have ht := ht hprofile
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

/-- The greedy environment scan stops only at end of input or at a complete section header for the
code section (`10`) or data section (`11`). -/
def StopAt (data : Slice U8) (pos : Usize) : Prop :=
  pos = Slice.len data ∨ ∃ id first last,
    ModuleBinary.SectionHeader data pos id first last ∧ (id = 10#u8 ∨ id = 11#u8)

/-- All slots through rank `last` are complete in `decls`, including omitted empty sections, and
match the raw module `raw`. The environment `env` represents `decls`. -/
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
  dataCount : 10 ≤ last → decls.dataCount = raw.dataCount

/-- The semantic requirements of declaration section rank `id` of `raw` against `env`. Binary
framing, UTF-8 names, and cursor and capacity bounds come separately from the grammar. -/
def SectionValid (raw : ModuleBinary.Module) (id : Nat) (env : module.Env)
    (profile : ValidationProfile := .Wasm1) : Prop :=
  match id with
  | 1 => ∀ ft ∈ raw.types, Profile.FuncTypeAdmissible profile ft
  | 2 => ModuleSections.ImportsValid env raw.imports profile
  | 3 => ∀ idx ∈ raw.functions, idx.val < env.types.val.length
  | 4 => (∀ tt ∈ raw.tables, ModuleBinary.LimitsValid tt.limits limits.MAX_TABLE_ELEMS) ∧
      (profile = .Wasm1 → env.table_types.val.length + raw.tables.length ≤ 1)
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
def Requirements (raw : ModuleBinary.Module) (profile : ValidationProfile := .Wasm1) : Prop :=
  ∀ id decls env, 1 ≤ id → id ≤ 10 → Ready raw (id - 1) decls env → SectionValid raw id env profile

end Itasca.ModuleEnv
