import Itasca.Module.Env.NameFacts
import Itasca.Binary.UnicodeUnique
import Itasca.Module.Code.Context
import Itasca.Module.Elab.SegmentTyping

/-!
# Elaboration of raw modules

`moduleOf` translates a raw `ModuleBinary.Module` into the SpecTec `module` syntax, expanding the
binary representation's indexed forms. `Elaborates` relates a SpecTec module to a raw one, and
`ModuleConditions` states the module-level restrictions that the generated 2.0 judgment lacks.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleElaboration

/-- The SpecTec type of function type index `idx`, with an empty type as the fallback that makes
the translation total. `Elaborates` requires every type reference to be in bounds, so no accepted
module uses the fallback. -/
def functionType (types : List wasm_types.FuncType) (idx : U32) : functype :=
  ((types[idx.val]?).map EnvTranslation.funcType).getD (.mk_functype (.mk_list []) (.mk_list []))

/-- An in-bounds type index looks up its translated function type. -/
theorem functionType_lookup {types : List wasm_types.FuncType} {idx : U32}
    (hi : idx.val < types.length) :
    functionType types idx = EnvTranslation.funcType types[idx.val] := by
  simp [functionType, List.getElem?_eq_getElem hi]

/-- The SpecTec external type of an import descriptor. -/
def importType (types : List wasm_types.FuncType) : metadata.ImportDesc → externtype
  | .Func idx => .FUNC (functionType types idx)
  | .Table tt => .TABLE (EnvTranslation.tableType tt)
  | .Memory mt => .MEM (EnvTranslation.memType mt)
  | .Global gt => .GLOBAL (Translate.globalType gt)

/-- The SpecTec import declaration of a raw import. -/
def importDecl (types : List wasm_types.FuncType) (entry : ModuleBinary.Import) : «import» :=
  .IMPORT (ModuleBinary.nameOfBytes entry.moduleName) (ModuleBinary.nameOfBytes entry.name)
    (importType types entry.desc)

/-- The SpecTec external index of an export descriptor. -/
def exportIndex : metadata.ExportDesc → externidx
  | .Func idx => .FUNC (.mk_uN idx.val)
  | .Table idx => .TABLE (.mk_uN idx.val)
  | .Memory idx => .MEM (.mk_uN idx.val)
  | .Global idx => .GLOBAL (.mk_uN idx.val)

/-- The SpecTec export declaration of a raw export. -/
def exportDecl (entry : ModuleBinary.Export) : «export» :=
  .EXPORT (ModuleBinary.nameOfBytes entry.name) (exportIndex entry.desc)

/-- The SpecTec element segment of a raw element segment. -/
def element (entry : ModuleBinary.Element) : elem :=
  .ELEM (Translate.referenceType entry.elem) (entry.init.map ModuleConstants.expression)
    (ModuleSegments.elementMode entry.mode)

/-- The SpecTec table of a table type. -/
def table (tt : wasm_types.TableType) : _root_.table := .TABLE (EnvTranslation.tableType tt)

/-- The SpecTec memory of a memory type. -/
def memory (mt : wasm_types.MemType) : mem := .MEMORY (EnvTranslation.memType mt)

/-- The SpecTec start function of a function index. -/
def start (idx : U32) : _root_.start := .START (.mk_uN idx.val)

/-- The SpecTec module of a raw module. It keeps the decoded declarations, the ordered exports and
the exact function bodies, and only expands the binary representation's indexed forms. -/
def moduleOf (raw : ModuleBinary.Module) : _root_.module :=
  .MODULE (raw.types.map (fun ft => .TYPE (EnvTranslation.funcType ft)))
    (raw.imports.map (importDecl raw.types))
    (List.zipWith CodeEntry.function raw.functions raw.codes)
    (raw.globals.map ModuleConstants.global) (raw.tables.map table) (raw.memories.map memory)
    (raw.elements.map element) (raw.data.map ModuleData.translate) (raw.start.map start)
    (raw.exports.map exportDecl)

/-- `spec` is the elaboration of `raw`. No validator call occurs in elaboration. The index bounds
exclude fallback lookups, and the count equality excludes truncation by `zipWith`. -/
structure Elaborates (raw : ModuleBinary.Module) (spec : _root_.module) : Prop where
  module_eq : spec = moduleOf raw
  imports : ∀ entry ∈ raw.imports, ∀ idx, entry.desc = .Func idx → idx.val < raw.types.length
  functions : ∀ idx ∈ raw.functions, idx.val < raw.types.length
  code_count : raw.functions.length = raw.codes.length

/-- The module-level conditions that `Module_ok` does not express: unique export names, the
profile's table count limit, at most one memory, and function types admitted by the profile.
Instruction syntax itself is restricted by `ModuleBinary`. -/
structure ModuleConditions (raw : ModuleBinary.Module) (profile : ValidationProfile := .Wasm1) : Prop where
  unique_exports : (raw.exports.map (fun entry => ModuleBinary.nameOfBytes entry.name)).Nodup
  table_count : profile = .Wasm1 → (ModuleTranslation.tables (raw.imports.map (fun entry => importType raw.types entry.desc))).length +
    raw.tables.length ≤ 1
  memory_count : (ModuleTranslation.mems (raw.imports.map (fun entry => importType raw.types entry.desc))).length +
    raw.memories.length ≤ 1
  arity : ∀ ft ∈ raw.types, Itasca.Profile.FuncType profile ft

end Itasca.ModuleElaboration
