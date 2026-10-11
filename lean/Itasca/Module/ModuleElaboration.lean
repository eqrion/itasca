import Itasca.Module.ModuleNameFacts
import Itasca.Binary.ModuleUnicodeUnique
import Itasca.Module.ModuleCodeContext
import Itasca.Module.ModuleDataTyping

open Aeneas Aeneas.Std

namespace Itasca.ModuleElaboration

/-- The fallback only makes the translation total. `Elaborates` separately
requires every type reference to be in bounds, so no accepted module uses it. -/
def functionType (types : List types.FuncType) (idx : U32) : functype :=
  ((types[idx.val]?).map EnvTranslation.funcType).getD (.mk_functype (.mk_list []) (.mk_list []))

theorem functionType_lookup {types : List types.FuncType} {idx : U32}
    (hi : idx.val < types.length) :
    functionType types idx = EnvTranslation.funcType types[idx.val] := by
  simp [functionType, List.getElem?_eq_getElem hi]

def importType (types : List types.FuncType) : module.ImportDesc → externtype
  | .Func idx => .FUNC (functionType types idx)
  | .Table tt => .TABLE (EnvTranslation.tableType tt)
  | .Memory mt => .MEM (EnvTranslation.memType mt)
  | .Global gt => .GLOBAL (Translate.globalType gt)

def importDecl (types : List types.FuncType) (entry : ModuleBinary.Import) : «import» :=
  .IMPORT (ModuleBinary.nameOfBytes entry.moduleName) (ModuleBinary.nameOfBytes entry.name)
    (importType types entry.desc)

def exportIndex : module.ExportDesc → externidx
  | .Func idx => .FUNC (.mk_uN idx.val)
  | .Table idx => .TABLE (.mk_uN idx.val)
  | .Memory idx => .MEM (.mk_uN idx.val)
  | .Global idx => .GLOBAL (.mk_uN idx.val)

def exportDecl (entry : ModuleBinary.Export) : «export» :=
  .EXPORT (ModuleBinary.nameOfBytes entry.name) (exportIndex entry.desc)

def element (entry : ModuleBinary.Element) : elem :=
  .ELEM .FUNCREF (entry.init.map (fun idx => [instr.REF_FUNC (.mk_uN idx.val)]))
    (.ACTIVE (.mk_uN entry.tableIdx.val) (ModuleConstants.expression entry.offset))

def table (tt : types.TableType) : _root_.table := .TABLE (EnvTranslation.tableType tt)

def memory (mt : types.MemType) : mem := .MEMORY (EnvTranslation.memType mt)

def start (idx : U32) : _root_.start := .START (.mk_uN idx.val)

/-- Elaboration retains the decoded declarations, ordered exports, and exact
function bodies, expanding only the binary representation's indexed forms. -/
def moduleOf (raw : ModuleBinary.Module) : _root_.module :=
  .MODULE (raw.types.map (fun ft => .TYPE (EnvTranslation.funcType ft)))
    (raw.imports.map (importDecl raw.types))
    (List.zipWith CodeEntry.function raw.functions raw.codes)
    (raw.globals.map ModuleConstants.global) (raw.tables.map table) (raw.memories.map memory)
    (raw.elements.map element) (raw.data.map ModuleData.translate) (raw.start.map start)
    (raw.exports.map exportDecl)

/-- No validator call occurs in elaboration. The bounds exclude fallback
lookups, and the count equality excludes truncation by `zipWith`. -/
structure Elaborates (raw : ModuleBinary.Module) (spec : _root_.module) : Prop where
  module_eq : spec = moduleOf raw
  imports : ∀ entry ∈ raw.imports, ∀ idx, entry.desc = .Func idx → idx.val < raw.types.length
  functions : ∀ idx ∈ raw.functions, idx.val < raw.types.length
  code_count : raw.functions.length = raw.codes.length

/-- The additional module-level conditions missing from the generated 2.0
judgment. Instruction syntax itself is restricted by `ModuleBinary`. -/
structure ModuleConditions (raw : ModuleBinary.Module) : Prop where
  unique_exports : (raw.exports.map (fun entry => ModuleBinary.nameOfBytes entry.name)).Nodup
  table_count : (ModuleTranslation.tables (raw.imports.map (fun entry => importType raw.types entry.desc))).length +
    raw.tables.length ≤ 1
  memory_count : (ModuleTranslation.mems (raw.imports.map (fun entry => importType raw.types entry.desc))).length +
    raw.memories.length ≤ 1
  arity : ∀ ft ∈ raw.types, ft.results.val.length ≤ 1

end Itasca.ModuleElaboration
