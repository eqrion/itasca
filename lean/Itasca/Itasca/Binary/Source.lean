import Itasca.Results.Definitions.Binary
import WebAssembly.Binary

namespace Itasca.Binary.Source

open Aeneas.Std
open WebAssembly

@[simp] theorem valueType_toSpec (ty) : (valueType ty).toSpec = Translation.valueType ty := by
  cases ty <;> rfl

@[simp] theorem valueByte_eq (ty) :
    sourceByte (Itasca.Binary.valueByte ty) = WebAssembly.Binary.valueByte (valueType ty) := by
  cases ty <;> rfl

@[simp] theorem referenceByte_eq (ty) : sourceByte (Itasca.Body.ReferencesBinary.referenceByte ty) =
    WebAssembly.Binary.ReferencesBinary.referenceByte (Translation.referenceType ty) := by
  cases ty <;> rfl

def token : Body.Token → WebAssembly.Binary.Token
  | .plain op => .plain op
  | .block bt => .block (Body.blockType bt)
  | .loop bt => .loop (Body.blockType bt)
  | .if_ bt => .if_ (Body.blockType bt)
  | .else_ => .else_
  | .end_ => .end_

def code (e : Itasca.Binary.Code) : WebAssembly.Binary.Code :=
  ⟨e.locals.map localDecl, e.body⟩

def rawModule (m : Itasca.Binary.Module) : WebAssembly.Binary.Module where
  types := m.types.map Translation.Environment.funcType
  imports := m.imports.map importEntry
  functions := m.functions.map UScalar.val
  tables := m.tables.map Translation.Environment.tableType
  memories := m.memories.map Translation.Environment.memType
  globals := m.globals.map globalEntry
  exports := m.exports.map exportEntry
  start := m.start.map UScalar.val
  elements := m.elements.map element
  dataCount := m.dataCount.map UScalar.val
  codes := m.codes.map code
  data := m.data.map dataEntry

end Itasca.Binary.Source
