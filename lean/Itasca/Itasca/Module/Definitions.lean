import Itasca.Results.Definitions.Validation

/-! Proof helpers for intermediate states; public results use the semantic
vocabulary in Interface. Keeping these here avoids exposing parser progress
and implementation accounting as part of the public contract. -/

namespace Itasca.Module.Environment
open Aeneas Aeneas.Std Itasca

/-- The declared contents of each pre-code section, kept apart rather than merged with imports. -/
structure Declarations where
  types : List wasm_types.FuncType := []
  imports : List Binary.Import := []
  functions : List U32 := []
  tables : List _root_.Itasca.wasm_types.TableType := []
  memories : List _root_.Itasca.wasm_types.MemType := []
  globals : List Binary.Global := []
  exports : List Binary.Export := []
  start : Option U32 := none
  elements : List Binary.Element := []
  dataCount : Option U32 := none

end Itasca.Module.Environment

namespace Itasca.Module.Environment
open Aeneas Aeneas.Std Itasca

/-- Sections ranked after `last` are still empty, which excludes duplicate and misordered
sections. -/
def Phase (last : Nat) (decls : Declarations) : Prop :=
  (last < 1 → decls.types = []) ∧
  (last < 2 → decls.imports = []) ∧
  (last < 3 → decls.functions = []) ∧
  (last < 4 → decls.tables = []) ∧
  (last < 5 → decls.memories = []) ∧
  (last < 6 → decls.globals = []) ∧
  (last < 7 → decls.exports = []) ∧
  (last < 8 → decls.start = none) ∧
  (last < 9 → decls.elements = []) ∧
  (last < 10 → decls.dataCount = none)

end Itasca.Module.Environment

namespace Itasca.Module.Environment
open Aeneas Aeneas.Std Itasca

/-- The environment `env` stores exactly the declarations `decls`, and its caches are the merged
index spaces of `decls`. -/
structure Represents (env : metadata.ModuleMetadata metadata.CodeMetadata) (decls : Declarations) : Prop where
  types : decls.types = env.code.types.val
  imports : env.imports.val.map (fun i => (i.module.val, i.name.val, i.kind)) =
    decls.imports.map importRecord
  exports : decls.exports = env.exports.val.map rawExport
  start : decls.start = env.code.start
  elements : decls.elements = env.elements.val.map rawElement
  elementTypes : env.code.elem_segment_types.val = decls.elements.map Binary.Element.elem
  dataCount : decls.dataCount = env.code.data_count
  cache : Cache env.code decls.imports decls.functions decls.globals decls.tables decls.memories

end Itasca.Module.Environment

namespace Itasca.Module.Environment
open Aeneas Aeneas.Std Itasca

/-- Descriptor flags agree with the start function and the ordered export records. -/
structure DescriptorFlags (env : metadata.ModuleMetadata metadata.CodeMetadata) : Prop where
  eager : ∀ i d, env.code.funcs.val[i]? = some d → (d.eager = true ↔
    ∃ idx : U32, idx.val = i ∧ (env.code.start = some idx ∨ ∃ e ∈ env.exports.val, e.desc = .Func idx))
  tablesExported : ∀ i d, env.code.tables.val[i]? = some d → (d.is_exported = true ↔
    ∃ idx : U32, idx.val = i ∧ ∃ e ∈ env.exports.val, e.desc = .Table idx)
  memoriesExported : ∀ i d, env.code.memories.val[i]? = some d → (d.is_exported = true ↔
    ∃ idx : U32, idx.val = i ∧ ∃ e ∈ env.exports.val, e.desc = .Memory idx)
  globalsExported : ∀ i d, env.code.globals.val[i]? = some d → (d.is_exported = true ↔
    ∃ idx : U32, idx.val = i ∧ ∃ e ∈ env.exports.val, e.desc = .Global idx)

/-- All slots through rank `last` are complete in `decls`, including omitted empty sections, and
match the raw module `raw`. The environment `env` represents `decls`. -/
structure Ready (raw : Binary.Module) (last : Nat) (decls : Declarations)
    (env : metadata.ModuleMetadata metadata.CodeMetadata) : Prop where
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

end Itasca.Module.Environment

namespace Itasca.Binary
open Aeneas Aeneas.Std Itasca


end Itasca.Binary

namespace Itasca.Module.Code
open Aeneas Aeneas.Std Itasca

/-- The fields of a code section header: the entry count, the position of the first entry and the
end of the section. -/
structure Header where
  count : U32
  entries : Usize
  «end» : Usize

end Itasca.Module.Code

namespace Itasca.Module.Code
open Aeneas Aeneas.Std Itasca

/-- The header `cs` is the code section header at `start`, with an entry count equal to the number
of defined functions. -/
def Section (data : Slice U8) (start : Usize) (env : metadata.CodeMetadata) (cs : Header) : Prop :=
  ∃ content, Binary.SectionHeader data start 10#u8 content cs.end ∧
    Binary.Leb128.Decoded data content cs.count cs.entries ∧
    cs.count.val = (Translation.Environment.definedTypeIndices env).length

end Itasca.Module.Code

namespace Itasca.Module.Constants
open Aeneas Aeneas.Std Itasca

/-- The operand type corresponding to a table element type. -/
def referenceValueType : wasm_types.ElemType → wasm_types.ValueType
  | .FuncRef => .FuncRef
  | .ExternRef => .ExternRef

end Itasca.Module.Constants

namespace Itasca.Module.Constants
open Aeneas Aeneas.Std Itasca

/-- The initializer has the given type in `env`. `ref.func` needs an in-range function index, and
`global.get` needs an imported immutable global. -/
inductive Valid (env : metadata.CodeMetadata) : wasm_types.ConstExpr → wasm_types.ValueType → Prop where
  | i32 (value : I32) : Valid env (.I32 value) .I32
  | i64 (value : I64) : Valid env (.I64 value) .I64
  | f32 (value : U32) : Valid env (.F32 value) .F32
  | f64 (value : U64) : Valid env (.F64 value) .F64
  | v128 (low high : U64) : Valid env (.V128 low high) .V128
  | refNull (ty : wasm_types.ElemType) : Valid env (.RefNull ty) (referenceValueType ty)
  | refFunc (idx : U32) (hi : idx.val < env.funcs.val.length) :
      Valid env (.RefFunc idx) .FuncRef
  | globalGet (idx : U32) (gt : wasm_types.GlobalType)
      (hi : idx.val < env.globals.val.length)
      (hgt : env.globals.val[idx.val].gtype = gt)
      (himport : idx.val < env.num_imported_globals.val)
      (hconst : gt.mutability = .Const) : Valid env (.GlobalGet idx) gt.valtype

end Itasca.Module.Constants

namespace Itasca.Module.Segments
open Aeneas Aeneas.Std Itasca

/-- The element segment is valid against `env`. An active segment names a table of its element type
with a valid `i32` offset, and every initializer is a valid constant of the element type. Validity
describes index spaces and initializer types independently of binary decoding and the generated
module judgment. -/
def elementValid (env : metadata.CodeMetadata) (entry : metadata.Element) : Prop :=
  (match entry.mode with
    | .Active idx offset => ∃ hi : idx.val < env.tables.val.length,
        env.tables.val[idx.val].ty.elem = entry.elem ∧ Module.Constants.Valid env offset .I32
    | .Passive | .Declarative => True) ∧
  ∀ init ∈ (Module.Environment.rawElement entry).init,
    Module.Constants.Valid env init (Module.Constants.referenceValueType entry.elem)

end Itasca.Module.Segments

namespace Itasca.Module.Environment

/-- The import/definition ordering certifies the subtraction performed by
`CodeMetadata::num_func_defs`, including when every function is imported. -/
theorem Cache.imported_func_bound {env imports functions globals tables memories}
    (h : Cache env imports functions globals tables memories) :
    env.num_imported_funcs.val ≤ env.funcs.val.length := by
  have sizes := congrArg List.length h.funcs
  simp only [List.length_map, List.length_append] at sizes
  rw [h.numFuncs, sizes]
  omega

/-- Skipping the import prefix in retained descriptors recovers the function section. -/
theorem Cache.defined_type_indices {env imports functions globals tables memories}
    (h : Cache env imports functions globals tables memories) :
    Translation.Environment.definedTypeIndices env = functions := by
  simp [Translation.Environment.definedTypeIndices, List.map_drop, h.funcs, h.numFuncs]

end Itasca.Module.Environment
