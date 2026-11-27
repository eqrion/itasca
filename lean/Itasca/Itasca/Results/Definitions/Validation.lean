import Aeneas
import ItascaRust.Funs
import Itasca.Binary.Source
import Itasca.Results.Definitions.Foundations
import Itasca.Results.Definitions.Observations
import Itasca.Results.Definitions.Visitor
import WebAssembly

open WebAssembly

/-!
# From bytes to validated modules

Read these certificates from independent body validity through function entries to whole-module
elaboration and returned metadata. Binary encoding, generated source typing, declared
references and implementation bounds are distinct conjuncts because soundness and
completeness use them differently. Callback and entry traces retain the actual byte
coordinates. This unit states what validation establishes; the construction proofs remain
in Body, CodeEntry and Module.

-/

section BodyState

/-!
## Independent body validity

A body certificate joins the binary grammar, generated typing and declared-reference
condition. Validator control stacks and intermediate-state invariants belong to
the construction proof, so they are not part of this certificate.
-/

open Aeneas Aeneas.Std

namespace Itasca.Body

/-- The typing context of a function body. Return typing comes from the selected type-section
entry. The extracted scalar context carries empty results because `return` is dispatched by
the Wasm 2.0 body loop itself. Function parameters are already included in locals. -/
def bodyContext (env : metadata.CodeMetadata) (locals : alloc.vec.Vec wasm_types.ValueType)
    (ft : wasm_types.FuncType) : context := Translation.Environment.context env ⟨locals, ft.results⟩

/-- The context of a function body: the function label on top of `bodyContext`. -/
def functionContext (env : metadata.CodeMetadata) (locals : alloc.vec.Vec wasm_types.ValueType)
    (ft : wasm_types.FuncType) : context :=
  Body.Control.labelContext (ft.results.val.map Translation.valueType) ++ bodyContext env locals ft

/-- The instruction sequence is typed by the generated `Instrs_ok` rules from no operands to the
function's result type, with the function label in scope. -/
def FunctionTyped (env : metadata.CodeMetadata) (locals : alloc.vec.Vec wasm_types.ValueType)
    (ft : wasm_types.FuncType) (ops : List instr) : Prop :=
  Instrs_ok (functionContext env locals ft)
    ops (.mk_functype (.mk_list []) (.mk_list (ft.results.val.map Translation.valueType)))

/-- The whole-body certificate used by both soundness and completeness. It contains no
validator-success premise. -/
def Validated (data : Slice U8) (env : metadata.CodeMetadata)
    (locals : alloc.vec.Vec wasm_types.ValueType) (index : U32) : Prop :=
  ∃ ft ops, env.types.val[index.val]? = some ft ∧ BodyEncoding data ops ∧
    FunctionTyped env locals ft ops ∧
    Spec.DeclaredReferences.Instructions (Translation.Environment.declaredReferences env) ops

end Itasca.Body

end BodyState

section BodyCallbackTrace

/-!
## Callback byte traces and acceptance

Byte provenance and acceptance share one ordered observation list. Completed
chunks distinguish fully decoded instructions from partial table callbacks;
acceptance additionally requires source typing and declared references.
-/

/-!
## Independent callback byte traces

Action tokens, completed chunks and body traces relate ordered observations to exact
instruction bytes and returned outcomes.
-/

namespace Itasca.Body.CallbackTrace
open Aeneas Aeneas.Std
open Itasca.Visitor.Trace

/-- The Wasm 2.0 token of an operator callback. Block, loop and if tokens keep their indexed
parameter and result signatures. -/
def actionToken (action : Action) (pending : List U32) : Option Token :=
  match action with
  | .block bt => some (.block bt)
  | .loop bt => some (.loop bt)
  | .if_ bt => some (.if_ bt)
  | _ => action.token pending

/-- Exactly the callbacks for one fully decoded instruction. The table case
separates vector entries from its default target, which has no label callback.
Computed metadata and state snapshots remain in the observations. -/
inductive Chunk (data : Slice U8) (start : Usize) :
    List Observation → Token → Usize → Prop where
  | single (st : code.OpIterState) (action : Action) (reply : VisitResult) (token : Token) :
      actionToken action [] = some token → action.opcode ≠ some 0x0E#u8 →
      At data start token st.pos →
      Chunk data start [⟨.op st action, reply⟩] token st.pos
  | table {pos count first labels depths last fallback st bt reply} :
      Body.Scalar.BytesAt data start [0x0E#u8] pos →
      Binary.Leb128.Decoded data pos count first →
      LabelsAt data first labels depths last → depths.length = count.val →
      Binary.Leb128.Decoded data last fallback st.pos →
      At data start
        (.plain (.BR_TABLE (depths.map (fun i => .mk_uN i.val)) (.mk_uN fallback.val))) st.pos →
      Chunk data start (labels ++ [⟨.op st (.br_table fallback bt), reply⟩])
        (.plain (.BR_TABLE (depths.map (fun i => .mk_uN i.val)) (.mk_uN fallback.val))) st.pos

/-- Concatenation of complete instruction chunks, independently of execution. -/
inductive Completed (data : Slice U8) :
    Usize → List Observation → List Token → Usize → Prop where
  | nil (pos : Usize) (bound : pos.val ≤ data.length) : Completed data pos [] [] pos
  | cons {start first token middle rest tokens next} :
      Chunk data start first token middle → Completed data middle rest tokens next →
      Completed data start (first ++ rest) (token :: tokens) next

/-- Whole-run byte provenance. Only the final rejected table can be partial. -/
def BodyTrace (data : Slice U8) (start : Usize) (observations : List Observation)
    (result : BodyResult) : Prop :=
  Outcomes observations result ∧ ∃ complete tokens cursor tail,
    observations = complete ++ tail ∧ Completed data start complete tokens cursor ∧
    (tail = [] ∨ PartialTable data cursor tail) ∧
    (result = .Ok () → tail = [] ∧ cursor.val = data.length)

end Itasca.Body.CallbackTrace

/-!
## Accepted callback traces

`AcceptedBody` connects the recorded observations of an accepted body to its independent
encoding, typing and declared references.
-/

namespace Itasca.Body.CallbackTrace
open Aeneas Aeneas.Std
open Itasca.Visitor.Trace

/-- The accepted callbacks spell the same independently encoded and SpecTec-typed body, with
indexed block signatures and declared references. -/
def AcceptedBody (data : Slice U8) (env : metadata.CodeMetadata)
    (ctx : code.Context) (index : U32) (observations : List Observation) : Prop :=
  AllAccepted observations ∧ ∃ ft tokens ops next,
    env.types.val[index.val]? = some ft ∧
    Completed data 0#usize observations tokens next ∧ next.val = data.length ∧
    BodyTokens tokens ops ∧ FunctionTyped env ctx.locals ft ops ∧
    Spec.DeclaredReferences.Instructions (Translation.Environment.declaredReferences env) ops

end Itasca.Body.CallbackTrace

end BodyCallbackTrace

section CodeEntrySemantics

/-!
## Function-entry bytes and source typing

Read the exact byte spelling alongside its source context and typing. Both use
the same independent code entry; implementation signature bounds remain in Limits.
-/

/-!
## Exact function-entry bytes

Body/code encodings account for size prefixes, local declarations and the final
`end`. The source interpretation below supplies typing and declared references.
-/

namespace Itasca.CodeEntry
open Aeneas Aeneas.Std

/-- The bytes of a body for the Wasm 2.0 instruction grammar. -/
abbrev BodyBytes := WebAssembly.Binary.BodyBytesWith Body.TokenEncoding Body.BodyTokens

abbrev CodeEncoding (entry : Binary.Code) :=
  WebAssembly.Binary.CodeEntryWith Binary.Leb128.Encoding Binary.LocalEncoding BodyBytes entry.locals entry.body

/-- Both implementation bounds apply to the same local groups and body span used by the grammar. -/
def CodeEncodingWithinLimits (entry : Binary.Code) (bs : List U8) : Prop :=
  entry.declared.length ≤ limits.MAX_LOCALS.val ∧
    WebAssembly.Binary.CodeEntryWith Binary.Leb128.Encoding Binary.LocalEncoding
      (fun ops body => BodyBytes ops body ∧ body.length ≤ limits.MAX_FUNCTION_BYTES.val) entry.locals entry.body bs

end Itasca.CodeEntry

section

/-!
## Function-entry source interpretation

Body contexts, instruction types, entry typing and local expansion relate code entries to the environment and generated specification.
-/

open Aeneas Aeneas.Std

namespace Itasca.CodeEntry

/-- The typing context of a function body: the module's index spaces, the parameters followed by
the declared locals, and a single label and the return type both given by the results. -/
def bodyContext (env : metadata.CodeMetadata) (params declared results : List wasm_types.ValueType) : context :=
  { TYPES := env.types.val.map Translation.Environment.funcType
    FUNCS := env.funcs.val.map (Translation.Environment.descriptorType env.types.val)
    GLOBALS := env.globals.val.map (fun g => Translation.globalType g.gtype)
    TABLES := env.tables.val.map (fun d => Translation.Environment.tableType d.ty)
    MEMS := env.memories.val.map (fun d => Translation.Environment.memType d.ty)
    ELEMS := Translation.Environment.elementTypes env
    DATAS := Translation.Environment.dataTypes env
    LOCALS := (params ++ declared).map Translation.valueType
    LABELS := [.mk_list (results.map Translation.valueType)]
    RETURN := some (.mk_list (results.map Translation.valueType))}

/-- The type `[] -> results` that a body must have. -/
def instructionType (ft : wasm_types.FuncType) : functype :=
  .mk_functype (.mk_list []) (.mk_list (ft.results.val.map Translation.valueType))

/-- The code entry has a function type in the environment's type table. Its body is typed in
`bodyContext` with the parameters followed by the declared locals and mentions only
declared function references. -/
structure Typed (env : metadata.CodeMetadata) (typeIdx : U32) (entry : Binary.Code) : Prop where
  type_lt : typeIdx.val < env.types.val.length
  typed : Instrs_ok (bodyContext env env.types.val[typeIdx.val].params.val
    entry.declared env.types.val[typeIdx.val].results.val) entry.body
    (instructionType env.types.val[typeIdx.val])
  declared : Spec.DeclaredReferences.Instructions
    (Translation.Environment.declaredReferences env) entry.body

/-- The SpecTec function for a code entry with type index `typeIdx`. -/
def function (typeIdx : U32) (entry : Binary.Code) : func :=
  .FUNC (.mk_uN typeIdx.val) (entry.declared.map (fun t => .LOCAL (Translation.valueType t))) entry.body

end Itasca.CodeEntry

namespace Itasca.CodeEntry.Locals

/-- The expansion of grouped local declarations into one type per local. -/
def declared (groups : List (U32 × wasm_types.ValueType)) : List wasm_types.ValueType :=
  groups.flatMap (fun (count, ty) => List.replicate count.val ty)

end Itasca.CodeEntry.Locals

end

end CodeEntrySemantics

section CodeEntryTrace

/-!
## Accepted entry observations

`AcceptedTrace` connects one returning code-entry validation run to its independently decoded body and callback observations.
-/

open Aeneas Aeneas.Std
open Itasca.Visitor.Trace

namespace Itasca.CodeEntry

/-- The observations of an accepted entry come from a function-start event followed by body
operator events. The code bytes, generated typing and recorded operators share one instruction
tree. The start event uses module offsets, and operator states use offsets of the sliced body. -/
def AcceptedTrace (data : Slice U8) (env : metadata.CodeMetadata)
    (index start finish : Usize) (observations : List Observation) : Prop :=
  ∃ (typeIdx : U32) (groups : List (U32 × wasm_types.ValueType)) (ctx : code.Context)
      (bodyStart : Usize) (body : Slice U8) (bodyObservations : List Observation)
      (tokens : List Body.Token) (ops : List instr) (next : Usize),
    (∃ hi : index.val < (Translation.Environment.definedTypeIndices env).length,
      (Translation.Environment.definedTypeIndices env)[index.val] = typeIdx) ∧
    Binary.At (CodeEntry.CodeEncoding ) data start ⟨groups, ops⟩ finish ∧
    CodeEntry.Typed env typeIdx ⟨groups, ops⟩ ∧
    (CodeEntry.Locals.declared groups).length ≤ limits.MAX_LOCALS.val ∧
    (∃ ht : typeIdx.val < env.types.val.length,
      ctx.locals.val = env.types.val[typeIdx.val].params.val ++ CodeEntry.Locals.declared groups ∧
      ctx.results.val = env.types.val[typeIdx.val].results.val) ∧
    Body.Scalar.BytesAt data bodyStart body.val finish ∧
    observations = ⟨.functionStart ctx typeIdx bodyStart finish, .Ok ()⟩ :: bodyObservations ∧
    AllAccepted bodyObservations ∧
    Body.CallbackTrace.Completed body 0#usize bodyObservations tokens next ∧
    next.val = body.length ∧ Body.BodyTokens tokens ops ∧
    (∃ (content : Usize) (size : U32),
      Binary.Leb128.Decoded data start size content ∧
      finish.val = content.val + size.val ∧
      Binary.At (Binary.VecEncoding Binary.LocalEncoding)
        data content groups bodyStart)

end Itasca.CodeEntry

end CodeEntryTrace

section CodeEntryLimits

/-!
## Implementation signature bounds

`FuncTypeWithinLimits` bounds parameter/result counts; `EnvironmentWithinLimits` applies those bounds to both type tables and cached function signatures.
-/

open Aeneas Aeneas.Std

namespace Itasca.CodeEntry

/-- The implementation bounds on a signature, separate from language validity: the parameter and result counts are bounded. -/
def FuncTypeWithinLimits (ft : wasm_types.FuncType) : Prop :=
  ft.params.val.length ≤ limits.MAX_MULTI_VALUE_PARAMS.val ∧
    ft.results.val.length ≤ limits.MAX_MULTI_VALUE_RESULTS.val

/-- Every signature in the type table and the function signature cache satisfies
`FuncTypeWithinLimits`. -/
structure EnvironmentWithinLimits (env : metadata.CodeMetadata) : Prop where
  types : ∀ ft ∈ env.types.val, FuncTypeWithinLimits ft
  funcs : ∀ d ∈ env.funcs.val, d.type_index.val < env.types.val.length

end Itasca.CodeEntry

end CodeEntryLimits

section ModuleEnvironment

/-!
## Environment declarations and readiness

Section framing, merged type/index spaces and readiness describe the environment supplied to body validation.
-/

section

/-!
## Environment declarations and readiness

Merged index-space caches describe the environment supplied
to code validation. These are independent correspondence conditions, not parser calls.
-/

/-!
## Environment caches and resolution

Imported counts, resolution and `Cache` describe the merged type/index spaces represented by metadata.
-/

namespace Itasca.Module.Environment
open Aeneas Aeneas.Std

/-- The type indices of the function imports, in import order. -/
def importedFuncs (imports : List Binary.Import) : List U32 :=
  imports.filterMap fun entry => match entry.desc with | .Func idx => some idx | _ => none

/-- The types of the global imports, in import order. -/
def importedGlobals (imports : List Binary.Import) : List wasm_types.GlobalType :=
  imports.filterMap fun entry => match entry.desc with | .Global gt => some gt | _ => none

/-- The types of the table imports, in import order. -/
def importedTables (imports : List Binary.Import) : List wasm_types.TableType :=
  imports.filterMap fun entry => match entry.desc with | .Table tt => some tt | _ => none

/-- The types of the memory imports, in import order. -/
def importedMems (imports : List Binary.Import) : List wasm_types.MemType :=
  imports.filterMap fun entry => match entry.desc with | .Memory mt => some mt | _ => none

/-- Type index `idx` is in range of `typeList` and denotes the function type `ft`. -/
def Resolves (typeList : List wasm_types.FuncType) (idx : U32) (ft : wasm_types.FuncType) : Prop :=
  ∃ hi : idx.val < typeList.length, typeList[idx.val] = ft

/-- Decode-time import and definition order in every code index space. -/
structure Cache (env : metadata.CodeMetadata) (imports : List Binary.Import)
    (functions : List U32) (globals : List Binary.Global)
    (tables : List wasm_types.TableType) (memories : List wasm_types.MemType) : Prop where
  funcs : env.funcs.val.map metadata.FuncDesc.type_index = importedFuncs imports ++ functions
  numFuncs : env.num_imported_funcs.val = (importedFuncs imports).length
  globalEntries : env.globals.val.map (fun g => (g.gtype, g.init)) =
    ((importedGlobals imports).map fun ty => (ty, none)) ++ globals.map (fun g => (g.gtype, some g.init))
  numGlobals : env.num_imported_globals.val = (importedGlobals imports).length
  tableEntries : env.tables.val.map (fun d => (d.ty, d.is_imported)) =
    ((importedTables imports).map fun ty => (ty, true)) ++ tables.map (fun ty => (ty, false))
  memoryEntries : env.memories.val.map (fun d => (d.ty, d.is_imported)) =
    ((importedMems imports).map fun ty => (ty, true)) ++ memories.map (fun ty => (ty, false))

end Itasca.Module.Environment

/-!
## Ordered environment declarations

Raw imports, exports and elements connect returned metadata to the independent
binary grammar. Parser phase and readiness witnesses live in Module.Definitions.
-/

namespace Itasca.Module.Environment
open Aeneas Aeneas.Std

/-- Import names and kinds are module-owned, while the payload enters its code index space. -/
def importRecord (entry : Binary.Import) : List U8 × List U8 × metadata.ImportKind :=
  (entry.moduleName, entry.name, match entry.desc with
    | .Func _ => .Func | .Table _ => .Table | .Memory _ => .Memory | .Global _ => .Global)

/-- The independent grammar's export corresponding to an extracted export. -/
def rawExport (entry : metadata.Export) : Binary.Export := ⟨entry.name.val, entry.desc⟩

/-- The independent grammar's element segment corresponding to an extracted element. -/
def rawElement (entry : metadata.Element) : Binary.Element :=
  ⟨entry.elem, entry.mode, match entry.init with
    | .Functions indices => indices.val.map wasm_types.ConstExpr.RefFunc
    | .Expressions exprs => exprs.val⟩

end Itasca.Module.Environment

end

end ModuleEnvironment

section ModuleCodeSection

/-!
## Code-section shape

Entry-position predicates relate code entries to their function indices and
SpecTec typing judgments. Header-reading witnesses are internal to the parser.
-/

open Aeneas Aeneas.Std

namespace Itasca.Module.Code

/-- The code entry is typed against the `i`-th defined function and has a declared local count
within `limits.MAX_LOCALS`. -/
def EntryAt (env : metadata.CodeMetadata) (i : Nat) (entry : Binary.Code) : Prop :=
  ∃ hi : i < (Translation.Environment.definedTypeIndices env).length,
    CodeEntry.Typed env (Translation.Environment.definedTypeIndices env)[i] entry ∧
    entry.declared.length ≤ limits.MAX_LOCALS.val

/-- The entries are `EntryAt` the defined functions in order, starting at function index `i`. -/
inductive EntriesTyped (env : metadata.CodeMetadata) : Nat → List Binary.Code → Prop where
  | nil (i : Nat) : EntriesTyped env i []
  | cons {i entry entries} : EntryAt env i entry →
      EntriesTyped env (i + 1) entries → EntriesTyped env i (entry :: entries)

end Itasca.Module.Code

end ModuleCodeSection

section ModuleInitializers

/-!
## Constant-expression interpretation

Instructions, expressions and globals describe initializer meaning independently
of parsing success. Internal initializer typing helpers are proved against
SpecTec judgments in the module proofs.
-/

open Aeneas Aeneas.Std

namespace Itasca.Module.Constants

/-- Translates an initializer to a SpecTec instruction. `V128` combines the low and high halves in
little-endian order. -/
def instruction : wasm_types.ConstExpr → instr
  | .I32 value => Spec.i32Const value
  | .I64 value => Spec.Constants.i64 value
  | .F32 bits => Spec.Constants.f32 bits
  | .F64 bits => Spec.Constants.f64 bits
  | .V128 low high => .VCONST .V128 (.mk_uN (low.val + high.val * 2 ^ 64))
  | .RefNull ty => .REF_NULL (Translation.referenceType ty)
  | .RefFunc idx => .REF_FUNC (.mk_uN idx.val)
  | .GlobalGet idx => .GLOBAL_GET (.mk_uN idx.val)

/-- The single-instruction SpecTec expression of an initializer. -/
def expression (e : wasm_types.ConstExpr) : expr := [instruction e]

/-- The SpecTec global of a decoded global. -/
def global (g : Binary.Global) : WebAssembly.global :=
  .GLOBAL (Translation.globalType g.gtype) (expression g.init)

end Itasca.Module.Constants

end ModuleInitializers

section ModuleElaboration

/-!
## Independent module elaboration and validity

Index-space projections and segment interpretation build one source module from
independent binary declarations. Elaboration excludes fallback lookups; restrictions
supply language conditions absent from the generated typing judgment.
-/

/-!
## Environment index spaces

Function, global, table and memory translations describe the source declarations represented by cached runtime metadata.
-/

namespace Itasca.Module.Translation
open Aeneas Aeneas.Std

/-- The function types among the external types, in order. -/
def funcs : List externtype → List functype
  | [] => []
  | .FUNC t :: rest => t :: funcs rest
  | _ :: rest => funcs rest

/-- The global types among the external types, in order. -/
def globals : List externtype → List globaltype
  | [] => []
  | .GLOBAL t :: rest => t :: globals rest
  | _ :: rest => globals rest

/-- The table types among the external types, in order. -/
def tables : List externtype → List tabletype
  | [] => []
  | .TABLE t :: rest => t :: tables rest
  | _ :: rest => tables rest

/-- The memory types among the external types, in order. -/
def mems : List externtype → List memtype
  | [] => []
  | .MEM t :: rest => t :: mems rest
  | _ :: rest => mems rest

end Itasca.Module.Translation

section

/-!
## Segment translation

Element/data modes, initializers and raw segment interpretations supply the source terms used by module validity.
-/

open Aeneas Aeneas.Std

namespace Itasca.Module.Segments

/-- The SpecTec element mode of an element segment mode. -/
def elementMode : metadata.ElementMode → elemmode
  | .Active idx offset => .ACTIVE (.mk_uN idx.val) (Module.Constants.expression offset)
  | .Passive => .PASSIVE
  | .Declarative => .DECLARE

/-- The SpecTec data mode of a data segment mode. -/
def dataMode : metadata.DataMode → datamode
  | .Active idx offset => .ACTIVE (.mk_uN idx.val) (Module.Constants.expression offset)
  | .Passive => .PASSIVE

end Itasca.Module.Segments

namespace Itasca.Module.Data

/-- The independent grammar's data segment corresponding to an extracted data segment. -/
def raw (segment : metadata.Data) : Binary.Data := ⟨segment.mode, segment.init.val⟩

/-- The SpecTec data segment of a raw data segment. -/
def translate (segment : Binary.Data) : WebAssembly.data :=
  .DATA (segment.init.map (fun b => .mk_byte b.val)) (Module.Segments.dataMode segment.mode)

end Itasca.Module.Data

end

/-!
## Raw-module elaboration and validity

Translation functions expand binary indices into specification syntax; `Elaborates` and module restrictions rule out invalid lookups and missing language conditions.
-/

namespace Itasca.Module.Elaboration
open Aeneas Aeneas.Std

/-- The SpecTec type of function type index `idx`, with an empty type as the fallback that makes
the translation total. `Elaborates` requires every type reference to be in bounds, so no accepted
module uses the fallback. -/
def functionType (types : List wasm_types.FuncType) (idx : U32) : functype :=
  ((types[idx.val]?).map Translation.Environment.funcType).getD (.mk_functype (.mk_list []) (.mk_list []))

/-- The SpecTec external type of an import descriptor. -/
def importType (types : List wasm_types.FuncType) : Binary.ImportDesc → externtype
  | .Func idx => .FUNC (functionType types idx)
  | .Table tt => .TABLE (Translation.Environment.tableType tt)
  | .Memory mt => .MEM (Translation.Environment.memType mt)
  | .Global gt => .GLOBAL (Translation.globalType gt)

/-- The SpecTec import declaration of a raw import. -/
def importDecl (types : List wasm_types.FuncType) (entry : Binary.Import) : «import» :=
  .IMPORT (Binary.nameOfBytes entry.moduleName) (Binary.nameOfBytes entry.name)
    (importType types entry.desc)

/-- The SpecTec external index of an export descriptor. -/
def exportIndex : metadata.ExportDesc → externidx
  | .Func idx => .FUNC (.mk_uN idx.val)
  | .Table idx => .TABLE (.mk_uN idx.val)
  | .Memory idx => .MEM (.mk_uN idx.val)
  | .Global idx => .GLOBAL (.mk_uN idx.val)

/-- The SpecTec export declaration of a raw export. -/
def exportDecl (entry : Binary.Export) : «export» :=
  .EXPORT (Binary.nameOfBytes entry.name) (exportIndex entry.desc)

/-- The SpecTec element segment of a raw element segment. -/
def element (entry : Binary.Element) : elem :=
  .ELEM (Translation.referenceType entry.elem) (entry.init.map Module.Constants.expression)
    (Module.Segments.elementMode entry.mode)

/-- The SpecTec table of a table type. -/
def table (tt : wasm_types.TableType) : WebAssembly.table := .TABLE (Translation.Environment.tableType tt)

/-- The SpecTec memory of a memory type. -/
def memory (mt : wasm_types.MemType) : mem := .MEMORY (Translation.Environment.memType mt)

/-- The SpecTec start function of a function index. -/
def start (idx : U32) : WebAssembly.start := .START (.mk_uN idx.val)

/-- The SpecTec module of a raw module. It keeps the decoded declarations, the ordered exports and
the exact function bodies, and only expands the binary representation's indexed forms. -/
def moduleOf (raw : Binary.Module) : WebAssembly.module :=
  .MODULE (raw.types.map (fun ft => .TYPE (Translation.Environment.funcType ft)))
    (raw.imports.map (importDecl raw.types))
    (List.zipWith CodeEntry.function raw.functions raw.codes)
    (raw.globals.map Module.Constants.global) (raw.tables.map table) (raw.memories.map memory)
    (raw.elements.map element) (raw.data.map Module.Data.translate) (raw.start.map start)
    (raw.exports.map exportDecl)

/-- `spec` is the elaboration of `raw`. No validator call occurs in elaboration. The index bounds
exclude fallback lookups, and the count equality excludes truncation by `zipWith`. -/
structure Elaborates (raw : Binary.Module) (spec : WebAssembly.module) : Prop where
  module_eq : spec = moduleOf raw
  imports : ∀ entry ∈ raw.imports, ∀ idx, entry.desc = .Func idx → idx.val < raw.types.length
  functions : ∀ idx ∈ raw.functions, idx.val < raw.types.length
  code_count : raw.functions.length = raw.codes.length

/-- The module-level conditions that `Module_ok` does not express: unique export names and
at most one memory.
Instruction syntax itself is restricted by `Binary`. -/
structure ModuleConditions (raw : Binary.Module) : Prop where
  unique_exports : (raw.exports.map (fun entry => Binary.nameOfBytes entry.name)).Nodup
  memory_count : (Module.Translation.mems (raw.imports.map (fun entry => importType raw.types entry.desc))).length +
    raw.memories.length ≤ 1

/-- The explicit restrictions that supplement the generated 2.0 judgment. Neither
these conditions nor elaboration mention validator calls. -/
structure Restrictions (raw : Binary.Module) : Prop
    extends ModuleConditions raw where
  declared : Spec.DeclaredReferences.Module (moduleOf raw)

end Itasca.Module.Elaboration

end ModuleElaboration

section ModuleMetadata

/-!
## Returned metadata and external types

External-type translation and returned-metadata correspondence interpret one
independent raw module. Accessor types and environment/tail caches must describe
that same module, rather than unrelated existential witnesses.
-/

/-!
## External type translation

`externalType` interprets a public import/export type in the generated specification vocabulary.
-/

namespace Itasca.Module.Externals
open Aeneas Aeneas.Std

/-- The SpecTec external type for an extracted external type. -/
def externalType : wasm_types.ExternType → externtype
  | .Func ft => .FUNC (Translation.Environment.funcType ft)
  | .Table tt => .TABLE (Translation.Environment.tableType tt)
  | .Memory mt => .MEM (Translation.Environment.memType mt)
  | .Global gt => .GLOBAL (Translation.globalType gt)

end Itasca.Module.Externals

/-!
## Returned metadata correspondence

`contextOf`, `AccessorTypes` and `Matches` relate the returned environment/tail and import/export accessors to one raw module.
-/

namespace Itasca.Module.Elaboration
open Aeneas Aeneas.Std

/-- The module typing context computed from the independently decoded module. Index spaces list
imports in import order and do not depend on validator caches. -/
def contextOf (raw : Binary.Module) : context :=
  let imports := raw.imports.map (fun e => importType raw.types e.desc)
  ⟨raw.types.map Translation.Environment.funcType,
    Module.Translation.funcs imports ++ raw.functions.map (functionType raw.types),
    Module.Translation.globals imports ++ raw.globals.map (fun g => Translation.globalType g.gtype),
    Module.Translation.tables imports ++ raw.tables.map Translation.Environment.tableType,
    Module.Translation.mems imports ++ raw.memories.map Translation.Environment.memType,
    raw.elements.map (fun entry => Translation.referenceType entry.elem),
    List.replicate raw.data.length .OK, [], [], none⟩

/-- Both type accessors succeed on `env`, and their results match the elaborated module: the import
types are equal, and the exports are typed by `Export_ok` pointwise, which preserves the export
count. -/
def AccessorTypes (env : metadata.ModuleMetadata (alloc.sync.Arc metadata.CodeMetadata)) (raw : Binary.Module) : Prop :=
  ∃ imports exports,
    metadata.ModuleMetadataArcCodeMetadata.import_types env = .ok (.Ok imports) ∧
    metadata.ModuleMetadataArcCodeMetadata.export_types env = .ok (.Ok exports) ∧
    imports.val.map Module.Externals.externalType = raw.imports.map (fun e => importType raw.types e.desc) ∧
    List.Forall₂ (Export_ok (contextOf raw)) (raw.exports.map exportDecl)
      (exports.val.map Module.Externals.externalType)

/-- The retained module describes the same declarations, initializer values and payload
bytes as the independent decoding. Code flags refer to Wasm index-space positions. -/
structure Matches (decoded : metadata.ModuleMetadata (alloc.sync.Arc metadata.CodeMetadata)) (raw : Binary.Module) : Prop where
  types : decoded.code.types.val = raw.types
  imports : decoded.imports.val.map (fun i => (i.module.val, i.name.val, i.kind)) =
    raw.imports.map Module.Environment.importRecord
  exports : decoded.exports.val.map Module.Environment.rawExport = raw.exports
  start : decoded.code.start = raw.start
  elements : decoded.elements.val.map Module.Environment.rawElement = raw.elements
  elementTypes : decoded.code.elem_segment_types.val = raw.elements.map Binary.Element.elem
  dataCount : decoded.code.data_count = raw.dataCount
  data : decoded.data.val.map Module.Data.raw = raw.data
  cache : Module.Environment.Cache decoded.code raw.imports raw.functions raw.globals raw.tables raw.memories
  refs : ∀ x, x ∈ Translation.Environment.declaredReferences decoded.code ↔
    x ∈ Spec.DeclaredReferences.declarations (moduleOf raw)
  eager : ∀ i d, decoded.code.funcs.val[i]? = some d → (d.eager = true ↔
    (∃ idx : U32, idx.val = i ∧ (raw.start = some idx ∨ ∃ e ∈ raw.exports, e.desc = .Func idx)))
  tablesExported : ∀ i d, decoded.code.tables.val[i]? = some d → (d.is_exported = true ↔
    ∃ idx : U32, idx.val = i ∧ ∃ e ∈ raw.exports, e.desc = .Table idx)
  memoriesExported : ∀ i d, decoded.code.memories.val[i]? = some d → (d.is_exported = true ↔
    ∃ idx : U32, idx.val = i ∧ ∃ e ∈ raw.exports, e.desc = .Memory idx)
  globalsExported : ∀ i d, decoded.code.globals.val[i]? = some d → (d.is_exported = true ↔
    ∃ idx : U32, idx.val = i ∧ ∃ e ∈ raw.exports, e.desc = .Global idx)

end Itasca.Module.Elaboration

end ModuleMetadata

section ModuleValidation

/-!
## Accepted modules and completeness limits

`Validated` binds exact bytes, elaboration, typing, restrictions and returned metadata to one raw module; byte and signature bounds are separate completeness premises.
-/

open Aeneas Aeneas.Std
open Itasca.Module.Elaboration

namespace Itasca.Module.Sound

/-- A raw module from the independent grammar that encodes exactly `data` under the
code encoding, elaborates to `moduleOf raw`, matches the returned environment and tail, satisfies
the generated `Module_ok`, meets the module restrictions, and has the types returned by the
public external-type accessors. -/
def Validated (data : Slice U8) (decoded : metadata.ModuleMetadata (alloc.sync.Arc metadata.CodeMetadata)) : Prop :=
  ∃ raw, WebAssembly.Binary.ModuleEncoding (Binary.Source.rawModule raw) (Binary.Source.bytes data.val) ∧
    Elaborates raw (moduleOf raw) ∧ Matches decoded raw ∧
    Module_ok (moduleOf raw) ∧ Restrictions raw ∧ AccessorTypes decoded raw

end Itasca.Module.Sound

namespace Itasca.Binary

/-- Local and byte limits on the same body witness used by the Wasm code entry grammar. -/
def CodeWithinLimits (entry : WebAssembly.Binary.Code) (bs : List UInt8) : Prop :=
  entry.declared.length ≤ limits.MAX_LOCALS.val ∧
    WebAssembly.Binary.CodeEncodingWith (fun ops body =>
      WebAssembly.Binary.BodyBytes ops body ∧ body.length ≤ limits.MAX_FUNCTION_BYTES.val) entry bs

/-- The independent module grammar with the module and code-entry size limits. -/
def ModuleEncodingWithinLimits (raw : Module) (bs : List U8) : Prop :=
  bs.length ≤ limits.MAX_MODULE_BYTES.val ∧
    WebAssembly.Binary.ModuleEncodingWith CodeWithinLimits (Source.rawModule raw) (Source.bytes bs)

/-- Every signature in the type section satisfies `CodeEntry.FuncTypeWithinLimits`. This is an
implementation cap on parameters and results, required for
completeness only. -/
def ModuleSignaturesWithinLimits (raw : Module) : Prop :=
  ∀ ft ∈ raw.types, CodeEntry.FuncTypeWithinLimits ft

end Itasca.Binary

end ModuleValidation
