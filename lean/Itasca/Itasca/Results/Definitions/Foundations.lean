import Aeneas
import ItascaRust.Types
import WebAssembly

open WebAssembly

/-!
# Shared representation conventions

Translation gives the precise correspondence between extracted Rust metadata and SpecTec
values. RustResult distinguishes Rust success/error from the outer Aeneas computation.
Keeping these small conventions below the semantic subjects lets every public contract use
the same meanings without importing execution machinery.

-/

/-! ## RustResult -/

section RustResult

/-!
## Rust result postconditions

`RustResult.Post` names the success and error branches of a returned Rust result.
It is shared by validation and runtime API statements without importing either
implementation. An enclosing Aeneas contract supplies the normal-return or
divergence guarantee separately.
-/

namespace Itasca
open Aeneas.Std

/-- The branch condition for an inner Rust `Result`. This predicate alone says
nothing about the outer Aeneas computation: `.Ok` is Rust success and `.Err` is
an ordinary Rust error. Use named `onSuccess` and `onError` arguments in public
statements so their order is explicit. -/
def RustResult.Post {α ε : Type} (result : core.result.Result α ε)
    (onSuccess : α → Prop) (onError : ε → Prop) : Prop :=
  match result with
  | .Ok value => onSuccess value
  | .Err error => onError error

end Itasca

end RustResult

/-! ## Translation -/

section Translation

/-!
## Translation foundations

Value, signature, environment and block-type translations provide the vocabulary required to elaborate public validation and execution definitions.
-/

open Aeneas Aeneas.Std

namespace Itasca.Translation

/-- The SpecTec value type of a Rust value type. -/
def valueType : wasm_types.ValueType → valtype
  | .I32 => .I32
  | .I64 => .I64
  | .F32 => .F32
  | .F64 => .F64
  | .V128 => .V128
  | .FuncRef => .FUNCREF
  | .ExternRef => .EXTERNREF

/-- The SpecTec reference type of a Rust element type. -/
def referenceType : wasm_types.ElemType → reftype
  | .FuncRef => .FUNCREF
  | .ExternRef => .EXTERNREF

/-- The SpecTec mutability of a Rust mutability. -/
def mutability : wasm_types.Mut → «mut»
  | .Const => none
  | .Var => some .MUT

/-- The SpecTec global type of a Rust global type. -/
def globalType (g : wasm_types.GlobalType) : globaltype :=
  .mk_globaltype (mutability g.mutability) (valueType g.valtype)

end Itasca.Translation

namespace Itasca.Translation.Environment

/-- The SpecTec function type of a Rust function type. -/
def funcType (ft : wasm_types.FuncType) : functype :=
  .mk_functype (.mk_list (ft.params.val.map Translation.valueType))
    (.mk_list (ft.results.val.map Translation.valueType))

/-- The SpecTec limits of Rust limits. -/
def limitsType (lim : wasm_types.Limits) : limits :=
  .mk_limits (.mk_uN lim.min.val) (lim.max.map fun x => .mk_uN x.val)

/-- The SpecTec table type of a Rust table type. -/
def tableType (tt : wasm_types.TableType) : tabletype :=
  .mk_tabletype (limitsType tt.limits) (Translation.referenceType tt.elem)

/-- The SpecTec memory type of a Rust memory type. -/
def memType (mt : wasm_types.MemType) : memtype := .PAGE (limitsType mt.limits)

/-- The element segment types of `env`. -/
def elementTypes (env : metadata.CodeMetadata) : List elemtype :=
  env.elem_segment_types.val.map Translation.referenceType

/-- The data segment types of `env`, one `OK` per declared data segment. -/
def dataTypes (env : metadata.CodeMetadata) : List datatype :=
  List.replicate ((env.data_count.map (fun count => count.val)).getD 0) .OK

/-- The signature selected by a function descriptor. The fallback makes this
translation total for arbitrary extracted values. A decoded module must establish
that every descriptor indexes its type section. -/
def descriptorType (types : List wasm_types.FuncType) (desc : metadata.FuncDesc) : functype :=
  ((types[desc.type_index.val]?).map funcType).getD (.mk_functype (.mk_list []) (.mk_list []))

/-- Function indices for which the descriptor authorizes a body `ref.func`. -/
def declaredReferences (env : metadata.CodeMetadata) : List funcidx :=
  env.funcs.val.zipIdx.filterMap fun (d, i) => if d.can_ref_func then some (.mk_uN i) else none

/-- Type indices in code-entry order, after the function-import prefix. -/
def definedTypeIndices (env : metadata.CodeMetadata) : List U32 :=
  (env.funcs.val.drop env.num_imported_funcs.val).map metadata.FuncDesc.type_index

/-- The SpecTec context for a function body, in Wasm index order. -/
def context (env : metadata.CodeMetadata) (ctx : code.Context) : WebAssembly.context :=
  { TYPES := env.types.val.map funcType
    FUNCS := env.funcs.val.map (descriptorType env.types.val)
    GLOBALS := env.globals.val.map (fun g => Translation.globalType g.gtype)
    TABLES := env.tables.val.map (fun t => tableType t.ty)
    MEMS := env.memories.val.map (fun m => memType m.ty)
    ELEMS := elementTypes env
    DATAS := dataTypes env
    LOCALS := ctx.locals.val.map Translation.valueType
    LABELS := []
    RETURN := some (.mk_list (ctx.results.val.map Translation.valueType)) }

end Itasca.Translation.Environment

namespace Itasca.Body.Control

/-- The context that adds one label with result types `ts`, to be prepended to the outer context. -/
def labelContext (ts : List valtype) : context :=
  ⟨[], [], [], [], [], [], [], [], [.mk_list ts], none⟩

end Itasca.Body.Control

namespace Itasca.Body

/-- The SpecTec block type of a Wasm 2.0 block type, including type-index blocks. -/
def blockType : signature.BlockType → blocktype
  | .Empty => ._RESULT none
  | .Value t => ._RESULT (some (Translation.valueType t))
  | .TypeIndex i => ._IDX (.mk_uN i.val)

end Itasca.Body

end Translation
