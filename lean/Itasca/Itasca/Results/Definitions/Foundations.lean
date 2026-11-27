import Aeneas
import ItascaRust.Types
import WebAssembly

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
def elementTypes (env : metadata.Env) : List elemtype :=
  env.elements.val.map (fun entry => Translation.referenceType entry.elem)

/-- The data segment types of `env`, one `OK` per declared data segment. -/
def dataTypes (env : metadata.Env) : List datatype :=
  List.replicate ((env.data_count.map (fun count => count.val)).getD 0) .OK

/-- The SpecTec context for a function body, with no labels. Function types come from the
environment's resolved function-type cache; its coherence with the module's type indices is a
separate module invariant. -/
def context (env : metadata.Env) (ctx : code.Context) : _root_.context :=
  { TYPES := env.types.val.map funcType
    FUNCS := env.func_types.val.map funcType
    GLOBALS := env.global_types.val.map Translation.globalType
    TABLES := env.table_types.val.map tableType
    MEMS := env.mem_types.val.map memType
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
