import Exec.Code.Local.Control.Common.StructuredFunction
import Exec.Code.Local.Relations.Common.CoreEmission
import Itasca.Support.EnvTranslation
namespace Exec.Code
open Aeneas.Std

/-- The source function context is fixed by the independently decoded module
metadata and the function's parameter, local and result declarations. -/
def sourceFunctionContext (env : Itasca.module.Env) (locals results : List valtype) : context :=
  { TYPES := env.types.val.map Itasca.EnvTranslation.funcType
    FUNCS := env.func_types.val.map Itasca.EnvTranslation.funcType
    GLOBALS := env.global_types.val.map Itasca.Translate.globalType
    TABLES := env.table_types.val.map Itasca.EnvTranslation.tableType
    MEMS := env.mem_types.val.map Itasca.EnvTranslation.memType
    ELEMS := Itasca.EnvTranslation.elementTypes env
    DATAS := Itasca.EnvTranslation.dataTypes env
    LOCALS := locals
    LABELS := []
    RETURN := some (.mk_list results) }

theorem sourceFunctionContext_reader (env : Itasca.module.Env) (ctx : Itasca.code.Context) :
    sourceFunctionContext env (ctx.locals.val.map Itasca.Translate.valueType)
      (ctx.results.val.map Itasca.Translate.valueType) = Itasca.EnvTranslation.context env ctx := rfl

/-- Contextual compiled-code evidence retains the module lookup context used
by global and memory instructions, as well as the function's exact locals. -/
def CoreFunctionCode (C : context) (params declared results : List valtype)
    (body : List instr) (compiled : runtime.bytecode.CompiledFunction) (epilogue : U32) : Prop :=
  C.LOCALS = params ++ declared ∧
  StructuredFunctionCode (CoreEmission C) C.TYPES C.FUNCS params declared results body compiled epilogue

theorem CoreFunctionCode.entry {C params declared results body compiled epilogue}
    (certificate : CoreFunctionCode C params declared results body compiled epilogue) :
    StructuredCode.Point (CoreEmission C) C.TYPES C.FUNCS results C.LOCALS compiled.code.val
      [functionRootLabel results compiled epilogue] [] body 0 epilogue.val results := by
  simpa only [certificate.1] using certificate.2.entry

def DefinedStructuredFunctionCode
    (emit : List valtype → instr → List Bytecode → List valtype → Prop)
    (env : Itasca.module.Env) (typeIndex : U32) (source : funccode)
    (compiled : runtime.bytecode.CompiledFunction) : Prop :=
  compiled.type_index = typeIndex ∧
    ∃ signature declared body epilogue,
      env.types.val[typeIndex.val]? = some signature ∧
      source = .FUNC (.mk_uN typeIndex.val) (declared.map local.LOCAL) body ∧
      StructuredFunctionCode emit (env.types.val.map Itasca.EnvTranslation.funcType)
        (env.func_types.val.map Itasca.EnvTranslation.funcType)
        (signature.params.val.map Itasca.Translate.valueType) declared
        (signature.results.val.map Itasca.Translate.valueType) body compiled epilogue

def DefinedCoreFunctionCode (env : Itasca.module.Env) (typeIndex : U32)
    (source : funccode) (compiled : runtime.bytecode.CompiledFunction) : Prop :=
  compiled.type_index = typeIndex ∧
    ∃ signature declared body epilogue,
      env.types.val[typeIndex.val]? = some signature ∧
      source = .FUNC (.mk_uN typeIndex.val) (declared.map local.LOCAL) body ∧
      CoreFunctionCode (sourceFunctionContext env
        (signature.params.val.map Itasca.Translate.valueType ++ declared)
        (signature.results.val.map Itasca.Translate.valueType))
        (signature.params.val.map Itasca.Translate.valueType) declared
        (signature.results.val.map Itasca.Translate.valueType) body compiled epilogue
end Exec.Code
