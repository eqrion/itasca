import Itasca.Runtime.Compiler.Local.Control.Segments.Structured
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredComposition
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredLabels
import Itasca.Runtime.Compiler.Local.Relations.Layout.LayoutProofs
import Itasca.Support.TypeTranslation
import Itasca.Runtime.Compiler.Local.Relations.Function.Function
import Itasca.Runtime.Compiler.Local.Relations.Emission.ScalarEmission
import Itasca.Support.EnvTranslation

/-!
The source function context is fixed by the independently decoded module metadata and the function's parameter, local and result declarations.

Main declarations: `sourceFunctionContext`. A direct consumer is `Compiler.Local.Relations.Function.CoreFunctionContext`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas.Std

/-- The source function context is fixed by the independently decoded module
metadata and the function's parameter, local and result declarations. -/
def sourceFunctionContext (env : Itasca.metadata.Env) (locals results : List valtype) : context :=
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

theorem source_function_context_reader (env : Itasca.metadata.Env) (ctx : Itasca.code.Context) :
    sourceFunctionContext env (ctx.locals.val.map Itasca.Translate.valueType)
      (ctx.results.val.map Itasca.Translate.valueType) = Itasca.EnvTranslation.context env ctx := rfl

end Itasca.Runtime.Compiler
