import Itasca.Runtime.Compiler.Local.Control.Table.StructuredFunction
import Itasca.Runtime.Compiler.Local.Relations.Function.CoreFunction
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerTables

/-!
Contextual function syntax with the actual retained jump table. The certificate contains source/layout evidence, never an execution premise.

Main declarations: `IndexedFunctionCode` and `DefinedIndexedFunctionCode`. A direct consumer is `Compiler.Body.Relations.Executable.ExecutableFunction`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas.Std

/-- Contextual function syntax with the actual retained jump table. The
certificate contains source/layout evidence, never an execution premise. -/
def IndexedFunctionCode
    (emission : CompilerTables → context → List valtype → instr → List Bytecode → List valtype → Prop)
    (C : context) (params declared results : List valtype) (body : List instr)
    (compiled : runtime.bytecode.CompiledFunction) (epilogue : U32) : Prop :=
  C.LOCALS=params++declared ∧
  StructuredFunctionCode (emission (CompilerTables.ofFunction compiled) C)
    C.TYPES C.FUNCS params declared results body compiled epilogue

def DefinedIndexedFunctionCode
    (emission : CompilerTables → context → List valtype → instr → List Bytecode → List valtype → Prop)
    (env : Itasca.metadata.Env) (typeIndex : U32) (source : funccode)
    (compiled : runtime.bytecode.CompiledFunction) : Prop :=
  compiled.type_index=typeIndex ∧ ∃ signature declared body epilogue,
    env.types.val[typeIndex.val]?=some signature ∧
    source=.FUNC (.mk_uN typeIndex.val) (declared.map local.LOCAL) body ∧
    IndexedFunctionCode emission (sourceFunctionContext env
      (signature.params.val.map Itasca.Translate.valueType++declared)
      (signature.results.val.map Itasca.Translate.valueType))
      (signature.params.val.map Itasca.Translate.valueType) declared
      (signature.results.val.map Itasca.Translate.valueType) body compiled epilogue
end Itasca.Runtime.Compiler
