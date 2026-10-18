import Exec.Code.Local.Control.Table.StructuredFunctionWithTables
import Exec.Code.Local.Relations.Common.CoreFunction
import Exec.Code.Local.Callbacks.Table.CompilerTables
namespace Exec.Code
open Aeneas.Std

/-- Contextual function syntax with the actual retained jump table. The
certificate contains source/layout evidence, never an execution premise. -/
def IndexedFunctionCode
    (emission : CompilerTables → context → List valtype → instr → List Bytecode → List valtype → Prop)
    (C : context) (params declared results : List valtype) (body : List instr)
    (compiled : runtime.bytecode.CompiledFunction) (epilogue : U32) : Prop :=
  C.LOCALS=params++declared ∧
  StructuredFunctionCodeWithTables (emission (CompilerTables.ofFunction compiled) C)
    C.TYPES C.FUNCS params declared results body compiled epilogue

theorem IndexedFunctionCode.entry {emission C params declared results body compiled epilogue}
    (certificate : IndexedFunctionCode emission C params declared results body compiled epilogue) :
    StructuredCodeWithTables.Point (emission (CompilerTables.ofFunction compiled) C) C.TYPES C.FUNCS results C.LOCALS
      compiled.code.val compiled.jump_tables.val [functionRootLabel results compiled epilogue]
      [] body 0 epilogue.val results := by
  simpa only [certificate.1] using certificate.2.entry

def DefinedIndexedFunctionCode
    (emission : CompilerTables → context → List valtype → instr → List Bytecode → List valtype → Prop)
    (env : Itasca.module.Env) (typeIndex : U32) (source : funccode)
    (compiled : runtime.bytecode.CompiledFunction) : Prop :=
  compiled.type_index=typeIndex ∧ ∃ signature declared body epilogue,
    env.types.val[typeIndex.val]?=some signature ∧
    source=.FUNC (.mk_uN typeIndex.val) (declared.map local.LOCAL) body ∧
    IndexedFunctionCode emission (sourceFunctionContext env
      (signature.params.val.map Itasca.Translate.valueType++declared)
      (signature.results.val.map Itasca.Translate.valueType))
      (signature.params.val.map Itasca.Translate.valueType) declared
      (signature.results.val.map Itasca.Translate.valueType) body compiled epilogue
end Exec.Code
