import Exec.Code.Local.Relations.Common.CoreFunction
import Exec.Code.Body.Lowering.Simd.SimdCumulativeEmission
namespace Exec.Code
open Aeneas.Std

/-- Contextual compiled-code evidence retains the module lookup context used
by global and memory instructions, as well as the function's exact locals. -/
def TableFunctionCode (emission : CompilerTables → context → List valtype → instr → List Bytecode → List valtype → Prop) (C : context) (params declared results : List valtype)
    (body : List instr) (compiled : runtime.bytecode.CompiledFunction) (epilogue : U32) : Prop :=
  C.LOCALS = params ++ declared ∧
  StructuredFunctionCode (emission (CompilerTables.ofFunction compiled) C) C.TYPES C.FUNCS params declared results body compiled epilogue

theorem TableFunctionCode.entry {emission C params declared results body compiled epilogue}
    (certificate : TableFunctionCode emission C params declared results body compiled epilogue) :
    StructuredCode.Point (emission (CompilerTables.ofFunction compiled) C) C.TYPES C.FUNCS results C.LOCALS compiled.code.val
      [functionRootLabel results compiled epilogue] [] body 0 epilogue.val results := by
  simpa only [certificate.1] using certificate.2.entry

def DefinedTableFunctionCode (emission : CompilerTables → context → List valtype → instr → List Bytecode → List valtype → Prop) (env : Itasca.module.Env) (typeIndex : U32)
    (source : funccode) (compiled : runtime.bytecode.CompiledFunction) : Prop :=
  compiled.type_index = typeIndex ∧
    ∃ signature declared body epilogue,
      env.types.val[typeIndex.val]? = some signature ∧
      source = .FUNC (.mk_uN typeIndex.val) (declared.map local.LOCAL) body ∧
      TableFunctionCode emission (sourceFunctionContext env
        (signature.params.val.map Itasca.Translate.valueType ++ declared)
        (signature.results.val.map Itasca.Translate.valueType))
        (signature.params.val.map Itasca.Translate.valueType) declared
        (signature.results.val.map Itasca.Translate.valueType) body compiled epilogue
end Exec.Code
