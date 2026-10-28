import Exec.Code.Body.Control.Table.StructuredCompilerPrefixFinish
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca
/-- Completed source-to-bytecode evidence, before the compiler's final
well-formedness check packages the executable function. -/
def StructuredCompiledBody (jumpTables : List U32) (emit : List valtype → instr → List Bytecode → List valtype → Prop) {A : Type} (initial final : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype) (source : List instr) : Prop :=
  ∃ target : U32, CompilerStable initial final ∧ final.frames.val = [] ∧
    StructuredCode emit types functions returns locals final.function.code.val jumpTables
      [functionRootLabel returns final.function target] [] source 0 target.val returns ∧
    (∃ src count, src.val = slots locals ∧ final.function.code.val[target.val]? = some (.Return src count)) ∧
    final.function.code.val.length = target.val + 1 ∧ final.function.code.val.length ≤ U32.max

end Itasca.Runtime.Code
