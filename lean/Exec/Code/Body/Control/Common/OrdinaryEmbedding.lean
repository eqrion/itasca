import Exec.Code.Body.Control.Common.StructuredScalarEmbedding
import Exec.Code.Local.Relations.Common.StatefulEmission
namespace Exec.Code
open Aeneas.Std

/-- Checked syntactic inclusion of the scalar, stateful and indirect-call
families, which share the function's immutable index-pair table. -/
class OrdinaryEmbedding (pairs : List (U32 × U32)) (C : context)
    (emit : List valtype → instr → List Bytecode → List valtype → Prop) : Prop where
  scalar : ∀ {input instruction code output}, ScalarEmission C input instruction code output →
    emit input instruction code output
  stateful : ∀ {input instruction code output}, StatefulEmission pairs C input instruction code output →
    emit input instruction code output
  indirect : ∀ {input instruction code output}, IndirectCallEmission pairs C input instruction code output →
    emit input instruction code output

end Exec.Code
