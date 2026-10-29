import Itasca.Runtime.Compiler.Body.Control.Embedding.StructuredScalarEmbedding
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulEmission

/-!
Checked syntactic inclusion of the scalar, stateful and indirect-call families, which share the function's immutable index-pair table.

Main declarations: `OrdinaryEmbedding`. A direct consumer is `Compiler.Body.Control.Table.IndexedTablePointControl`.
-/

namespace Itasca.Runtime.Code
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

end Itasca.Runtime.Code
