import Itasca.Runtime.Compiler.Body.Callbacks.Prefix.CompilerPrefixStart
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredLabels
import Itasca.Runtime.Compiler.Local.Relations.Prefix.SuspendedPrefix
import Itasca.Runtime.Compiler.Local.Relations.Prefix.PrefixZipper
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalPrefix
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalDormant
import Itasca.Runtime.Compiler.Local.Lowering.Emission.LoweringEmpty
import Itasca.Runtime.Compiler.Local.Relations.Emission.ScalarEmission
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulLowered

/-!
Sections, each formerly its own module: StructuredLinearEmbedding, StructuredScalarEmbedding, OrdinaryEmbedding.
-/

/-! ## StructuredLinearEmbedding -/

section

/-!
A syntactic inclusion of the existing pure bytecode emission cases.

Main declarations: `LinearEmbedding`. A direct consumer is `Compiler.Body.Control.Embedding.StructuredScalarEmbedding`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- A syntactic inclusion of the existing pure bytecode emission cases. -/
def LinearEmbedding (locals : List valtype)
    (emit : List valtype → instr → List Bytecode → List valtype → Prop) : Prop :=
  ∀ {input instruction code output}, LinearEmission locals input instruction code output → emit input instruction code output

end Itasca.Runtime.Compiler

end

/-! ## StructuredScalarEmbedding -/

section

/-!
A checked inclusion of contextual scalar emissions into a larger compiler certificate; it asserts no execution or compiler-correctness premise.

Main declarations: `ScalarEmbedding`. A direct consumer is `Compiler.Body.Control.Embedding.OrdinaryEmbedding`.
-/

namespace Itasca.Runtime.Compiler

/-- A checked inclusion of contextual scalar emissions into a larger compiler
certificate; it asserts no execution or compiler-correctness premise. -/
class ScalarEmbedding (C : context)
    (emit : List valtype → instr → List Bytecode → List valtype → Prop) : Prop where
  lift : ∀ {input instruction code output}, ScalarEmission C input instruction code output → emit input instruction code output

end Itasca.Runtime.Compiler

end

/-! ## OrdinaryEmbedding -/

section

/-!
Checked syntactic inclusion of the scalar, stateful and indirect-call families, which share the function's immutable index-pair table.

Main declarations: `OrdinaryEmbedding`. A direct consumer is `Compiler.Body.Control.Table.IndexedTablePointControl`.
-/

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end
