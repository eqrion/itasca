import Itasca.Runtime.Compiler.Body.Callbacks.Prefix.CompilerPrefix
import Itasca.Runtime.Compiler.Local.Control.Segments.Structured
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredComposition
import Itasca.Runtime.Compiler.Local.Relations.Prefix.Concatenation
import Itasca.Runtime.Compiler.Local.Relations.Prefix.Extension
import Itasca.Runtime.Compiler.Local.Relations.Prefix.PrefixZipper
import Itasca.Runtime.Compiler.Local.Relations.Prefix.Prefix
import Itasca.Runtime.Compiler.Local.Relations.Prefix.ResolvedPrefix
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalPrefix
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalTerminal
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalDormant
import Itasca.Runtime.Compiler.Local.Lowering.Emission.LoweringEmpty
import Itasca.Runtime.Compiler.Local.Relations.Emission.ScalarEmission

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
