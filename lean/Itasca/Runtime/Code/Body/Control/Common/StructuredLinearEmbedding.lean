import Itasca.Runtime.Code.Body.Callbacks.Common.CompilerPrefix
import Itasca.Runtime.Code.Local.Control.Common.Structured
import Itasca.Runtime.Code.Local.Control.Common.StructuredComposition
import Itasca.Runtime.Code.Local.Relations.Common.Concatenation
import Itasca.Runtime.Code.Local.Relations.Common.Extension
import Itasca.Runtime.Code.Local.Relations.Common.PrefixZipper
import Itasca.Runtime.Code.Local.Relations.Common.Prefix
import Itasca.Runtime.Code.Local.Relations.Common.ResolvedPrefix
import Itasca.Runtime.Code.Local.Control.Common.UniversalPrefix
import Itasca.Runtime.Code.Local.Control.Common.UniversalTerminal
import Itasca.Runtime.Code.Local.Control.Common.UniversalDormant
import Itasca.Runtime.Code.Local.Lowering.Common.LoweringEmpty
import Itasca.Runtime.Code.Local.Relations.Common.ScalarEmission
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- A syntactic inclusion of the existing pure bytecode emission cases. -/
def LinearEmbedding (locals : List valtype)
    (emit : List valtype → instr → List Bytecode → List valtype → Prop) : Prop :=
  ∀ {input instruction code output}, LinearEmission locals input instruction code output → emit input instruction code output

end Itasca.Runtime.Code
