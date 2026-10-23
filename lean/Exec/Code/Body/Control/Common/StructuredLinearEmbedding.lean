import Exec.Code.Body.Callbacks.Common.CompilerPrefix
import Exec.Code.Local.Control.Common.Structured
import Exec.Code.Local.Control.Common.StructuredComposition
import Exec.Code.Local.Relations.Common.Concatenation
import Exec.Code.Local.Relations.Common.Extension
import Exec.Code.Local.Relations.Common.PrefixZipper
import Exec.Code.Local.Relations.Common.Prefix
import Exec.Code.Local.Relations.Common.ResolvedPrefix
import Exec.Code.Local.Control.Common.UniversalPrefix
import Exec.Code.Local.Control.Common.UniversalTerminal
import Exec.Code.Local.Control.Common.UniversalDormant
import Exec.Code.Local.Lowering.Common.LoweringEmpty
import Exec.Code.Local.Relations.Common.ScalarEmission
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- A syntactic inclusion of the existing pure bytecode emission cases. -/
def LinearEmbedding (locals : List valtype)
    (emit : List valtype → instr → List Bytecode → List valtype → Prop) : Prop :=
  ∀ {input instruction code output}, LinearEmission locals input instruction code output → emit input instruction code output

end Exec.Code
