import Exec.Code.Local.Relations.Common.StatefulEmission
import Exec.Code.Body.Control.Common.StructuredCoreEmbedding
namespace Exec.Code

/-- Checked inclusion of scalar float emissions in a cumulative instruction
family. This is syntactic inclusion, with no compiler correctness premise. -/
class FloatEmbedding (C : context)
    (emit : List valtype → instr → List Bytecode → List valtype → Prop) : Prop where
  lift : ∀ {input instruction code output}, FloatCoreEmission C input instruction code output →
    emit input instruction code output

instance (C : context) : FloatEmbedding C (FloatCoreEmission C) := ⟨fun h => h⟩
instance (C : context) (pairs) : FloatEmbedding C (CumulativeEmission pairs C) := ⟨fun h => .left h⟩
instance (C : context) (pairs) : CoreEmbedding C (CumulativeEmission pairs C) := ⟨fun h => .left (.core h)⟩
end Exec.Code
