import Exec.Code.Local.Lowering.Float.FloatCoreEmission
import Exec.Code.Body.Control.Common.StructuredCoreEmbedding
namespace Exec.Code

instance (C : context) : CoreEmbedding C (FloatCoreEmission C) := ⟨fun h => .core h⟩

theorem FloatCoreEmission.linearEmbedding (C : context) : LinearEmbedding C.LOCALS (FloatCoreEmission C) := by
  intro input instruction code output emission
  exact .core (.pure emission)
end Exec.Code
