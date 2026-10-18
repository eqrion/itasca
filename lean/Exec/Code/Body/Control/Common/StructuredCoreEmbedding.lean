import Exec.Code.Body.Control.Common.StructuredLinearEmbedding
namespace Exec.Code

/-- A checked inclusion of contextual scalar emissions into a larger compiler
certificate; it asserts no execution or compiler-correctness premise. -/
class CoreEmbedding (C : context)
    (emit : List valtype → instr → List Bytecode → List valtype → Prop) : Prop where
  lift : ∀ {input instruction code output}, CoreEmission C input instruction code output → emit input instruction code output

instance (C : context) : CoreEmbedding C (CoreEmission C) := ⟨fun h => h⟩

theorem CoreEmbedding.linear {C emit} [CoreEmbedding C emit] : LinearEmbedding C.LOCALS emit :=
  fun h => CoreEmbedding.lift (.pure h)
end Exec.Code
