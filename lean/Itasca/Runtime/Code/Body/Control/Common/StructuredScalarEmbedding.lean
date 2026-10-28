import Itasca.Runtime.Code.Body.Control.Common.StructuredLinearEmbedding
namespace Itasca.Runtime.Code

/-- A checked inclusion of contextual scalar emissions into a larger compiler
certificate; it asserts no execution or compiler-correctness premise. -/
class ScalarEmbedding (C : context)
    (emit : List valtype → instr → List Bytecode → List valtype → Prop) : Prop where
  lift : ∀ {input instruction code output}, ScalarEmission C input instruction code output → emit input instruction code output

end Itasca.Runtime.Code
