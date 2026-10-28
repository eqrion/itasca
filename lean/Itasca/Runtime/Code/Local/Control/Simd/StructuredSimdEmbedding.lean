import Itasca.Runtime.Code.Local.Lowering.Simd.SimdEmission
namespace Itasca.Runtime.Code
open Aeneas.Std

/-- Syntactic inclusion of independently decoded SIMD emissions into a larger
certificate. This contains no execution or callback-correctness assumption. -/
class SimdEmbedding (immediates : List runtime.bytecode.SimdImmediate) (constants : List U128)
    (C : context) (emit : List valtype → instr → List Bytecode → List valtype → Prop) : Prop where
  lift : ∀ {input source code output}, SimdEmission immediates constants C input source code output →
    emit input source code output

end Itasca.Runtime.Code
