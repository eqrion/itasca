import Exec.Code.Local.Lowering.Simd.SimdEmission
namespace Exec.Code
open Aeneas.Std

/-- Syntactic inclusion of independently decoded SIMD emissions into a larger
certificate. This contains no execution or callback-correctness assumption. -/
class SimdEmbedding (immediates : List runtime.bytecode.SimdImmediate) (constants : List U128)
    (C : context) (emit : List valtype → instr → List Bytecode → List valtype → Prop) : Prop where
  lift : ∀ {input source code output}, SimdEmission immediates constants C input source code output →
    emit input source code output

instance (immediates constants C) : SimdEmbedding immediates constants C (SimdEmission immediates constants C) :=
  ⟨fun h => h⟩

theorem SimdEmbedding.append_tables (immediates constants extraImmediates extraConstants C) :
    SimdEmbedding immediates constants C (SimdEmission (immediates ++ extraImmediates) (constants ++ extraConstants) C) :=
  ⟨fun h => h.append_tables extraImmediates extraConstants⟩
end Exec.Code
