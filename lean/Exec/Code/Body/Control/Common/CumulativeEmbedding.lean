import Exec.Code.Body.Lowering.Simd.SimdCumulativeEmission
namespace Exec.Code
open Aeneas.Std

/-- Checked syntactic inclusion of the existing ordinary instruction family. -/
class CumulativeEmbedding (pairs : List (U32 × U32)) (C : context)
    (emit : List valtype → instr → List Bytecode → List valtype → Prop) : Prop where
  lift : ∀ {input instruction code output}, CumulativeEmission pairs C input instruction code output →
    emit input instruction code output

instance (pairs C) : CumulativeEmbedding pairs C (CumulativeEmission pairs C) := ⟨fun head => head⟩
instance (tables C) : CumulativeEmbedding tables.indirect C (SimdCumulativeEmission tables C) :=
  ⟨fun head => .left head⟩

theorem CumulativeEmbedding.append {pairs C emit} (extra : List (U32 × U32))
    [CumulativeEmbedding (pairs ++ extra) C emit] : CumulativeEmbedding pairs C emit :=
  ⟨fun head => CumulativeEmbedding.lift (head.append_pairs extra)⟩

end Exec.Code
