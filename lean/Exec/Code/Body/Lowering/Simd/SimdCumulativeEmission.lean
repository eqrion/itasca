import Exec.Code.Local.Relations.Common.StatefulEmissionTransport
import Exec.Code.Body.Lowering.Float.FloatEmbedding
import Exec.Code.Local.Control.Simd.StructuredSimdEmbedding
import Exec.Code.Local.Callbacks.Table.CompilerTables
namespace Exec.Code
open Aeneas.Std

/-- Cumulative ordinary emissions retain the complete function-local table
state. Structural code and saved-frame relations use this common parameter. -/
abbrev SimdCumulativeEmission (tables : CompilerTables) :=
  EmissionUnion (CumulativeEmission tables.indirect) (SimdEmission tables.simd tables.constants)

instance (tables C) : FloatEmbedding C (SimdCumulativeEmission tables C) :=
  ⟨fun head => .left (.left head)⟩
instance (tables C) : CoreEmbedding C (SimdCumulativeEmission tables C) :=
  ⟨fun head => .left (.left (.core head))⟩
instance (tables C) : SimdEmbedding tables.simd tables.constants C (SimdCumulativeEmission tables C) :=
  ⟨fun head => .right head⟩

theorem CumulativeEmission.append_pairs {pairs C before source emitted after}
    (head : CumulativeEmission pairs C before source emitted after) (extra : List (U32 × U32)) :
    CumulativeEmission (pairs ++ extra) C before source emitted after := by
  have preserve : ∀ (index : Nat) (pair : U32 × U32), pairs[index]? = some pair → (pairs ++ extra)[index]? = some pair := by
    intro index pair member
    have bound := (List.getElem?_eq_some_iff.mp member).1
    simpa only [List.getElem?_append,if_pos bound] using member
  cases head with
  | left h => exact .left h
  | right h => exact .right (h.map_pairs preserve)
  | indirect h => exact .indirect (h.map_pairs preserve)

theorem SimdCumulativeEmission.append_tables {tables C before source emitted after}
    (head : SimdCumulativeEmission tables C before source emitted after) (extra : CompilerTables) :
    SimdCumulativeEmission (tables.append extra) C before source emitted after := by
  cases head with
  | left h => exact .left (h.append_pairs extra.indirect)
  | right h => exact .right (h.append_tables extra.simd extra.constants)
end Exec.Code
