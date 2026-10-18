import Exec.Code.Body.Lowering.Simd.SimdEmissionExclusion
import Exec.Interp.StructuredMachine.FloatHeads
import Exec.Interp.StructuredMachine.StatefulProjection
namespace Exec.Interp.StructuredMachine

instance (tables : Code.CompilerTables) : FloatHeads (Code.SimdCumulativeEmission tables) where
  project allowed head := FloatHeads.project allowed (head.cumulative (.core allowed))

instance (tables : Code.CompilerTables) :
    StatefulProjection (Code.SimdCumulativeEmission tables) tables.indirect where
  project := by
    intro C before op emitted after head
    exact StatefulProjection.project (head.cumulative (.stateful op))

end Exec.Interp.StructuredMachine
