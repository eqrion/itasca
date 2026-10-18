import Exec.Interp.StructuredMachine.IndirectPoint
import Exec.Code.Local.Control.Calls.CumulativeIndirectInversion
import Exec.Code.Body.Lowering.Simd.SimdEmissionExclusion
import Exec.Interp.Cumulative.Machine
namespace Exec.Interp.StructuredMachine

/-- The current indirect call retains its actual immutable table/type pair. -/
class IndirectProjection (emission : ContextEmission) (pairs : List (Aeneas.Std.U32 × Aeneas.Std.U32)) : Prop where
  project : ∀ {C before table type emitted after},
    emission C before (.CALL_INDIRECT table type) emitted after →
    Code.IndirectCallEmission pairs C before (.CALL_INDIRECT table type) emitted after

instance {pairs} : IndirectProjection (Code.CumulativeEmission pairs) pairs where
  project head := head.indirect_inv

instance (compiled : runtime.bytecode.CompiledFunction) :
    IndirectProjection (Cumulative.emission compiled) compiled.indirect.val := by
  unfold Cumulative.emission
  infer_instance

instance (tables : Code.CompilerTables) :
    IndirectProjection (Code.SimdCumulativeEmission tables) tables.indirect where
  project head := (head.cumulative (.indirect_call _ _)).indirect_inv

end Exec.Interp.StructuredMachine
