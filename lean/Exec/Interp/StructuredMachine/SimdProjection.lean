import Exec.Interp.StructuredMachine.SimdPoint
import Exec.Code.Body.Lowering.Simd.SimdEmissionExclusion
namespace Exec.Interp.StructuredMachine

/-- An emitted SIMD head retains the current function's exact SIMD and constant tables. -/
class SimdProjection (emission : ContextEmission)
    (simd : List runtime.bytecode.SimdImmediate) (constants : List Aeneas.Std.U128) : Prop where
  project : ∀ {C before source emitted after}, Abs.SimdInstr source →
    emission C before source emitted after → Code.SimdEmission simd constants C before source emitted after

instance (tables : Code.CompilerTables) :
    SimdProjection (Code.SimdCumulativeEmission tables) tables.simd tables.constants where
  project allowed head := head.simd allowed

end Exec.Interp.StructuredMachine
