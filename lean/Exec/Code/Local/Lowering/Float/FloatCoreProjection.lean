import Exec.Code.Local.Lowering.Float.FloatEmissionInversion
namespace Exec.Code

/-- A non-float source instruction in the extended emission relation retains
exactly its original contextual Core emission evidence. -/
theorem FloatCoreEmission.core_inv {C before instruction emitted after}
    (emission : FloatCoreEmission C before instruction emitted after)
    (nonFloat : Abs.Float.decodeInstruction instruction = none) :
    CoreEmission C before instruction emitted after := by
  cases emission with
  | core h => exact h
  | scalar stack op left right leftSlot rightSlot =>
    rw [Abs.Float.decodeInstruction_source] at nonFloat
    contradiction
end Exec.Code
