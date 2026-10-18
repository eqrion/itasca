import Exec.Interp.StructuredMachine.ExecutableHeads
import Exec.Interp.StructuredMachine.SupportedHeadCoverage
namespace Exec.Interp.StructuredMachine

/-- Every non-erased head of the complete compiler relation selects a proved
machine branch. Branch-table layout itself is supplied by the indexed point. -/
instance (tables : Code.CompilerTables) : SupportedHeads (Code.ExecutableEmission tables) where
  head := by
    intro C stack source emitted output ready head
    cases head with
    | base h => exact SupportedHeads.head ready h
    | typedSelect h => cases h; exact .typedSelect _
    | branchTable stack depths fallback selector start len => exact .branchTable depths fallback
end Exec.Interp.StructuredMachine
