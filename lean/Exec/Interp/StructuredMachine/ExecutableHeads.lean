import Exec.Code.Body.Relations.Common.ExecutableProjection
import Exec.Interp.StructuredMachine.SimdCumulativeHeads
import Exec.Interp.StructuredMachine.SimdProjection
import Exec.Interp.StructuredMachine.IndirectProjection
import Exec.Interp.StructuredMachine.TypedSelectHeads
namespace Exec.Interp.StructuredMachine

instance (immediates constants) : OrdinaryHeads (Code.SimdEmission immediates constants) where
  ordinary := by
    intro C before source emitted after head
    have tag := head.allowed.source_tag
    cases source <;> simp_all [ordinarySource,Abs.simdSourceTag]

instance (immediates constants) : ErasedHeads (Code.SimdEmission immediates constants) where
  nop := by
    intro C before after emitted head
    have impossible := head.allowed.source_tag
    cases impossible
  drop := by
    intro C before after emitted head
    have impossible := head.allowed.source_tag
    cases impossible

instance (tables : Code.CompilerTables) : OrdinaryHeads (Code.ExecutableEmission tables) where
  ordinary := by
    intro C before source emitted after head
    cases head with
    | base h => exact OrdinaryHeads.ordinary h
    | typedSelect h => cases h; rfl
    | branchTable => rfl

instance (tables : Code.CompilerTables) : ErasedHeads (Code.ExecutableEmission tables) where
  nop head := ErasedHeads.nop (head.base_inv rfl)
  drop head := ErasedHeads.drop (head.base_inv rfl)

instance (tables : Code.CompilerTables) : FloatHeads (Code.ExecutableEmission tables) where
  project allowed head := FloatHeads.project allowed (head.base_inv allowed.executable_extension_tag)

instance (tables : Code.CompilerTables) : StatefulProjection (Code.ExecutableEmission tables) tables.indirect where
  project := by
    intro C before op emitted after head
    have ordinary : Abs.executableExtensionTag op.source = false := by cases op <;> rfl
    exact StatefulProjection.project (head.base_inv ordinary)

instance (tables : Code.CompilerTables) : IndirectProjection (Code.ExecutableEmission tables) tables.indirect where
  project head := IndirectProjection.project (head.base_inv rfl)

instance (tables : Code.CompilerTables) : SimdProjection (Code.ExecutableEmission tables) tables.simd tables.constants where
  project allowed head := SimdProjection.project allowed (head.base_inv allowed.executable_extension_tag)

instance (tables : Code.CompilerTables) : TypedSelectHeads (Code.ExecutableEmission tables) where
  project head := head.typed_select_inv
end Exec.Interp.StructuredMachine

namespace Exec.Interp.Executable
/-- Each function supplies the exact retained indirect, SIMD, constant and
jump-table metadata for the complete source language. -/
abbrev emission (compiled : runtime.bytecode.CompiledFunction) : StructuredMachine.ContextEmission :=
  Code.ExecutableEmission (Code.CompilerTables.ofFunction compiled)
end Exec.Interp.Executable
