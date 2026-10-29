import Itasca.Runtime.Compiler.Local.Control.Table.StructuredCodeTableExclusion
import Itasca.Runtime.Compiler.Body.Lowering.Simd.SimdEmissionExclusion
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulEmission
namespace Itasca.Runtime.Compiler
open Aeneas.Std

theorem StatefulEmission.not_branch_table {pairs C before instruction emitted after}
    (h : StatefulEmission pairs C before instruction emitted after) (depths fallback) :
    instruction ≠ .BR_TABLE depths fallback := by
  cases h with
  | instruction stack input output op => cases op <;> simp [SourceMachine.Stateful.Instruction.source]

theorem SimdEmission.not_branch_table {immediates constants C before instruction emitted after}
    (h : SimdEmission immediates constants C before instruction emitted after) (depths fallback) :
    instruction ≠ .BR_TABLE depths fallback := by
  intro same
  have tag := h.allowed.source_tag
  simp only [same,SourceMachine.simdSourceTag] at tag
  contradiction

end Itasca.Runtime.Compiler
