import Exec.Code.Local.Lowering.Simd.SimdMeaningCounts
import Mathlib.Tactic.IntervalCases

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std
set_option maxRecDepth 4096
set_option maxHeartbeats 8000000

/-- Independent source opcode meaning excludes every reserved constructor
case. This covers all nonconstant SIMD families, without assuming construction
or successful compilation. -/
theorem SimdImmediateMeaning.constructor_available {C opcode immediate input source output}
    (meaning : SimdImmediateMeaning C opcode immediate input source output)
    (bounded : opcode.val < 256) (dst operand entry : U32) :
    ∃ instruction, runtime.bytecode.Instr.make_simd opcode dst operand entry = .ok (some instruction) := by
  rcases opcode with ⟨⟨number,numberBound⟩⟩
  change number < 256 at bounded
  interval_cases number <;> first
    | exact ⟨_,rfl⟩
    | (cases meaning with
      | pure _ _ _ decoded => change none = some _ at decoded; contradiction
      | lane _ _ _ decoded _ _ => change none = some _ at decoded; contradiction
      | memory _ _ _ decoded _ _ _ _ _ _ => change none = some _ at decoded; contradiction)

end Itasca.Runtime.Code
