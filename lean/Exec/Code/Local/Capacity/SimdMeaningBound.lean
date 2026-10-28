import Exec.Code.Local.Lowering.Simd.SimdMeaningCounts
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca.Wasm2.Simd
set_option maxRecDepth 4096

theorem SimdImmediateMeaning.opcode_bound {C opcode immediate input source output}
    (meaning : SimdImmediateMeaning C opcode immediate input source output) : opcode.val < 256 := by
  cases meaning with
  | pure opcode immediate op meaning => exact pure_bound meaning
  | lane opcode immediate op meaning lane position =>
    unfold laneMeaning at meaning
    split at meaning <;> first | contradiction | omega
  | memory opcode immediate op meaning argument lane memory available offset position =>
    unfold memoryMeaning at meaning
    split at meaning <;> first | contradiction | omega
  | shuffle => decide
end Itasca.Runtime.Code
