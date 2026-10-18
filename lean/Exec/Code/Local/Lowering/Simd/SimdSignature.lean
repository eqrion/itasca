import Exec.Code.Local.Lowering.Simd.SimdEmission

namespace Exec.Code
open Aeneas.Std Itasca.Wasm2.Simd

/-- The retained binary meaning has the same principal signature under every
source context in which the instruction is typed. -/
theorem SimdImmediateMeaning.principal {C D opcode immediate input source output ins outs}
    (meaning : SimdImmediateMeaning C opcode immediate input source output)
    (typed : Instr_ok D source (.mk_functype (.mk_list ins) (.mk_list outs))) :
    ins = input ∧ outs = output := by
  cases meaning with
  | pure opcode immediate op meaning => exact op.principal D ins outs typed
  | lane opcode immediate op meaning lane position => exact op.principal D _ ins outs typed
  | memory opcode immediate op meaning argument lane memory available offset position =>
    exact op.principal D argument _ ins outs typed
  | shuffle immediate low high bits => cases typed; exact ⟨rfl,rfl⟩

end Exec.Code
