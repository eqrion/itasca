import Itasca.Runtime.Code.Local.Lowering.Simd.SimdSourceSignature
import Itasca.Binary.Wasm2.SimdBitsMeaning
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca.Wasm2.Simd SpecExt

theorem simd_memory_lane_valid (op : MemoryOperation) (C : context) (argument : memarg) (lane : laneidx)
    (ins outs : List valtype)
    (typed : Instr_ok C (op.instruction argument lane) (.mk_functype (.mk_list ins) (.mk_list outs))) :
    op.laneCount ≠ 0 → proj_uN_0 lane < op.laneCount := by
  intro nonzero
  cases op <;> simp only [MemoryOperation.laneCount] at nonzero ⊢
  all_goals first | contradiction | skip
  all_goals simp only [MemoryOperation.instruction] at typed
  all_goals cases typed
  all_goals norm_num at *
  all_goals omega

end Itasca.Runtime.Code
