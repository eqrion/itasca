import Itasca.Wasm2.Simd.MemoryReaders
import Itasca.Binary.Wasm1.MemoryInversion

open Aeneas Aeneas.Std

namespace Itasca.MultiValue.Simd

theorem MemoryOperation.conditions (op : MemoryOperation) (C : context)
    (arg : code.MemArg) (lane : U8) (ins outs : List valtype)
    (ht : Instr_ok C (op.instruction (MemoryMeaning.memArg arg) (.mk_uN lane.val))
      (.mk_functype (.mk_list ins) (.mk_list outs))) :
    0 < C.MEMS.length ∧ arg.align.val ≤ op.naturalAlign ∧
      (op.laneCount ≠ 0 → lane.val < op.laneCount) := by
  have hp : 0 < C.MEMS.length ∧
      (2 : Rat) ^ arg.align.val ≤ 2 ^ op.naturalAlign ∧
      (op.laneCount ≠ 0 → lane.val < op.laneCount) := by
    cases op <;> simp only [instruction] at ht <;> cases ht
    all_goals refine ⟨by assumption, ?_, ?_⟩
    all_goals norm_num [naturalAlign, laneCount, MemoryMeaning.memArg, proj_uN_0, size] at *
    all_goals norm_cast at *
    all_goals assumption
  exact ⟨hp.1, (pow_le_pow_iff_right₀ (a := (2 : Rat)) (by norm_num)).mp hp.2.1, hp.2.2⟩

theorem MemoryOperation.typed_runtime (op : MemoryOperation) (C : context)
    (env : module.Env) (ctx : code.Context) (hC : wf_context C)
    (hm : EnvTranslation.Matches env ctx C) (arg : code.MemArg) (lane : U8)
    (hmem : 0 < env.mem_types.val.length) (ha : arg.align.val ≤ op.naturalAlign)
    (hl : op.laneCount ≠ 0 → lane.val < op.laneCount) :
    Instr_ok C (op.instruction (MemoryMeaning.memArg arg) (.mk_uN lane.val))
      (.mk_functype (.mk_list op.inputs) (.mk_list op.outputs)) := by
  have hlen : 0 < C.MEMS.length := by simpa [hm.mems] using hmem
  apply op.typed C (MemoryMeaning.memArg arg) (.mk_uN lane.val) C.MEMS[0]!
    hlen rfl hC ?_ (MemoryMeaning.memArg_wf arg) (by constructor; scalar_tac)
    (MemoryMeaning.alignment_mono _ _ ha) hl
  rw [hm.mems]
  cases he : env.mem_types.val with
  | nil => simp [he] at hmem
  | cons mt rest => simpa [he] using EnvTranslation.memType_wf mt

end Itasca.MultiValue.Simd
