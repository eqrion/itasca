import Itasca.Runtime.Interp.Simd.Memory.SimdMemoryRange
set_option maxHeartbeats 2000000
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

inductive PlainLoad where
  | full | zero32 | zero64

def PlainLoad.opcode : PlainLoad → U32
  | .full => 0#u32 | .zero32 => 92#u32 | .zero64 => 93#u32

def PlainLoad.bytes : PlainLoad → Usize
  | .full => 16#usize | .zero32 => 4#usize | .zero64 => 8#usize

theorem PlainLoad.small (op : PlainLoad) : op.bytes.val ≤ 16 := by cases op <;> decide

theorem plain_load_unfold (op : PlainLoad) (offset lane : U32) (address value : U128) (memory : Slice U8) :
    runtime.interp.simd.memory_op op.opcode offset lane address value memory = (do
      let result ← runtime.interp.memory.address (UScalar.cast .U32 address) offset op.bytes (Slice.len memory)
      match result with
      | .Err error => .ok (.Err error,memory)
      | .Ok start =>
        let loaded ← runtime.interp.simd.read memory start op.bytes
        .ok (core.result.Result.Ok loaded,memory)) := by
  cases op <;> unfold PlainLoad.opcode PlainLoad.bytes runtime.interp.simd.memory_op
  all_goals simp only [lift, bind_ok]
  all_goals with_unfolding_all change
    (do
      let result ← runtime.interp.memory.address (UScalar.cast .U32 address) offset _ (Slice.len memory)
      let cf ← core.result.Result.Insts.CoreOpsTry.branch result
      match cf with
      | core.ops.control_flow.ControlFlow.Continue start => do
        let loaded ← runtime.interp.simd.read memory start _
        .ok (core.result.Result.Ok loaded,memory)
      | core.ops.control_flow.ControlFlow.Break residual => do
        let error ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          U128 (core.convert.FromSame runtime.ExecError) residual
        .ok (error,memory)) = _
  all_goals congr 1; funext result; cases result <;>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, core.convert.FromSame.from, bind_ok]
  all_goals with_unfolding_all rfl

def PlainLoadEffect (op : PlainLoad) (offset : U32) (address : U128) (memory : Slice U8)
    (out : core.result.Result U128 runtime.ExecError × Slice U8) : Prop :=
  if (UScalar.cast .U32 address).val + offset.val + op.bytes.val ≤ memory.length then
    out = (.Ok (vectorLoadBytes memory.val ((UScalar.cast .U32 address).val + offset.val)
      0#u128 0 op.bytes.val),memory)
  else out = (.Err (.Trap .MemoryOutOfBounds),memory)

@[step] theorem plain_load_effect (op : PlainLoad) (offset lane : U32) (address value : U128) (memory : Slice U8) :
    runtime.interp.simd.memory_op op.opcode offset lane address value memory
      ⦃ PlainLoadEffect op offset address memory ⦄ := by
  rw [plain_load_unfold]
  step with memory_range memory (UScalar.cast .U32 address) offset op.bytes op.small as ⟨result,effect⟩
  by_cases fits : (UScalar.cast .U32 address).val + offset.val + op.bytes.val ≤ memory.length
  · simp only [MemoryAddressEffect,Slice.len_val,fits,if_true] at effect
    obtain ⟨start,rfl,startEq⟩ := effect
    unfold runtime.interp.simd.read
    step with read_loop_effect memory op.bytes start 0#u128 0#usize op.small
      (by omega) (by simp) as ⟨word,wordEq⟩
    simpa [PlainLoadEffect,fits,wordEq,startEq]
  · simp only [MemoryAddressEffect,Slice.len_val,fits,if_false] at effect
    simp only [effect,WP.spec_ok,PlainLoadEffect,if_neg fits]
end Itasca.Runtime.Interp.Simd
