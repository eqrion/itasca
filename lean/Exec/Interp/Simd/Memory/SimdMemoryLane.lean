import Exec.Interp.Simd.Memory.SimdMemoryRange
import Exec.Interp.Simd.Common.SimdShift
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std
set_option maxHeartbeats 2000000

def memoryLaneOpcode (ty : Jnn) (store : Bool) : U32 :=
  match ty,store with
  | .I8,false => 84#u32 | .I16,false => 85#u32 | .I32,false => 86#u32 | .I64,false => 87#u32
  | .I8,true => 88#u32 | .I16,true => 89#u32 | .I32,true => 90#u32 | .I64,true => 91#u32

def memoryLaneBytes : Jnn → Usize
  | .I8 => UScalar.cast .Usize 1#u32 | .I16 => UScalar.cast .Usize 2#u32
  | .I32 => UScalar.cast .Usize 4#u32 | .I64 => UScalar.cast .Usize 8#u32

theorem memoryLaneBytes_small (ty : Jnn) : (memoryLaneBytes ty).val ≤ 16 := by cases ty <;> simp [memoryLaneBytes]

theorem memory_lane_unfold (ty : Jnn) (store : Bool) (offset index : U32) (address value : U128) (memory : Slice U8) :
    runtime.interp.simd.memory_op (memoryLaneOpcode ty store) offset index address value memory = (do
      if index.val ≥ 128/(shiftWidth ty).val then .ok (.Err runtime.ExecError.BadArguments,memory)
      else
        let result ← runtime.interp.simd.range memory (UScalar.cast .U32 address) offset (memoryLaneBytes ty)
        match result with
        | .Err error => .ok (.Err error,memory)
        | .Ok start =>
          if store then
            let word ← runtime.interp.simd.lane value (shiftWidth ty) index
            let updated ← runtime.interp.simd.write memory start (memoryLaneBytes ty) (UScalar.cast .U128 word)
            .ok (.Ok 0#u128,updated)
          else
            let word ← runtime.interp.simd.read memory start (memoryLaneBytes ty)
            let updated ← runtime.interp.simd.put value (shiftWidth ty) index (UScalar.cast .U64 word)
            .ok (.Ok updated,memory)) := by
  cases ty <;> cases store
  all_goals dsimp only [memoryLaneOpcode,memoryLaneBytes,shiftWidth]
  all_goals unfold runtime.interp.simd.memory_op
  all_goals repeat (with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) = _;rw [bind_ok])
  all_goals first
    | with_unfolding_all change (if index.val ≥ 16 then (_ : Result (core.result.Result U128 runtime.ExecError × Slice U8)) else _) = (if index.val ≥ 16 then _ else _)
    | with_unfolding_all change (if index.val ≥ 8 then (_ : Result (core.result.Result U128 runtime.ExecError × Slice U8)) else _) = (if index.val ≥ 8 then _ else _)
    | with_unfolding_all change (if index.val ≥ 4 then (_ : Result (core.result.Result U128 runtime.ExecError × Slice U8)) else _) = (if index.val ≥ 4 then _ else _)
    | with_unfolding_all change (if index.val ≥ 2 then (_ : Result (core.result.Result U128 runtime.ExecError × Slice U8)) else _) = (if index.val ≥ 2 then _ else _)
  all_goals split <;> try rfl
  all_goals repeat (with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) = _;rw [bind_ok])
  all_goals congr 1
  all_goals try (with_unfolding_all rfl)
  all_goals try (solve | congr 1; scalar_tac)
  all_goals funext result;cases result <;>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame,core.convert.FromSame.from,lift,bind_ok]
  all_goals try (solve | congr 1; scalar_tac)
  all_goals with_unfolding_all rfl
end Exec.Interp.Simd
