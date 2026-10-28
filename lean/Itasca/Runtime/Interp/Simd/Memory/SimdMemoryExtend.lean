import Itasca.Runtime.Interp.Simd.Memory.SimdMemoryExtendLoop
import Itasca.Runtime.Interp.Simd.Integer.SimdWidenSound
import Itasca.Runtime.Interp.Simd.Memory.SimdMemoryRange
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd
set_option maxHeartbeats 200000

def memoryExtendOpcode (ty : WidenWidth) (signed : Bool) : U32 :=
  match ty,signed with
  | .i8,true => 1#u32 | .i8,false => 2#u32
  | .i16,true => 3#u32 | .i16,false => 4#u32
  | .i32,true => 5#u32 | .i32,false => 6#u32

def memoryExtendLoop (ty : WidenWidth) (signed : Bool) : U128 → Result U128 :=
  match ty,signed with
  | .i8,true => fun v => runtime.interp.simd.memory_op_loop84 1#u32 v 8#u32 0#u128 0#u32
  | .i8,false => fun v => runtime.interp.simd.memory_op_loop91 2#u32 v 8#u32 0#u128 0#u32
  | .i16,true => fun v => runtime.interp.simd.memory_op_loop98 3#u32 v 16#u32 0#u128 0#u32
  | .i16,false => fun v => runtime.interp.simd.memory_op_loop105 4#u32 v 16#u32 0#u128 0#u32
  | .i32,true => fun v => runtime.interp.simd.memory_op_loop112 5#u32 v 32#u32 0#u128 0#u32
  | .i32,false => fun v => runtime.interp.simd.memory_op_loop119 6#u32 v 32#u32 0#u128 0#u32

theorem memory_extend_unfold (ty : WidenWidth) (signed : Bool)
    (offset lane : U32) (address value : U128) (memory : Slice U8) :
    runtime.interp.simd.memory_op (memoryExtendOpcode ty signed) offset lane address value memory = (do
      let result ← runtime.interp.memory.address (UScalar.cast .U32 address) offset 8#usize (Slice.len memory)
      match result with
      | .Err error => .ok (.Err error,memory)
      | .Ok start =>
        let loaded ← runtime.interp.simd.read memory start 8#usize
        let answer ← memoryExtendLoop ty signed loaded
        .ok (core.result.Result.Ok answer,memory)) := by
  cases ty <;> cases signed
  all_goals dsimp only [memoryExtendOpcode,memoryExtendLoop]
  all_goals unfold runtime.interp.simd.memory_op
  all_goals with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) = _
  all_goals rw [bind_ok]
  all_goals rw [if_neg (by decide),if_neg (by decide)]
  all_goals simp only [lift,bind_ok]
  all_goals split <;> try contradiction
  all_goals congr 1
  all_goals funext result;cases result <;>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame,core.convert.FromSame.from]
  all_goals try (with_unfolding_all change (Aeneas.Std.bind (Aeneas.Std.bind (Result.ok _) _) _) = _;rw [bind_ok,bind_ok])
  all_goals try (with_unfolding_all rfl)
  all_goals congr 1
  all_goals funext loaded
  all_goals split <;> try contradiction
  all_goals repeat (with_unfolding_all change (Aeneas.Std.bind (Result.ok _) _) = _;rw [bind_ok])
  all_goals with_unfolding_all rfl
theorem memoryExtendLoop_eq (ty : WidenWidth) (signed : Bool) (value : U128) :
    memoryExtendLoop ty signed value =
      runtime.interp.simd.memory_op_loop0 (memoryExtendOpcode ty signed) value (widenWidth ty) 0#u128 0#u32 := by
  cases ty <;> cases signed <;> with_unfolding_all rfl

end Itasca.Runtime.Interp.Simd
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd

@[step] theorem memory_extend_lanes (ty : WidenWidth) (signed : Bool) (value : U128) :
    runtime.interp.simd.memory_op_loop0 (memoryExtendOpcode ty signed) value (widenWidth ty) 0#u128 0#u32
      ⦃ answer => uN.mk_uN answer.val = widenResult ty false false signed value.bv value.bv ⦄ := by
  have parity : ((memoryExtendOpcode ty signed).val % 2 = 1) = (signed = true) := by cases ty <;> cases signed <;> decide
  have loopLaw := memory_extend_loop (memoryExtendOpcode ty signed) (widenWidth ty) 0#u32 value 0#u128
    (by cases ty <;> decide) (by cases ty <;> decide)
    (fun j bits => bits = extendBits signed ((widenWidth ty).val*2) (laneBits (widenWidth ty).val j value.bv))
    (by
      intro j valid a aEq
      simp only [parity]
      exact widen_input (widenWidth ty) signed a _ (by cases ty <;> decide) (by cases ty <;> decide) aEq)
    (by simp) (by simp)
  apply WP.spec_mono loopLaw
  intro answer lanes
  apply widen_packed ty false false signed value value answer
  intro j valid
  rw [widenWidth_val] at lanes
  have selected := lanes j valid
  simpa only [widenWidth_val,widenBits,Bool.false_eq_true,↓reduceIte,Nat.add_zero] using selected

@[step] theorem memory_extend_effect (ty : WidenWidth) (signed : Bool)
    (offset lane : U32) (address value : U128) (bytes : Slice U8) :
    runtime.interp.simd.memory_op (memoryExtendOpcode ty signed) offset lane address value bytes ⦃ out =>
      if (UScalar.cast .U32 address).val+offset.val+8 ≤ bytes.length then
        ∃ answer, out = (.Ok answer,bytes) ∧ uN.mk_uN answer.val = widenResult ty false false signed
          (vectorLoadBytes bytes.val ((UScalar.cast .U32 address).val+offset.val) 0#u128 0 8).bv
          (vectorLoadBytes bytes.val ((UScalar.cast .U32 address).val+offset.val) 0#u128 0 8).bv
      else out = (.Err (.Trap .MemoryOutOfBounds),bytes) ⦄ := by
  rw [memory_extend_unfold]
  simp only [memoryExtendLoop_eq]
  step with memory_range bytes (UScalar.cast .U32 address) offset 8#usize (by decide) as ⟨result,effect⟩
  by_cases fits : (UScalar.cast .U32 address).val+offset.val+8 ≤ bytes.length
  · simp only [MemoryAddressEffect,Slice.len_val,show (8#usize).val=8 by simp,fits,if_true] at effect
    obtain ⟨start,rfl,startEq⟩ := effect
    unfold runtime.interp.simd.read
    step with read_loop_effect bytes 8#usize start 0#u128 0#usize (by decide) (by scalar_tac) (by simp)
      as ⟨word,wordEq⟩
    step with memory_extend_lanes ty signed word as ⟨answer,packed⟩
    simp only [if_pos fits]
    refine ⟨answer,rfl,?_⟩
    simpa only [wordEq,startEq,show (8#usize).val=8 by simp,show (0#usize).val=0 by simp,Nat.sub_zero] using packed
  · simp only [MemoryAddressEffect,Slice.len_val,show (8#usize).val=8 by simp,fits,if_false] at effect
    simp only [effect,WP.spec_ok,if_neg fits]
end Itasca.Runtime.Interp.Simd
