import Exec.Interp.Simd.Common.SimdLanes
import Exec.Spec.SimdBitwise
set_option maxRecDepth 4096
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std

def binaryOpcode (op : vvbinop) : U32 :=
  match op with
  | .AND => 78#u32
  | .ANDNOT => 79#u32
  | .OR => 80#u32
  | .XOR => 81#u32

theorem binary_lanes_eq (op : vvbinop) (a b : U128) :
    runtime.interp.simd.bitwise_lanes (binaryOpcode op) a b =
      .ok ⟨Spec.Simd.binary op a.bv b.bv⟩ := by
  cases op <;> unfold runtime.interp.simd.bitwise_lanes binaryOpcode
  all_goals simp only [lift, bind_ok]
  all_goals with_unfolding_all change (Aeneas.Std.bind (Result.ok _) runtime.interp.simd.vector = _)
  all_goals rw [bind_ok]; rfl

@[step] theorem binary_lanes (op : vvbinop) (a b : U128) :
    runtime.interp.simd.bitwise_lanes (binaryOpcode op) a b ⦃ result =>
      result.bv = Spec.Simd.binary op a.bv b.bv ⦄ := by
  rw [binary_lanes_eq]
  simp only [WP.spec_ok]

@[step] theorem select_bits (a b c : U128) :
    runtime.interp.simd.select_bits a b c ⦃ result =>
      result.bv = (a.bv &&& c.bv) ||| (b.bv &&& ~~~c.bv) ⦄ := by
  simp only [runtime.interp.simd.select_bits, runtime.interp.simd.vector,
    lift, bind_ok, WP.spec_ok, UScalar.bv_and, UScalar.bv_or, UScalar.bv_not]

theorem not_dispatch_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (offset laneIndex : U32) (bits a b c : U128) (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats 77#u32 offset laneIndex bits a b c memory =
      .ok (.Ok (~~~a), memory) := by
  unfold runtime.interp.simd.simd
  with_unfolding_all change (Aeneas.Std.bind (lift (~~~a)) (fun x => Aeneas.Std.bind (runtime.interp.simd.vector x)
      (fun result => Result.ok (core.result.Result.Ok result, memory))) = _)
  rw [lift, bind_ok, runtime.interp.simd.vector, bind_ok]

theorem binary_dispatch_eq {F : Type} (floats : runtime.platform.FloatOps F)
    (op : vvbinop) (offset laneIndex : U32) (bits a b c : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (binaryOpcode op) offset laneIndex bits a b c memory =
      Aeneas.Std.bind (runtime.interp.simd.bitwise_lanes (binaryOpcode op) a b)
        (fun result => Result.ok (core.result.Result.Ok result, memory)) := by
  cases op <;> unfold runtime.interp.simd.simd binaryOpcode <;> with_unfolding_all rfl

@[step] theorem not_dispatch {F : Type} (floats : runtime.platform.FloatOps F)
    (offset laneIndex : U32) (bits a b c : U128) (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats 77#u32 offset laneIndex bits a b c memory
      ⦃ result => ∃ value, result = (.Ok value, memory) ∧ value.bv = ~~~a.bv ⦄ := by
  rw [not_dispatch_eq]
  simp only [WP.spec_ok]
  exact ⟨~~~a, rfl, rfl⟩

@[step] theorem binary_dispatch {F : Type} (floats : runtime.platform.FloatOps F)
    (op : vvbinop) (offset laneIndex : U32) (bits a b c : U128)
    (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats (binaryOpcode op) offset laneIndex bits a b c memory
      ⦃ result => ∃ value, result = (.Ok value, memory) ∧
        value.bv = Spec.Simd.binary op a.bv b.bv ⦄ := by
  rw [binary_dispatch_eq, binary_lanes_eq, bind_ok]
  simp only [WP.spec_ok]
  exact ⟨_, rfl, rfl⟩

@[step] theorem bitselect_dispatch {F : Type} (floats : runtime.platform.FloatOps F)
    (offset laneIndex : U32) (bits a b c : U128) (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats 82#u32 offset laneIndex bits a b c memory
      ⦃ result => ∃ value, result = (.Ok value, memory) ∧
        value.bv = (a.bv &&& c.bv) ||| (b.bv &&& ~~~c.bv) ⦄ := by
  unfold runtime.interp.simd.simd
  with_unfolding_all change
    (Aeneas.Std.bind (runtime.interp.simd.select_bits a b c)
      (fun result => Result.ok (core.result.Result.Ok result, memory))) ⦃ _ ⦄
  step as ⟨value, valueEq⟩
  exact ⟨_, rfl, valueEq⟩

@[step] theorem const_dispatch {F : Type} (floats : runtime.platform.FloatOps F)
    (offset laneIndex : U32) (bits a b c : U128) (memory : Option (Slice U8)) :
    runtime.interp.simd.simd floats 12#u32 offset laneIndex bits a b c memory
      ⦃ result => result = (.Ok bits, memory) ⦄ := by
  unfold runtime.interp.simd.simd
  with_unfolding_all change
    (Aeneas.Std.bind (runtime.interp.simd.vector bits)
      (fun result => Result.ok (core.result.Result.Ok result, memory))) ⦃ _ ⦄
  rw [runtime.interp.simd.vector, bind_ok]
  simp only [WP.spec_ok]

end Exec.Interp.Simd
