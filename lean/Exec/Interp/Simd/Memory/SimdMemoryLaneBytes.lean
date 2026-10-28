import Exec.Interp.Simd.Memory.SimdMemoryLaneEffect
import Exec.Interp.Simd.Memory.SimdMemoryLoadSource
import Exec.Interp.Simd.Common.SimdReplacePacking
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std SpecExt SpecExt.Builtins

theorem memoryLaneBytes_val (ty : Jnn) : (memoryLaneBytes ty).val = lsize (lanetype_Jnn ty)/8 := by
  cases ty <;> simp [memoryLaneBytes,lsize,lanetype_Jnn,size,valtype_numtype,psize]

theorem vector_lane_load_bound (ty : Jnn) (bytes : List U8) (start : Nat)
    (inside : start+(memoryLaneBytes ty).val ≤ bytes.length) :
    (vectorLoadBytes bytes start 0#u128 0 (memoryLaneBytes ty).val).val < 2^lsize (lanetype_Jnn ty) := by
  rw [vectorLoadBytes_source _ _ _ (memoryLaneBytes_small ty) inside]
  have valid := memory_bytes_wf ((bytes.drop start).take (memoryLaneBytes ty).val)
  have bounded := Spec.integerOfBytes_bound _ valid
  have lengthEq : (Store.decodeBytes ((bytes.drop start).take (memoryLaneBytes ty).val)).length = (memoryLaneBytes ty).val := by
    simp only [Store.decodeBytes,List.length_map,List.length_take,List.length_drop]
    omega
  rw [lengthEq] at bounded
  have power : 256^(memoryLaneBytes ty).val = 2^lsize (lanetype_Jnn ty) := by
    cases ty <;> simp [memoryLaneBytes,lsize,lanetype_Jnn,size,valtype_numtype,psize]
  rwa [power] at bounded

theorem vector_lane_load_word (ty : Jnn) (bytes : List U8) (start : Nat)
    (inside : start+(memoryLaneBytes ty).val ≤ bytes.length) :
    ((UScalar.cast .U64 (vectorLoadBytes bytes start 0#u128 0 (memoryLaneBytes ty).val)).bv.setWidth
      (lsize (lanetype_Jnn ty))).toNat =
      (vectorLoadBytes bytes start 0#u128 0 (memoryLaneBytes ty).val).val := by
  have bound := vector_lane_load_bound ty bytes start inside
  have width : lsize (lanetype_Jnn ty) ≤ 64 := by cases ty <;> decide
  have bound64 : (vectorLoadBytes bytes start 0#u128 0 (memoryLaneBytes ty).val).val < 2^64 :=
    lt_of_lt_of_le bound (Nat.pow_le_pow_right (by decide) width)
  simp only [BitVec.toNat_setWidth,UScalar.bv_toNat,UScalar.cast_val_eq]
  change ((vectorLoadBytes bytes start 0#u128 0 (memoryLaneBytes ty).val).val % 2^64) % 2^lsize (lanetype_Jnn ty) = _
  rw [Nat.mod_eq_of_lt bound64,Nat.mod_eq_of_lt bound]

theorem vector_lane_load_bytes (ty : Jnn) (bytes : List U8) (start : Nat)
    (inside : start+(memoryLaneBytes ty).val ≤ bytes.length) :
    ibytes_ (lsize (lanetype_Jnn ty)) (.mk_uN
      ((UScalar.cast .U64 (vectorLoadBytes bytes start 0#u128 0 (memoryLaneBytes ty).val)).bv.setWidth
        (lsize (lanetype_Jnn ty))).toNat) =
      ((Store.decodeBytes bytes).drop start).take (lsize (lanetype_Jnn ty)/8) := by
  rw [vector_lane_load_word _ _ _ inside,vectorLoadBytes_source _ _ _ (memoryLaneBytes_small ty) inside]
  have valid := memory_bytes_wf ((bytes.drop start).take (memoryLaneBytes ty).val)
  have exactBytes := Spec.integerBytes_ofBytes _ valid
  have lengthEq : (Store.decodeBytes ((bytes.drop start).take (memoryLaneBytes ty).val)).length = (memoryLaneBytes ty).val := by
    simp only [Store.decodeBytes,List.length_map,List.length_take,List.length_drop]
    omega
  rw [lengthEq,memoryLaneBytes_val] at exactBytes
  simpa only [ibytes_,proj_uN_0,memoryLaneBytes_val,Store.decodeBytes,List.map_take,List.map_drop] using exactBytes
end Itasca.Runtime.Interp.Simd
