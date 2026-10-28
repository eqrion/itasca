import Itasca.Runtime.Interp.Simd.Memory.SimdMemoryLaneBytes
import Itasca.Runtime.Spec.SimdMemoryChunks
import Itasca.Runtime.Spec.SimdWidenLists
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std SpecExt SpecExt.Builtins Itasca.Runtime.Spec.Simd

theorem vector_extend_load_bytes (ty : WidenWidth) (bytes : List U8) (start j : Nat)
    (inside : start+8 ≤ bytes.length) (lane : j < ty.count) :
    ibytes_ ty.width (.mk_uN (laneWord (lanetype_Jnn ty.input)
      (vectorLoadBytes bytes start 0#u128 0 8).bv j).toNat) =
      ((Store.decodeBytes bytes).drop (start+j*(ty.width/8))).take (ty.width/8) := by
  have payload : integerBytes 8 (vectorLoadBytes bytes start 0#u128 0 8).val =
      ((Store.decodeBytes bytes).drop start).take 8 := by
    rw [vectorLoadBytes_source _ _ _ (by decide) inside]
    have roundtrip := Spec.integerBytes_ofBytes (Store.decodeBytes ((bytes.drop start).take 8))
      (memory_bytes_wf _)
    have len : (Store.decodeBytes ((bytes.drop start).take 8)).length = 8 := by
      simp only [Store.decodeBytes,List.length_map,List.length_take,List.length_drop];omega
    rw [len] at roundtrip
    simpa only [Store.decodeBytes,List.map_take,List.map_drop] using roundtrip
  have fit : j*(ty.width/8)+ty.width/8 ≤ 8 := by
    cases ty <;> norm_num [WidenWidth.width,WidenWidth.input,WidenWidth.count,lsize,lanetype_Jnn,size,valtype_numtype,psize] at * <;> omega
  have chunk := integerBytes_chunk (ty.width/8) j (vectorLoadBytes bytes start 0#u128 0 8).val fit
  rw [payload] at chunk
  have pow : 256^(ty.width/8) = 2^ty.width := by cases ty <;> decide
  have offsetPow : 256^(j*(ty.width/8)) = 2^(ty.width*j) := by
    rw [Nat.mul_comm j (ty.width/8),Nat.pow_mul,pow,←Nat.pow_mul]
  rw [offsetPow,pow] at chunk
  change integerBytes (ty.width/8) (laneBits ty.width j (vectorLoadBytes bytes start 0#u128 0 8).bv).toNat = _
  rw [laneBits_toNat,UScalar.bv_toNat]
  rw [←chunk,List.drop_take,List.take_take,List.drop_drop]
  rw [Nat.min_eq_left (by omega)]
end Itasca.Runtime.Interp.Simd
