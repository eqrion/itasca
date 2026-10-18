import Exec.Spec.SimdExtract
namespace Exec.Spec.Simd
open SpecExt.Builtins

def byteAt (bits : BitVec 128) (index : Nat) : Nat := bits.toNat/2^(8*index)%2^8

def byteWords (bits : BitVec 128) : List uN := (List.range 16).map (fun i => .mk_uN (byteAt bits i))

theorem byteAt_bound (bits : BitVec 128) (index : Nat) : byteAt bits index < 2^8 :=
  Nat.mod_lt _ (by decide)

@[simp] theorem byteWords_length (bits : BitVec 128) : (byteWords bits).length = 16 := by
  simp [byteWords]

theorem byteWords_get (bits : BitVec 128) (index : Nat) (valid : index < 16) :
    (byteWords bits)[index]! = .mk_uN (byteAt bits index) := by
  simp [byteWords,List.getElem!_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,valid]

theorem byteWords_lanes (bits : BitVec 128) :
    (byteWords bits).map (lane_.mk_lane__0 .I8) = lanes_ (shapeOf .I8) (.mk_uN bits.toNat) := by
  apply List.ext_getElem?
  intro i
  change (((List.range 16).map (fun j => uN.mk_uN (byteAt bits j))).map (lane_.mk_lane__0 .I8))[i]? =
    (unpackLanes .I8 16 bits.toNat)[i]?
  rw [unpackLanes_getElem?]
  by_cases valid : i < 16
  · simp [List.getElem?_map,List.getElem?_range,valid,byteAt,lsize,psize,size,laneOfBits]
  · simp [List.getElem?_map,List.getElem?_range,valid]

theorem byteWords_wf (bits : BitVec 128) :
    Forall (fun word => wf_lane_ .I8 (.mk_lane__0 .I8 word)) (byteWords bits) := by
  intro word member
  obtain ⟨index,_,rfl⟩ := List.mem_map.mp member
  exact .lane__case_0 _ _ _ (unsigned_wf_of_lt 8 _ (byteAt_bound bits index)) rfl

end Exec.Spec.Simd
