import Exec.Spec.SimdIntegerArithmetic
import Exec.Spec.IntegerExtend
namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

def dotProduct (x y : BitVec 128) (j : Nat) : BitVec 32 :=
  (laneWord .I16 x j).signExtend 32 * (laneWord .I16 y j).signExtend 32

def dotBits (x y : BitVec 128) (j : Nat) : BitVec 32 :=
  dotProduct x y (j*2) + dotProduct x y (j*2+1)

theorem dot_bits_int (x y : BitVec 128) (j : Nat) :
    dotBits x y j = BitVec.ofInt 32
      ((laneWord .I16 x (j*2)).toInt * (laneWord .I16 y (j*2)).toInt +
       (laneWord .I16 x (j*2+1)).toInt * (laneWord .I16 y (j*2+1)).toInt) := by
  simp [dotBits,dotProduct,BitVec.signExtend,BitVec.ofInt_add,BitVec.ofInt_mul]

def dotProducts (x y : BitVec 128) : List uN :=
  (List.range 8).map (fun j => .mk_uN (dotProduct x y j).toNat)

def dotHalfProducts (x y : BitVec 128) (offset : Nat) : List uN :=
  (List.range 4).map (fun j => .mk_uN (dotProduct x y (j*2+offset)).toNat)

def dotWords (x y : BitVec 128) : List uN :=
  (List.range 4).map (fun j => .mk_uN (dotBits x y j).toNat)

def dotResult (x y : BitVec 128) : uN :=
  inv_lanes_ (shapeOf .I32) (Map (lane_.mk_lane__0 .I32) (dotWords x y))

def dotSource : admininstr :=
  .VEXTBINOP (.mk_ishape (shapeOf .I32)) (.mk_ishape (shapeOf .I16))
    (.mk_vextbinop___0 .I16 8 .I32 4 .DOTS)

theorem dot_product_relation (x y : BitVec 128) :
    Forall₃ (fun answer a b => fun_imul_ 32
      (extend__ 16 32 .S (Option.get! (proj_lane__0 a)))
      (extend__ 16 32 .S (Option.get! (proj_lane__0 b))) answer)
      (dotProducts x y) (lanes_ (shapeOf .I16) (.mk_uN x.toNat))
        (lanes_ (shapeOf .I16) (.mk_uN y.toNat)) := by
  rw [lanes_map_words,lanes_map_words]
  apply forall3_map
  intro j member
  simp only [laneOfBits,proj_lane__0,Option.get!_some]
  have relation := integer_arithmetic_relation .mul
    ((laneWord .I16 x j).signExtend 32) ((laneWord .I16 y j).signExtend 32)
  have ex := Itasca.Runtime.Spec.extend_signed_bitvec 16 32 (laneWord .I16 x j)
  have ey := Itasca.Runtime.Spec.extend_signed_bitvec 16 32 (laneWord .I16 y j)
  exact (congrArg₂ (fun a b => fun_imul_ 32 a b (.mk_uN (dotProduct x y j).toNat)) ex ey).mpr relation

theorem dot_sum_relation (x y : BitVec 128) :
    Forall₃ (fun answer a b => fun_iadd_ 32 a b answer)
      (dotWords x y) (dotHalfProducts x y 0) (dotHalfProducts x y 1) := by
  apply forall3_map
  intro j member
  exact integer_arithmetic_relation .add _ _

theorem dot_interleave (x y : BitVec 128) :
    concat_ uN (Map₂ (fun a b => [a,b]) (dotHalfProducts x y 0) (dotHalfProducts x y 1)) = dotProducts x y := by
  rfl

theorem dot_words_wf (x y : BitVec 128) :
    Forall (fun word => wf_lane_ .I32 (.mk_lane__0 .I32 word)) (dotWords x y) := by
  unfold dotWords
  intro a member
  obtain ⟨j,valid,rfl⟩ := List.mem_map.mp member
  exact .lane__case_0 _ _ _ (unsigned_wf_of_lt 32 _ (BitVec.isLt _)) rfl

end Itasca.Runtime.Spec.Simd
