import Exec.Spec.SimdWiden
import Exec.Spec.SimdIntegerArithmetic
namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

def widenInputs (ty : WidenWidth) (high : Bool) (x : BitVec 128) : List lane_ :=
  (List.range ty.count).map (fun j => laneOfBits (lanetype_Jnn ty.input)
    (laneWord (lanetype_Jnn ty.input) x (j+if high then ty.count else 0)).toNat)

def widenWords (ty : WidenWidth) (multiply high signed : Bool) (x y : BitVec 128) : List uN :=
  (List.range ty.count).map (fun j => .mk_uN (widenBits multiply signed
    (laneWord (lanetype_Jnn ty.input) x (j+if high then ty.count else 0))
    (laneWord (lanetype_Jnn ty.input) y (j+if high then ty.count else 0))).toNat)

def widenResult (ty : WidenWidth) (multiply high signed : Bool) (x y : BitVec 128) : uN :=
  inv_lanes_ (shapeOf (lanetype_Jnn ty.output)) (Map (lane_.mk_lane__0 ty.output) (widenWords ty multiply high signed x y))

theorem widen_selected (ty : WidenWidth) (high : Bool) (x : BitVec 128) :
    widenInputs ty high x = List.take ty.count (List.drop (fun_half (widenHalf high) 0 ty.count)
      (lanes_ (shapeOf (lanetype_Jnn ty.input)) (.mk_uN x.toNat))) := by
  rw [lanes_map_words]
  cases ty <;> cases high <;> rfl

theorem widen_inputs_nonempty (ty : WidenWidth) (high : Bool) (x : BitVec 128) :
    Forall (fun lane => proj_lane__0 lane ≠ none) (widenInputs ty high x) := by
  intro lane member
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
  cases ty <;> simp [laneOfBits,lanetype_Jnn,WidenWidth.input,proj_lane__0]

theorem widen_words_wf (ty : WidenWidth) (multiply high signed : Bool) (x y : BitVec 128) :
    Forall (fun word => wf_lane_ (lanetype_Jnn ty.output) (.mk_lane__0 ty.output word))
      (widenWords ty multiply high signed x y) := by
  intro word member
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
  have wf := unsigned_wf_of_lt (ty.width*2)
    (widenBits multiply signed (laneWord (lanetype_Jnn ty.input) x (j+if high then ty.count else 0))
      (laneWord (lanetype_Jnn ty.input) y (j+if high then ty.count else 0))).toNat (BitVec.isLt _)
  cases ty <;> exact .lane__case_0 _ _ _ wf rfl

theorem widen_multiply_relation (ty : WidenWidth) (high signed : Bool) (x y : BitVec 128) :
    Forall₃ (fun answer a b => fun_imul_ (lsize (lanetype_Jnn ty.output))
      (extend__ ty.width (lsize (lanetype_Jnn ty.output)) (widenSign signed) (Option.get! (proj_lane__0 a)))
      (extend__ ty.width (lsize (lanetype_Jnn ty.output)) (widenSign signed) (Option.get! (proj_lane__0 b))) answer)
      (widenWords ty true high signed x y) (widenInputs ty high x) (widenInputs ty high y) := by
  apply forall3_map
  intro j member
  have relation := integer_arithmetic_relation .mul
    (extendBits signed (ty.width*2) (laneWord (lanetype_Jnn ty.input) x (j+if high then ty.count else 0)))
    (extendBits signed (ty.width*2) (laneWord (lanetype_Jnn ty.input) y (j+if high then ty.count else 0)))
  have ex := extend_bits_source (ty.width*2) signed
    (laneWord (lanetype_Jnn ty.input) x (j+if high then ty.count else 0)) (by cases ty <;> decide)
  have ey := extend_bits_source (ty.width*2) signed
    (laneWord (lanetype_Jnn ty.input) y (j+if high then ty.count else 0)) (by cases ty <;> decide)
  have relation' := (congrArg₂ (fun a b => fun_imul_ (ty.width*2) a b
    (.mk_uN (widenBits true signed
      (laneWord (lanetype_Jnn ty.input) x (j+if high then ty.count else 0))
      (laneWord (lanetype_Jnn ty.input) y (j+if high then ty.count else 0))).toNat)) ex ey).mp relation
  cases ty <;> exact relation'
end Itasca.Runtime.Spec.Simd
