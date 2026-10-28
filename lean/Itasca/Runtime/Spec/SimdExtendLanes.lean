import Itasca.Runtime.Spec.SimdWidenLists
import Itasca.Runtime.Spec.SimdCompareFloatLists
import Itasca.Runtime.Spec.SimdChoices
namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

def extendOperation (ty : WidenWidth) (high signed : Bool) : vcvtop__ :=
  .mk_vcvtop___0 ty.input (128/ty.width) ty.output ty.count (.EXTEND (widenHalf high) (widenSign signed))

theorem extend_lane_relation (ty : WidenWidth) (high signed : Bool) (bits : BitVec ty.width) :
    fun_lcvtop__ (shapeOf (lanetype_Jnn ty.input)) (shapeOf (lanetype_Jnn ty.output))
      (extendOperation ty high signed) (laneOfBits (lanetype_Jnn ty.input) bits.toNat)
      (some [.mk_lane__0 ty.output (.mk_uN (extendBits signed (ty.width*2) bits).toNat)]) := by
  have equation := extend_bits_source (ty.width*2) signed bits (by omega)
  have wf := unsigned_wf_of_lt (ty.width*2) (extendBits signed (ty.width*2) bits).toNat (BitVec.isLt _)
  cases ty with
  | i8 => exact .fun_lcvtop___case_14 _ _ _ _ _ _ _ _ equation (.lane__case_0 _ _ _ wf rfl) rfl rfl
  | i16 => exact .fun_lcvtop___case_3 _ _ _ _ _ _ _ _ equation (.lane__case_0 _ _ _ wf rfl) rfl rfl
  | i32 => exact .fun_lcvtop___case_4 _ _ _ _ _ _ _ _ equation (.lane__case_0 _ _ _ wf rfl) rfl rfl

def extendChoices (ty : WidenWidth) (high signed : Bool) (x : BitVec 128) : List (Option (List lane_)) :=
  (widenWords ty false high signed x x).map (fun word => some [.mk_lane__0 ty.output word])

theorem extend_choices_relation (ty : WidenWidth) (high signed : Bool) (x : BitVec 128) :
    Forall₂ (fun result input => fun_lcvtop__ (shapeOf (lanetype_Jnn ty.input)) (shapeOf (lanetype_Jnn ty.output))
      (extendOperation ty high signed) input result) (extendChoices ty high signed x) (widenInputs ty high x) := by
  unfold extendChoices widenWords
  rw [List.map_map]
  apply forall2_map
  intro j member
  exact extend_lane_relation ty high signed _

theorem extend_choices_nonempty (ty : WidenWidth) (high signed : Bool) (x : BitVec 128) :
    Forall (fun choice => choice ≠ none) (extendChoices ty high signed x) := by
  intro choice member
  obtain ⟨word,_,rfl⟩ := List.mem_map.mp member
  simp

theorem extend_chosen (ty : WidenWidth) (high signed : Bool) (x : BitVec 128) :
    Map (lane_.mk_lane__0 ty.output) (widenWords ty false high signed x x) ∈
      setproduct_ lane_ (Map (fun choice => Option.get! choice) (extendChoices ty high signed x)) := by
  unfold extendChoices Map
  rw [List.map_map]
  apply mem_setproduct_map
  intro word member
  simp

theorem extend_halfop (ty : WidenWidth) (high signed : Bool) :
    fun_halfop (shapeOf (lanetype_Jnn ty.input)) (shapeOf (lanetype_Jnn ty.output))
      (extendOperation ty high signed) (some (some (widenHalf high))) := by
  cases ty with
  | i8 => exact .fun_halfop_case_14 _ _ _ _ _ _ rfl rfl
  | i16 => exact .fun_halfop_case_3 _ _ _ _ _ _ rfl rfl
  | i32 => exact .fun_halfop_case_4 _ _ _ _ _ _ rfl rfl

theorem extend_source_wf (ty : WidenWidth) (high signed : Bool) : wf_admininstr (widenSource ty false high signed) := by
  apply wf_admininstr.admininstr_case_39
  · exact shapeOf_wf _
  · exact shapeOf_wf _
  · apply wf_vcvtop__.vcvtop___case_0
    · apply wf_vcvtop__Jnn_1_M_1_Jnn_2_M_2.vcvtop__Jnn_1_M_1_Jnn_2_M_2_case_0
      cases ty <;> decide
    · rfl
    · cases ty <;> rfl
end Itasca.Runtime.Spec.Simd
