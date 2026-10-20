import Exec.Spec.Choices.ReadAuxiliaryUniqueness
/-! Canonical vector-byte, splat and lane-load results from source-width
bounds and well-formed lane/shape judgments. -/

namespace Exec.Spec
open SpecExt

theorem vectorBytes_injective {left right : vec_}
    (first : wf_admininstr (.VCONST .V128 left)) (second : wf_admininstr (.VCONST .V128 right))
    (same : vbytes_ .V128 left=vbytes_ .V128 right) : left=right := by
  cases first
  cases second
  apply ibytes_injective 128 (by decide)
  · exact unsigned_bound_of_wf _ _ (by assumption)
  · exact unsigned_bound_of_wf _ _ (by assumption)
  · exact same

theorem source_jsize_injective {left right : Jnn} (same : jsize left=jsize right) : left=right := by
  cases left <;> cases right <;> norm_num [jsize,lsize,lanetype_Jnn,sizenn,size,valtype_numtype,psize] at same <;> rfl

theorem source_shape_dimension_unique {type : Jnn} {left right : Nat}
    (first : wf_shape (.X (lanetype_Jnn type) (.mk_dim left)))
    (second : wf_shape (.X (lanetype_Jnn type) (.mk_dim right))) : left=right := by
  cases first
  cases second
  cases type <;> norm_num [lsize,lanetype_Jnn,sizenn,size,valtype_numtype,psize,proj_dim_0] at * <;> omega

theorem source_lane_word_unique {type : Jnn} {left right : uN}
    (first : wf_lane_ (lanetype_Jnn type) (.mk_lane__0 type (.mk_uN (proj_uN_0 left))))
    (second : wf_lane_ (lanetype_Jnn type) (.mk_lane__0 type (.mk_uN (proj_uN_0 right))))
    (same : ibytes_ (jsize type) left=ibytes_ (jsize type) right) : left=right := by
  exact ibytes_injective (jsize type)
    (by cases type <;> norm_num [jsize,lsize,lanetype_Jnn,sizenn,size,valtype_numtype,psize]) left right
    (source_lane_word_bound type 0 left first) (source_lane_word_bound type 0 right second) same

theorem source_lane_read_inside {type : Jnn} {bytes : List byte} {address : Nat} {word : uN}
    (read : ibytes_ (jsize type) word=(bytes.drop address).take (rat_to_nat ((jsize type : Rat)/8))) :
    address+rat_to_nat ((jsize type : Rat)/8)≤bytes.length :=
  bounded_integer_read_inside (by cases type <;> norm_num [jsize,lsize,lanetype_Jnn,sizenn,size,valtype_numtype,psize]) read

theorem source_splat_unique {leftType rightType : Jnn} {leftCount rightCount : Nat} {left right : uN}
    (sameSize : jsize leftType=jsize rightType)
    (leftShape : wf_shape (.X (lanetype_Jnn leftType) (.mk_dim leftCount)))
    (rightShape : wf_shape (.X (lanetype_Jnn rightType) (.mk_dim rightCount)))
    (leftTyped : wf_lane_ (lanetype_Jnn leftType) (.mk_lane__0 leftType (.mk_uN (proj_uN_0 left))))
    (rightTyped : wf_lane_ (lanetype_Jnn rightType) (.mk_lane__0 rightType (.mk_uN (proj_uN_0 right))))
    (sameBytes : ibytes_ (jsize leftType) left=ibytes_ (jsize rightType) right) :
    [admininstr.VCONST .V128 (inv_lanes_ (.X (lanetype_Jnn leftType) (.mk_dim leftCount))
      (List.replicate leftCount (.mk_lane__0 leftType (.mk_uN (proj_uN_0 left)))))] =
    [admininstr.VCONST .V128 (inv_lanes_ (.X (lanetype_Jnn rightType) (.mk_dim rightCount))
      (List.replicate rightCount (.mk_lane__0 rightType (.mk_uN (proj_uN_0 right)))))] := by
  have sameType := source_jsize_injective sameSize
  cases sameType
  have sameCount := source_shape_dimension_unique leftShape rightShape
  cases sameCount
  have sameWord := source_lane_word_unique leftTyped rightTyped sameBytes
  cases sameWord
  rfl

theorem source_lane_load_unique {leftType rightType : Jnn} {leftCount rightCount : Nat} {left right : uN}
    (old : vec_) (index : Nat) (sameSize : jsize leftType=jsize rightType)
    (leftShape : wf_shape (.X (lanetype_Jnn leftType) (.mk_dim leftCount)))
    (rightShape : wf_shape (.X (lanetype_Jnn rightType) (.mk_dim rightCount)))
    (leftTyped : wf_lane_ (lanetype_Jnn leftType) (.mk_lane__0 leftType (.mk_uN (proj_uN_0 left))))
    (rightTyped : wf_lane_ (lanetype_Jnn rightType) (.mk_lane__0 rightType (.mk_uN (proj_uN_0 right))))
    (sameBytes : ibytes_ (jsize leftType) left=ibytes_ (jsize rightType) right) :
    [admininstr.VCONST .V128 (inv_lanes_ (.X (lanetype_Jnn leftType) (.mk_dim leftCount))
      ((lanes_ (.X (lanetype_Jnn leftType) (.mk_dim leftCount)) old).modify index
        (fun _ => .mk_lane__0 leftType (.mk_uN (proj_uN_0 left)))))] =
    [admininstr.VCONST .V128 (inv_lanes_ (.X (lanetype_Jnn rightType) (.mk_dim rightCount))
      ((lanes_ (.X (lanetype_Jnn rightType) (.mk_dim rightCount)) old).modify index
        (fun _ => .mk_lane__0 rightType (.mk_uN (proj_uN_0 right)))))] := by
  have sameType := source_jsize_injective sameSize
  cases sameType
  have sameCount := source_shape_dimension_unique leftShape rightShape
  cases sameCount
  have sameWord := source_lane_word_unique leftTyped rightTyped sameBytes
  cases sameWord
  rfl
end Exec.Spec
