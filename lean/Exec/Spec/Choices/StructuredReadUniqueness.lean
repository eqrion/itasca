import Exec.Spec.Choices.ReadAuxiliaryUniqueness
import Exec.Spec.Choices.VectorReadUniqueness
/-! Well-formed widening and zero-extending loads have fixed widths,
complete read ranges and unique decoded vector results. -/

namespace Exec.Spec
open SpecExt

theorem source_vector_load_operation {z : state} {address : num_} {operation : vloadop_} {argument : memarg}
    (wellFormed : wf_config ⟨z,[.CONST .I32 address,.VLOAD .V128 (some operation) argument]⟩) :
    wf_vloadop_ .V128 operation := by
  have instruction := (wf_config_parts wellFormed).2 (.VLOAD .V128 (some operation) argument) (by simp)
  cases instruction
  have all : Forall (fun op => wf_vloadop_ .V128 op) (Option.toList (some operation)) := by assumption
  exact all _ (by simp)

theorem source_zero_read_width {z : state} {address : num_} {bits : Nat} {argument : memarg}
    (wellFormed : wf_config ⟨z,[.CONST .I32 address,.VLOAD .V128 (some (.ZERO (.mk_sz bits))) argument]⟩) :
    bits=32 ∨ bits=64 := by
  have operation := source_vector_load_operation wellFormed
  cases operation
  casesm* wf_sz _
  simp only [proj_sz_0] at *
  omega

theorem source_widening_shape {type : Jnn} {bits count : Nat}
    (double : jsize type=bits*2) (width : wf_sz (.mk_sz bits))
    (shape : wf_shape (.X (lanetype_Jnn type) (.mk_dim count))) :
    ∃ selected : Simd.WidenWidth, bits=selected.width ∧ count=selected.count ∧ type=selected.output := by
  cases width
  have sizes : bits=8 ∨ bits=16 ∨ bits=32 ∨ bits=64 := by tauto
  cases shape
  rcases sizes with rfl | rfl | rfl | rfl
  all_goals cases type <;> norm_num [jsize,lsize,lanetype_Jnn,sizenn,size,valtype_numtype,psize,proj_dim_0] at *
  all_goals first
    | exact ⟨.i8,rfl,by norm_num [Simd.WidenWidth.count,Simd.WidenWidth.width,Simd.WidenWidth.input,lsize,lanetype_Jnn,sizenn,size,valtype_numtype,psize] <;> omega,rfl⟩
    | exact ⟨.i16,rfl,by norm_num [Simd.WidenWidth.count,Simd.WidenWidth.width,Simd.WidenWidth.input,lsize,lanetype_Jnn,sizenn,size,valtype_numtype,psize] <;> omega,rfl⟩
    | exact ⟨.i32,rfl,by norm_num [Simd.WidenWidth.count,Simd.WidenWidth.width,Simd.WidenWidth.input,lsize,lanetype_Jnn,sizenn,size,valtype_numtype,psize] <;> omega,rfl⟩

theorem source_widening_values_unique {leftType rightType : Jnn} {bits : Nat} {sign : sx}
    {left right : List uN} (payload : Nat → List byte)
    (width : wf_sz (.mk_sz bits))
    (leftDouble : jsize leftType=bits*2) (rightDouble : jsize rightType=bits*2)
    (leftShape : wf_shape (.X (lanetype_Jnn leftType) (.mk_dim left.length)))
    (rightShape : wf_shape (.X (lanetype_Jnn rightType) (.mk_dim right.length)))
    (leftBound : Forall (fun word => proj_uN_0 word<2^bits) left)
    (rightBound : Forall (fun word => proj_uN_0 word<2^bits) right)
    (leftRead : Forall₂ (fun index word => ibytes_ bits word=payload index) (List.range left.length) left)
    (rightRead : Forall₂ (fun index word => ibytes_ bits word=payload index) (List.range right.length) right) :
    [admininstr.VCONST .V128 (inv_lanes_ (.X (lanetype_Jnn leftType) (.mk_dim left.length))
      (Map (fun word => .mk_lane__0 leftType (extend__ bits (jsize leftType) sign word)) left))] =
    [admininstr.VCONST .V128 (inv_lanes_ (.X (lanetype_Jnn rightType) (.mk_dim right.length))
      (Map (fun word => .mk_lane__0 rightType (extend__ bits (jsize rightType) sign word)) right))] := by
  have sameType := source_jsize_injective (leftDouble.trans rightDouble.symm)
  cases sameType
  have sameCount := source_shape_dimension_unique leftShape rightShape
  obtain ⟨selected,bitsEq,countEq,typeEq⟩ := source_widening_shape leftDouble width leftShape
  have rightCount : right.length=selected.count := sameCount.symm.trans countEq
  have words : left=right := by
    apply Simd.extending_read_values_unique selected payload left right countEq rightCount
    · simpa only [← bitsEq] using leftBound
    · simpa only [← bitsEq] using rightBound
    · simpa only [← bitsEq,← countEq] using leftRead
    · simpa only [← bitsEq,← rightCount] using rightRead
  cases words
  rfl

theorem source_widening_read_inside {type : Jnn} {bits : Nat} {words : List uN} {address : Nat} {bytes : List byte}
    (width : wf_sz (.mk_sz bits)) (double : jsize type=bits*2)
    (shape : wf_shape (.X (lanetype_Jnn type) (.mk_dim words.length)))
    (read : Forall₂ (fun (index : Nat) word => ibytes_ bits word=
      (bytes.drop (address+rat_to_nat ((index : Rat)*(bits : Rat)/8))).take (rat_to_nat ((bits : Rat)/8)))
      (List.range words.length) words) :
    address+rat_to_nat ((bits : Rat)*(words.length : Rat)/8)≤bytes.length := by
  obtain ⟨selected,bitsEq,countEq,typeEq⟩ := source_widening_shape double width shape
  have inside := Simd.extending_read_bounds selected bytes address words countEq (by simpa only [← bitsEq,← countEq] using read)
  rw [bitsEq,countEq]
  cases selected <;> norm_num [Simd.WidenWidth.count,Simd.WidenWidth.width,Simd.WidenWidth.input,
    lsize,lanetype_Jnn,sizenn,size,valtype_numtype,psize,rat_to_nat] at *
  all_goals omega

theorem source_zero_read_inside {z : state} {address : num_} {bits : Nat} {argument : memarg} {word : uN}
    (wellFormed : wf_config ⟨z,[.CONST .I32 address,.VLOAD .V128 (some (.ZERO (.mk_sz bits))) argument]⟩)
    (read : ibytes_ bits word=((fun_mem z (.mk_uN 0)).BYTES.drop
      (proj_uN_0 (proj_num__0 address).get!+proj_uN_0 argument.OFFSET)).take (rat_to_nat ((bits : Rat)/8))) :
    proj_uN_0 (proj_num__0 address).get!+proj_uN_0 argument.OFFSET+rat_to_nat ((bits : Rat)/8)≤
      (fun_mem z (.mk_uN 0)).BYTES.length := by
  have width := source_zero_read_width wellFormed
  exact bounded_integer_read_inside (by tauto) read

theorem source_zero_values_unique {bits : Nat} {left right : uN}
    (width : bits=32 ∨ bits=64) (leftTyped : wf_uN bits left) (rightTyped : wf_uN bits right)
    (same : ibytes_ bits left=ibytes_ bits right) :
    [admininstr.VCONST .V128 (extend__ bits 128 .U left)]=[admininstr.VCONST .V128 (extend__ bits 128 .U right)] := by
  have words := bounded_integer_encoding_unique (by tauto) (unsigned_bound_of_wf _ _ leftTyped)
    (unsigned_bound_of_wf _ _ rightTyped) same
  cases words
  rfl
end Exec.Spec
