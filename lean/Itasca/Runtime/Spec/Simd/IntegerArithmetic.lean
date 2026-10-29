import Itasca.Runtime.Spec.Simd.CompareInteger

/-!
Source-rule algebra for wrapping integer lane arithmetic. Lane/list calculations establish the generated source operation and its reduction step, consumed by source-machine and interpreter correspondence proofs.
-/

/-! ## Simd Integer Arithmetic -/

section

namespace Itasca.Runtime.Spec.Simd

inductive IntegerArithmetic where | add | sub | mul

def integerArithmeticBits (kind : IntegerArithmetic) {width : Nat} (a b : BitVec width) : BitVec width :=
  match kind with | .add => a+b | .sub => a-b | .mul => a*b

def IntegerArithmeticRel (kind : IntegerArithmetic) (width : Nat) (a b result : uN) : Prop :=
  match kind with
  | .add => fun_iadd_ width a b result
  | .sub => fun_isub_ width a b result
  | .mul => fun_imul_ width a b result

theorem integer_arithmetic_relation (kind : IntegerArithmetic) {width : Nat} (a b : BitVec width) :
    IntegerArithmeticRel kind width (.mk_uN a.toNat) (.mk_uN b.toNat)
      (.mk_uN (integerArithmeticBits kind a b).toNat) := by
  have wf := unsigned_wf_of_lt width (integerArithmeticBits kind a b).toNat (BitVec.isLt _)
  cases kind with
  | add =>
    simpa only [IntegerArithmeticRel,integerArithmeticBits,BitVec.toNat_add,proj_uN_0] using
      fun_iadd_.fun_iadd__case_0 width (.mk_uN a.toNat) (.mk_uN b.toNat) (by simpa only [integerArithmeticBits,BitVec.toNat_add,proj_uN_0] using wf)
  | mul =>
    simpa only [IntegerArithmeticRel,integerArithmeticBits,BitVec.toNat_mul,proj_uN_0] using
      fun_imul_.fun_imul__case_0 width (.mk_uN a.toNat) (.mk_uN b.toNat) (by simpa only [integerArithmeticBits,BitVec.toNat_mul,proj_uN_0] using wf)
  | sub =>
    have formula : (a-b).toNat = ((2^width+(a.toNat:Int)-b.toNat)%(2^width:Int)).toNat := by
      rw [BitVec.toNat_sub]
      have castEq : (((2^width-b.toNat+a.toNat)%2^width : Nat) : Int) =
          (2^width+(a.toNat:Int)-b.toNat)%(2^width:Int) := by
        rw [Int.natCast_emod,Nat.cast_add,Nat.cast_sub (Nat.le_of_lt b.isLt),Nat.cast_pow,Nat.cast_ofNat]
        congr 1
        omega
      exact congrArg Int.toNat castEq
    have relation := fun_isub_.fun_isub__case_0 width (.mk_uN a.toNat) (.mk_uN b.toNat)
      (by simpa only [integerArithmeticBits,formula,proj_uN_0] using wf)
    simpa only [IntegerArithmeticRel,integerArithmeticBits,formula,proj_uN_0] using relation

end Itasca.Runtime.Spec.Simd

end

/-! ## Simd Integer Arithmetic Shape -/

section

namespace Itasca.Runtime.Spec.Simd

def integerArithmeticSupported (ty : Jnn) (kind : IntegerArithmetic) : Prop :=
  match ty,kind with | .I8,.mul => False | _,_ => True

def integerArithmeticOp (kind : IntegerArithmetic) : vbinop_Jnn_N :=
  match kind with | .add => .ADD | .sub => .SUB | .mul => .MUL

def integerArithmeticSource (ty : Jnn) (kind : IntegerArithmetic) : vbinop_ :=
  .mk_vbinop__0 ty (128/lsize (lanetype_Jnn ty)) (integerArithmeticOp kind)

theorem integer_arithmetic_source_wf (ty : Jnn) (kind : IntegerArithmetic)
    (supported : integerArithmeticSupported ty kind) :
    wf_vbinop_ (shapeOf (lanetype_Jnn ty)) (integerArithmeticSource ty kind) := by
  cases ty <;> cases kind <;> simp only [integerArithmeticSupported] at supported
  all_goals try contradiction
  all_goals constructor <;> constructor
  all_goals decide

end Itasca.Runtime.Spec.Simd

end

/-! ## Simd Integer Arithmetic Lists -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

def arithmeticWords (ty : Jnn) (kind : IntegerArithmetic) (x y : BitVec 128) : List uN :=
  (List.range (128/lsize (lanetype_Jnn ty))).map (fun j =>
    .mk_uN (integerArithmeticBits kind (laneWord (lanetype_Jnn ty) x j) (laneWord (lanetype_Jnn ty) y j)).toNat)

theorem arithmetic_words_relation (ty : Jnn) (kind : IntegerArithmetic) (x y : BitVec 128) :
    Forall₃ (fun result a b => IntegerArithmeticRel kind (lsize (lanetype_Jnn ty))
      (Option.get! (proj_lane__0 a)) (Option.get! (proj_lane__0 b)) result)
      (arithmeticWords ty kind x y)
      (lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN x.toNat))
      (lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN y.toNat)) := by
  rw [lanes_map_words,lanes_map_words]
  apply forall3_map
  intro j member
  have relation := integer_arithmetic_relation kind (laneWord (lanetype_Jnn ty) x j) (laneWord (lanetype_Jnn ty) y j)
  cases ty <;> exact relation

theorem arithmetic_words_length (ty : Jnn) (kind : IntegerArithmetic) (x y : BitVec 128) :
    (arithmeticWords ty kind x y).length = 128/lsize (lanetype_Jnn ty) := by
  simp [arithmeticWords]

theorem arithmetic_words_wf (ty : Jnn) (kind : IntegerArithmetic) (x y : BitVec 128) :
    Forall (fun word => wf_lane_ (lanetype_Jnn ty) (.mk_lane__0 ty word)) (arithmeticWords ty kind x y) := by
  intro word member
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
  cases ty <;> constructor
  all_goals first | rfl | exact unsigned_wf_of_lt _ _ (BitVec.isLt _)

end Itasca.Runtime.Spec.Simd

end

/-! ## Simd Integer Arithmetic Source -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

def integerArithmeticResult (ty : Jnn) (kind : IntegerArithmetic) (x y : BitVec 128) : uN :=
  inv_lanes_ (shapeOf (lanetype_Jnn ty))
    (Map (lane_.mk_lane__0 ty) (arithmeticWords ty kind x y))

theorem integer_arithmetic_vector_relation (ty : Jnn) (kind : IntegerArithmetic) (x y : BitVec 128) :
    fun_vbinop_ (shapeOf (lanetype_Jnn ty)) (integerArithmeticSource ty kind)
      (.mk_uN x.toNat) (.mk_uN y.toNat) (some [integerArithmeticResult ty kind x y]) := by
  have lenX : (arithmeticWords ty kind x y).length =
      (lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN x.toNat)).length := by
    rw [arithmetic_words_length,lanes_map_words,List.length_map,List.length_range]
  have lenY : (arithmeticWords ty kind x y).length =
      (lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN y.toNat)).length := by
    rw [arithmetic_words_length,lanes_map_words,List.length_map,List.length_range]
  have nonX := integer_lanes_nonempty ty x
  have nonY := integer_lanes_nonempty ty y
  have relation := arithmetic_words_relation ty kind x y
  have maskWf := arithmetic_words_wf ty kind x y
  have shapeWf := shapeOf_wf (lanetype_Jnn ty)
  cases ty <;> cases kind
  all_goals first
    | apply fun_vbinop_.fun_vbinop__case_0 (var_1_lst := arithmeticWords _ _ x y) (var_0_lst := arithmeticWords _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat))
    | apply fun_vbinop_.fun_vbinop__case_1 (var_1_lst := arithmeticWords _ _ x y) (var_0_lst := arithmeticWords _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat))
    | apply fun_vbinop_.fun_vbinop__case_2 (var_1_lst := arithmeticWords _ _ x y) (var_0_lst := arithmeticWords _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat))
    | apply fun_vbinop_.fun_vbinop__case_3 (var_1_lst := arithmeticWords _ _ x y) (var_0_lst := arithmeticWords _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat))
    | apply fun_vbinop_.fun_vbinop__case_4 (var_1_lst := arithmeticWords _ _ x y) (var_0_lst := arithmeticWords _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat))
    | apply fun_vbinop_.fun_vbinop__case_5 (var_1_lst := arithmeticWords _ _ x y) (var_0_lst := arithmeticWords _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat))
    | apply fun_vbinop_.fun_vbinop__case_6 (var_1_lst := arithmeticWords _ _ x y) (var_0_lst := arithmeticWords _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat))
    | apply fun_vbinop_.fun_vbinop__case_7 (var_1_lst := arithmeticWords _ _ x y) (var_0_lst := arithmeticWords _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat))
    | apply fun_vbinop_.fun_vbinop__case_24 (var_1_lst := arithmeticWords _ _ x y) (var_0_lst := arithmeticWords _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat))
    | apply fun_vbinop_.fun_vbinop__case_25 (var_1_lst := arithmeticWords _ _ x y) (var_0_lst := arithmeticWords _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat))
    | apply fun_vbinop_.fun_vbinop__case_26 (var_1_lst := arithmeticWords _ _ x y) (var_0_lst := arithmeticWords _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat))
    | apply fun_vbinop_.fun_vbinop__case_27 (var_1_lst := arithmeticWords _ _ x y) (var_0_lst := arithmeticWords _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat))
  all_goals first
    | rfl
    | exact lenX
    | exact lenY
    | exact nonX
    | exact nonY
    | exact shapeWf
    | exact maskWf
    | exact relation

end Itasca.Runtime.Spec.Simd

end

/-! ## Simd Integer Arithmetic Step -/

section

namespace Itasca.Runtime.Spec.Simd

theorem integer_arithmetic_step (ty : Jnn) (kind : IntegerArithmetic) (x y result : BitVec 128)
    (supported : integerArithmeticSupported ty kind)
    (packed : uN.mk_uN result.toNat = integerArithmeticResult ty kind x y) :
    Step_pure [.VCONST .V128 (.mk_uN x.toNat),.VCONST .V128 (.mk_uN y.toNat),
      .VBINOP (shapeOf (lanetype_Jnn ty)) (integerArithmeticSource ty kind)]
      [.VCONST .V128 (.mk_uN result.toNat)] := by
  apply Step_pure.vbinop_val _ _ _ _ _ (some [.mk_uN result.toNat])
  · rw [packed]
    exact integer_arithmetic_vector_relation ty kind x y
  · change 0 < 1
    decide
  · simp
  · simp
  · exact const_wf x
  · exact const_wf y
  · exact .admininstr_case_26 _ _ (shapeOf_wf _) (integer_arithmetic_source_wf ty kind supported)
  · exact const_wf result

end Itasca.Runtime.Spec.Simd

end
