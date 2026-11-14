import Itasca.Runtime.Spec.Simd.CompareInteger
import Itasca.Runtime.Spec.SegmentInitCases
import SpecExt.Builtins.Examples
import SpecExt.Builtins.Float.MinMax

/-!
Sections, each formerly its own module: IntegerArithmetic, Shift, Widen, Choices, CompareFloat, ExtendLanes.
-/

/-! ## IntegerArithmetic -/

section

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
  have shapeWf := shape_of_wf (lanetype_Jnn ty)
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
  · exact .admininstr_case_26 _ _ (shape_of_wf _) (integer_arithmetic_source_wf ty kind supported)
  · exact const_wf result

end Itasca.Runtime.Spec.Simd

end

end

/-! ## Shift -/

section

/-!
Source-rule algebra for lane shifts. Lane/list calculations establish the generated source operation and its reduction step, consumed by source-machine and interpreter correspondence proofs.
-/

/-! ## Simd Shift -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

inductive ShiftKind where
  | left | signedRight | unsignedRight

def shiftBits (kind : ShiftKind) {width : Nat} (bits : BitVec width) (amount : Nat) : BitVec width :=
  match kind with
  | .left => bits <<< amount
  | .signedRight => bits.sshiftRight amount
  | .unsignedRight => bits >>> amount

def shiftOperation (kind : ShiftKind) : vshiftop_Jnn_N :=
  match kind with
  | .left => .SHL
  | .signedRight => .SHR .S
  | .unsignedRight => .SHR .U

def shiftSource (ty : Jnn) (kind : ShiftKind) : admininstr :=
  .VSHIFTOP (.mk_ishape (shapeOf (lanetype_Jnn ty)))
    (.mk_vshiftop__0 ty (128/lsize (lanetype_Jnn ty)) (shiftOperation kind))

theorem ishl_bitvec (width : Nat) (bits : BitVec width) (amount : Nat) :
    ishl_ width (.mk_uN bits.toNat) (.mk_uN amount) =
      .mk_uN (bits <<< (amount%width)).toNat := by
  simp [ishl_,proj_uN_0,BitVec.toNat_shiftLeft,Nat.shiftLeft_eq]

theorem ishru_bitvec (width : Nat) (bits : BitVec width) (amount : Nat) :
    ishr_ width .U (.mk_uN bits.toNat) (.mk_uN amount) =
      .mk_uN (bits >>> (amount%width)).toNat := by
  simp [ishr_,proj_uN_0,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]

theorem shift_lane_relation (ty : Jnn) (kind : ShiftKind)
    (bits : BitVec (lsize (lanetype_Jnn ty))) (amount : Nat) :
    fun_vshiftop_ (.mk_ishape (shapeOf (lanetype_Jnn ty)))
      (.mk_vshiftop__0 ty (128/lsize (lanetype_Jnn ty)) (shiftOperation kind))
      (laneOfBits (lanetype_Jnn ty) bits.toNat) (.mk_uN amount)
      (some (laneOfBits (lanetype_Jnn ty) (shiftBits kind bits (amount%lsize (lanetype_Jnn ty))).toNat)) := by
  have wf := lane_of_bits_wf (lanetype_Jnn ty) (shiftBits kind bits (amount%lsize (lanetype_Jnn ty))).toNat
    (BitVec.toNat_lt_twoPow_of_le (by rfl))
  have laneEq (n : Nat) : laneOfBits (lanetype_Jnn ty) n = .mk_lane__0 ty (.mk_uN n) := by cases ty <;> rfl
  simp only [laneEq] at wf ⊢
  cases kind with
  | left =>
    simp only [shiftBits,shiftOperation] at wf ⊢
    rw [←ishl_bitvec] at wf ⊢
    cases ty
    · exact .fun_vshiftop__case_0 _ _ _ _ wf rfl
    · exact .fun_vshiftop__case_1 _ _ _ _ wf rfl
    · exact .fun_vshiftop__case_2 _ _ _ _ wf rfl
    · exact .fun_vshiftop__case_3 _ _ _ _ wf rfl
  | signedRight =>
    simp only [shiftBits,shiftOperation] at wf ⊢
    rw [←ishrs_bitvec] at wf ⊢
    cases ty
    · exact .fun_vshiftop__case_4 _ _ _ _ _ wf rfl
    · exact .fun_vshiftop__case_5 _ _ _ _ _ wf rfl
    · exact .fun_vshiftop__case_6 _ _ _ _ _ wf rfl
    · exact .fun_vshiftop__case_7 _ _ _ _ _ wf rfl
  | unsignedRight =>
    simp only [shiftBits,shiftOperation] at wf ⊢
    rw [←ishru_bitvec] at wf ⊢
    cases ty
    · exact .fun_vshiftop__case_4 _ _ _ _ _ wf rfl
    · exact .fun_vshiftop__case_5 _ _ _ _ _ wf rfl
    · exact .fun_vshiftop__case_6 _ _ _ _ _ wf rfl
    · exact .fun_vshiftop__case_7 _ _ _ _ _ wf rfl
end Itasca.Runtime.Spec.Simd

end

/-! ## Simd Shift Source -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

def vectorLane (ty : lanetype) (bits : BitVec 128) (j : Nat) : BitVec (lsize ty) :=
  (bits >>> (lsize ty*j)).setWidth (lsize ty)

def shiftLaneValues (ty : Jnn) (kind : ShiftKind) (bits : BitVec 128) (amount : Nat) : List lane_ :=
  (List.range (128/lsize (lanetype_Jnn ty))).map (fun j =>
    laneOfBits (lanetype_Jnn ty) (shiftBits kind (vectorLane (lanetype_Jnn ty) bits j)
      (amount % lsize (lanetype_Jnn ty))).toNat)

theorem vector_lanes (ty : lanetype) (bits : BitVec 128) :
    lanes_ (shapeOf ty) (.mk_uN bits.toNat) =
      (List.range (128/lsize ty)).map (fun j => laneOfBits ty (vectorLane ty bits j).toNat) := by
  apply unpackLanes_eq_map
  intro j valid
  simp only [vectorLane, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,proj_uN_0]

theorem shift_step (ty : Jnn) (kind : ShiftKind) (bits result : BitVec 128) (amount : BitVec 32)
    (packed : uN.mk_uN result.toNat = inv_lanes_ (shapeOf (lanetype_Jnn ty))
      (shiftLaneValues ty kind bits amount.toNat)) :
    Step_pure [.VCONST .V128 (.mk_uN bits.toNat),
      .CONST .I32 (.mk_num__0 .I32 (.mk_uN amount.toNat)), shiftSource ty kind]
      [.VCONST .V128 (.mk_uN result.toNat)] := by
  let inputs := (List.range (128/lsize (lanetype_Jnn ty))).map (fun j =>
    laneOfBits (lanetype_Jnn ty) (vectorLane (lanetype_Jnn ty) bits j).toNat)
  let outputs := (shiftLaneValues ty kind bits amount.toNat).map some
  have shapeWf := shape_of_wf (lanetype_Jnn ty)
  have integerShape : wf_ishape (.mk_ishape (shapeOf (lanetype_Jnn ty))) :=
    .ishape_case_0 ty _ shapeWf rfl
  apply Step_pure.vshiftop (.mk_uN bits.toNat) amount.toNat ty (128/lsize (lanetype_Jnn ty))
    (.mk_vshiftop__0 ty _ (shiftOperation kind)) (.mk_uN result.toNat) inputs outputs
  · simp [inputs,outputs,shiftLaneValues]
  · dsimp only [inputs,outputs,shiftLaneValues]
    rw [List.map_map]
    intro pair member
    rw [List.zip_map'] at member
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
    exact shift_lane_relation ty kind (vectorLane (lanetype_Jnn ty) bits j) amount.toNat
  · exact (vector_lanes _ _).symm
  · intro output member
    obtain ⟨lane,_,rfl⟩ := List.mem_map.mp member
    simp
  · simpa [outputs,Map,List.map_map,Function.comp_def,shapeOf] using packed
  · intro lane member
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
    exact lane_of_bits_wf _ _ (BitVec.toNat_lt_twoPow_of_le (by rfl))
  · exact const_wf bits
  · exact .admininstr_case_13 _ _ (unsigned_num_wf .I32 _ amount.isLt)
  · exact .admininstr_case_29 _ _ integerShape (.vshiftop__case_0 _ _ _ _ rfl)
  · exact const_wf result
  · exact shapeWf
  · exact integerShape
  · exact unsigned_wf_of_lt 32 _ amount.isLt
end Itasca.Runtime.Spec.Simd

end

end

/-! ## Widen -/

section

/-!
Source-rule algebra for widening lane arithmetic. Lane/list calculations establish the generated source operation and its reduction step, consumed by source-machine and interpreter correspondence proofs.
-/

/-! ## Simd Widen -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

def extendBits (signed : Bool) {width : Nat} (output : Nat) (bits : BitVec width) : BitVec output :=
  if signed then bits.signExtend output else bits.setWidth output

def widenBits (multiply signed : Bool) {width : Nat} (a b : BitVec width) : BitVec (width*2) :=
  if multiply then extendBits signed (width*2) a * extendBits signed (width*2) b
  else extendBits signed (width*2) a

def pairwiseBits (signed : Bool) {width : Nat} (a b : BitVec width) : BitVec (width*2) :=
  extendBits signed (width*2) a + extendBits signed (width*2) b

theorem extend_bits_source {width : Nat} (output : Nat) (signed : Bool) (bits : BitVec width)
    (le : width ≤ output) :
    uN.mk_uN (extendBits signed output bits).toNat =
      extend__ width output (if signed then .S else .U) (.mk_uN bits.toNat) := by
  cases signed
  · simp only [extendBits,Bool.false_eq_true,↓reduceIte,extend__]
    rw [BitVec.toNat_setWidth_of_le le]
  · simp only [extendBits,Bool.true_eq,↓reduceIte,extend__,proj_uN_0,Itasca.Runtime.Spec.signed_value_bitvec]
    rfl

inductive WidenWidth where | i8 | i16 | i32

def WidenWidth.input : WidenWidth → Jnn | .i8 => .I8 | .i16 => .I16 | .i32 => .I32

def WidenWidth.output : WidenWidth → Jnn | .i8 => .I16 | .i16 => .I32 | .i32 => .I64

def WidenWidth.width (ty : WidenWidth) : Nat := lsize (lanetype_Jnn ty.input)

def WidenWidth.count (ty : WidenWidth) : Nat := 64/ty.width

def widenHalf (high : Bool) : half := if high then .HIGH else .LOW

def widenSign (signed : Bool) : sx := if signed then .S else .U

def widenSource (ty : WidenWidth) (multiply high signed : Bool) : admininstr :=
  if multiply then
    .VEXTBINOP (.mk_ishape (shapeOf (lanetype_Jnn ty.output)))
      (.mk_ishape (shapeOf (lanetype_Jnn ty.input)))
      (.mk_vextbinop___0 ty.input (128/ty.width) ty.output ty.count (.EXTMUL (widenHalf high) (widenSign signed)))
  else
    .VCVTOP (shapeOf (lanetype_Jnn ty.output)) (shapeOf (lanetype_Jnn ty.input))
      (.mk_vcvtop___0 ty.input (128/ty.width) ty.output ty.count (.EXTEND (widenHalf high) (widenSign signed)))

inductive PairwiseWidth where | i8 | i16

def PairwiseWidth.widen : PairwiseWidth → WidenWidth | .i8 => .i8 | .i16 => .i16

def pairwiseSource (ty : PairwiseWidth) (signed : Bool) : admininstr :=
  .VEXTUNOP (.mk_ishape (shapeOf (lanetype_Jnn ty.widen.output)))
    (.mk_ishape (shapeOf (lanetype_Jnn ty.widen.input)))
    (.mk_vextunop___0 ty.widen.input (128/ty.widen.width) ty.widen.output ty.widen.count (.EXTADD_PAIRWISE (widenSign signed)))
end Itasca.Runtime.Spec.Simd

end

/-! ## Simd Widen Lists -/

section

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

end

/-! ## Simd Widen Multiply -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

theorem widen_multiply_source_wf (ty : WidenWidth) (high signed : Bool) :
    wf_admininstr (widenSource ty true high signed) := by
  apply wf_admininstr.admininstr_case_37
  · exact .ishape_case_0 _ _ (shape_of_wf _) rfl
  · exact .ishape_case_0 _ _ (shape_of_wf _) rfl
  · apply wf_vextbinop__.vextbinop___case_0
    · apply wf_vextbinop__Jnn_1_M_1_Jnn_2_M_2.vextbinop__Jnn_1_M_1_Jnn_2_M_2_case_0
      cases ty <;> decide
    · rfl
    · cases ty <;> rfl

theorem widen_multiply_vector (ty : WidenWidth) (high signed : Bool) (x y : BitVec 128) :
    fun_vextbinop__ (.mk_ishape (shapeOf (lanetype_Jnn ty.input)))
      (.mk_ishape (shapeOf (lanetype_Jnn ty.output)))
      (.mk_vextbinop___0 ty.input (128/ty.width) ty.output ty.count (.EXTMUL (widenHalf high) (widenSign signed)))
      (.mk_uN x.toNat) (.mk_uN y.toNat) (some (widenResult ty true high signed x y)) := by
  cases ty with
  | i8 =>
    apply fun_vextbinop__.fun_vextbinop___case_14 16 8 (widenHalf high) (widenSign signed)
      (.mk_uN x.toNat) (.mk_uN y.toNat) 16 8
      (widenInputs .i8 high x) (widenInputs .i8 high y) (widenResult .i8 true high signed x y)
      (widenWords .i8 true high signed x y) (widenWords .i8 true high signed x y)
    · simp [widenWords,widenInputs]
    · simp [widenWords,widenInputs]
    · exact widen_inputs_nonempty .i8 high x
    · exact widen_inputs_nonempty .i8 high y
    · exact widen_multiply_relation .i8 high signed x y
    · simp [widenWords,widenInputs]
    · simp [widenWords,widenInputs]
    · exact widen_inputs_nonempty .i8 high x
    · exact widen_inputs_nonempty .i8 high y
    · exact widen_multiply_relation .i8 high signed x y
    · exact widen_selected .i8 high x
    · exact widen_selected .i8 high y
    · rfl
    · exact shape_of_wf _
    · exact shape_of_wf _
    · exact widen_words_wf .i8 true high signed x y
    · rfl
    · rfl
  | i16 =>
    apply fun_vextbinop__.fun_vextbinop___case_3 8 4 (widenHalf high) (widenSign signed)
      (.mk_uN x.toNat) (.mk_uN y.toNat) 8 4
      (widenInputs .i16 high x) (widenInputs .i16 high y) (widenResult .i16 true high signed x y)
      (widenWords .i16 true high signed x y) (widenWords .i16 true high signed x y)
    · simp [widenWords,widenInputs]
    · simp [widenWords,widenInputs]
    · exact widen_inputs_nonempty .i16 high x
    · exact widen_inputs_nonempty .i16 high y
    · exact widen_multiply_relation .i16 high signed x y
    · simp [widenWords,widenInputs]
    · simp [widenWords,widenInputs]
    · exact widen_inputs_nonempty .i16 high x
    · exact widen_inputs_nonempty .i16 high y
    · exact widen_multiply_relation .i16 high signed x y
    · exact widen_selected .i16 high x
    · exact widen_selected .i16 high y
    · rfl
    · exact shape_of_wf _
    · exact shape_of_wf _
    · exact widen_words_wf .i16 true high signed x y
    · rfl
    · rfl
  | i32 =>
    apply fun_vextbinop__.fun_vextbinop___case_4 4 2 (widenHalf high) (widenSign signed)
      (.mk_uN x.toNat) (.mk_uN y.toNat) 4 2
      (widenInputs .i32 high x) (widenInputs .i32 high y) (widenResult .i32 true high signed x y)
      (widenWords .i32 true high signed x y) (widenWords .i32 true high signed x y)
    · simp [widenWords,widenInputs]
    · simp [widenWords,widenInputs]
    · exact widen_inputs_nonempty .i32 high x
    · exact widen_inputs_nonempty .i32 high y
    · exact widen_multiply_relation .i32 high signed x y
    · simp [widenWords,widenInputs]
    · simp [widenWords,widenInputs]
    · exact widen_inputs_nonempty .i32 high x
    · exact widen_inputs_nonempty .i32 high y
    · exact widen_multiply_relation .i32 high signed x y
    · exact widen_selected .i32 high x
    · exact widen_selected .i32 high y
    · rfl
    · exact shape_of_wf _
    · exact shape_of_wf _
    · exact widen_words_wf .i32 true high signed x y
    · rfl
    · rfl

theorem widen_multiply_step (ty : WidenWidth) (high signed : Bool) (x y result : BitVec 128)
    (packed : uN.mk_uN result.toNat = widenResult ty true high signed x y) :
    Step_pure [.VCONST .V128 (.mk_uN x.toNat),.VCONST .V128 (.mk_uN y.toNat),widenSource ty true high signed]
      [.VCONST .V128 (.mk_uN result.toNat)] := by
  apply Step_pure.vextbinop _ _ _ _ _ _ (some (.mk_uN result.toNat))
  · rw [packed]; exact widen_multiply_vector ty high signed x y
  · simp
  · rfl
  · exact const_wf x
  · exact const_wf y
  · exact widen_multiply_source_wf ty high signed
  · exact const_wf result
end Itasca.Runtime.Spec.Simd

end

end

/-! ## Choices -/

section

/-!
Set-product membership for permitted SIMD source outcomes.

Main declarations: `mem_setproduct2` and `mem_setproduct_map`. A direct consumer is `Spec.Simd.ConvertInteger`.
-/

namespace Itasca.Runtime.Spec.Simd

theorem mem_setproduct2 {A : Type} (head : A) (tail : List A) (tails : List (List A))
    (member : tail ∈ tails) : head::tail ∈ setproduct2_ A head tails := by
  induction tails with
  | nil => simp at member
  | cons first rest ih =>
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · simp [setproduct2_]
    · exact List.mem_append_right _ (ih member)

theorem mem_setproduct1 {A : Type} (head : A) (tail : List A) (heads : List A) (tails : List (List A))
    (headMember : head ∈ heads) (tailMember : tail ∈ tails) :
    head::tail ∈ setproduct1_ A heads tails := by
  induction heads with
  | nil => simp at headMember
  | cons first rest ih =>
    simp only [List.mem_cons] at headMember
    rcases headMember with rfl | member
    · exact List.mem_append_left _ (mem_setproduct2 _ _ _ tailMember)
    · exact List.mem_append_right _ (ih member)

theorem mem_setproduct_map {I A : Type} (items : List I) (choices : I → List A) (selected : I → A)
    (each : ∀ i ∈ items, selected i ∈ choices i) :
    items.map selected ∈ setproduct_ A (items.map choices) := by
  induction items with
  | nil => simp [setproduct_]
  | cons head tail ih =>
    apply mem_setproduct1
    · exact each head (by simp)
    · exact ih (by intro i member; exact each i (by simp [member]))

end Itasca.Runtime.Spec.Simd

end

/-! ## CompareFloat -/

section

/-!
Floating-point SIMD comparison and its lane-mask source step. This preserves the generated floating-point comparison relation used by interpreter correspondence.
-/

/-! ## Simd Compare Float -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins SpecExt.Builtins.Float

def floatComparisonBool (width : Nat) (op : vrelop_Fnn_N) (a b : fN) : Bool :=
  match op with
  | .EQ => equal width a b
  | .NE => !equal width a b
  | .LT => less width a b
  | .GT => less width b a
  | .LE => less width a b || equal width a b
  | .GE => less width b a || equal width b a

def floatComparisonValue (width : Nat) (op : vrelop_Fnn_N) (a b : fN) : uN :=
  match op with
  | .EQ => feq_ width a b
  | .NE => fne_ width a b
  | .LT => flt_ width a b
  | .GT => fgt_ width a b
  | .LE => fle_ width a b
  | .GE => fge_ width a b

theorem float_comparison_value (width : Nat) (op : vrelop_Fnn_N) (a b : fN) :
    floatComparisonValue width op a b = .mk_uN (nat_of_bool (floatComparisonBool width op a b)) := by
  cases op
  · cases h : equal width a b <;> simp only [floatComparisonValue,floatComparisonBool,feq_,fne_,flt_,fgt_,fle_,fge_,h,nat_of_bool,Bool.not_false,Bool.not_true,ite_true,Bool.false_eq_true,ite_false]
  · cases h : equal width a b <;> simp only [floatComparisonValue,floatComparisonBool,feq_,fne_,flt_,fgt_,fle_,fge_,h,nat_of_bool,Bool.not_false,Bool.not_true,ite_true,Bool.false_eq_true,ite_false]
  · cases h : less width a b <;> simp only [floatComparisonValue,floatComparisonBool,feq_,fne_,flt_,fgt_,fle_,fge_,h,nat_of_bool,Bool.not_false,Bool.not_true,ite_true,Bool.false_eq_true,ite_false]
  · cases h : less width b a <;> simp only [floatComparisonValue,floatComparisonBool,feq_,fne_,flt_,fgt_,fle_,fge_,h,nat_of_bool,Bool.not_false,Bool.not_true,ite_true,Bool.false_eq_true,ite_false]
  · cases h : less width a b || equal width a b <;> simp only [floatComparisonValue,floatComparisonBool,feq_,fne_,flt_,fgt_,fle_,fge_,h,nat_of_bool,Bool.not_false,Bool.not_true,ite_true,Bool.false_eq_true,ite_false]
  · cases h : less width b a || equal width b a <;> simp only [floatComparisonValue,floatComparisonBool,feq_,fne_,flt_,fgt_,fle_,fge_,h,nat_of_bool,Bool.not_false,Bool.not_true,ite_true,Bool.false_eq_true,ite_false]

def floatCompareSource (ty : Fnn) (op : vrelop_Fnn_N) : vrelop_ :=
  .mk_vrelop__1 ty (128/lsize (lanetype_Fnn ty)) op

def floatCompareInteger (ty : Fnn) : Inn := match ty with | .F32 => .I32 | .F64 => .I64

theorem float_compare_source_wf (ty : Fnn) (op : vrelop_Fnn_N) :
    wf_vrelop_ (shapeOf (lanetype_Fnn ty)) (floatCompareSource ty op) := by
  cases ty <;> cases op <;> constructor <;> constructor <;>
    simp_all [lsizenn,lsize,size,psize,lanetype_Fnn,valtype_numtype]

end Itasca.Runtime.Spec.Simd

end

/-! ## Simd Compare Float Lists -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

theorem forall2_map {I A B : Type} (items : List I) (f : I → A) (g : I → B)
    (P : A → B → Prop) (each : ∀ i ∈ items, P (f i) (g i)) :
    Forall₂ P (items.map f) (items.map g) := by
  induction items with
  | nil => simp [Forall₂]
  | cons head tail ih =>
    have atHead := each head (by simp)
    have atTail := ih (by intro i member; exact each i (by simp [member]))
    simpa [Forall₂] using And.intro atHead atTail

theorem map2_map {I A B C : Type} (items : List I) (f : I → A) (g : I → B) (h : A → B → C) :
    Map₂ h (items.map f) (items.map g) = items.map (fun i => h (f i) (g i)) := by
  induction items with
  | nil => rfl
  | cons head tail ih => simpa [Map₂,List.ap] using congrArg (List.cons (h (f head) (g head))) ih

def floatComparisonMasks (ty : Fnn) (op : vrelop_Fnn_N) (x y : BitVec 128) : List uN :=
  Map₂ (fun a b => extend__ 1 (lsize (lanetype_Fnn ty)) .S
    (.mk_uN (proj_uN_0 (floatComparisonValue (lsize (lanetype_Fnn ty)) op
      (Option.get! (proj_lane__1 a)) (Option.get! (proj_lane__1 b))))))
    (lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN x.toNat))
    (lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN y.toNat))

theorem float_lanes_nonempty (ty : Fnn) (x : BitVec 128) :
    Forall (fun lane => proj_lane__1 lane ≠ none) (lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN x.toNat)) := by
  rw [lanes_map_words]
  intro lane member
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
  cases ty <;> simp [laneOfBits,lanetype_Fnn,proj_lane__1]

theorem float_comparison_answers_wf (ty : Fnn) (op : vrelop_Fnn_N) (x y : BitVec 128) :
    Forall₂ (fun a b => wf_uN 1 (.mk_uN (proj_uN_0
      (floatComparisonValue (lsize (lanetype_Fnn ty)) op
        (Option.get! (proj_lane__1 a)) (Option.get! (proj_lane__1 b))))))
      (lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN x.toNat))
      (lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN y.toNat)) := by
  intro pair member
  rw [float_comparison_value]
  cases floatComparisonBool (lsize (lanetype_Fnn ty)) op
    (Option.get! (proj_lane__1 pair.1)) (Option.get! (proj_lane__1 pair.2)) <;>
      apply wf_uN.uN_case_0 <;> decide

theorem float_comparison_masks_wf (ty : Fnn) (op : vrelop_Fnn_N) (x y : BitVec 128) :
    Forall (fun mask => wf_lane_ (lanetype_Inn (floatCompareInteger ty))
      (.mk_lane__0 (Jnn_Inn (floatCompareInteger ty)) (.mk_uN (proj_uN_0 mask))))
      (floatComparisonMasks ty op x y) := by
  unfold floatComparisonMasks
  rw [lanes_map_words,lanes_map_words,map2_map]
  intro mask member
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
  rw [float_comparison_value]
  simp only [proj_uN_0,boolean_extend]
  cases ty <;> constructor
  all_goals first | rfl | exact unsigned_wf_of_lt _ _ (BitVec.isLt _)

end Itasca.Runtime.Spec.Simd

end

/-! ## Simd Compare Float Relation -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

def floatComparisonResult (ty : Fnn) (op : vrelop_Fnn_N) (x y : BitVec 128) : uN :=
  inv_lanes_ (shapeOf (lanetype_Inn (floatCompareInteger ty)))
    (Map (fun mask => lane_.mk_lane__0 (Jnn_Inn (floatCompareInteger ty)) (.mk_uN (proj_uN_0 mask)))
      (floatComparisonMasks ty op x y))

theorem float_comparison_relation (ty : Fnn) (op : vrelop_Fnn_N) (x y : BitVec 128) :
    fun_vrelop_ (shapeOf (lanetype_Fnn ty)) (floatCompareSource ty op)
      (.mk_uN x.toNat) (.mk_uN y.toNat) (some (floatComparisonResult ty op x y)) := by
  have lenXY : (lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN x.toNat)).length =
      (lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN y.toNat)).length := by
    rw [lanes_map_words,lanes_map_words,List.length_map,List.length_map]
  have nonX := float_lanes_nonempty ty x
  have nonY := float_lanes_nonempty ty y
  have maskWf := float_comparison_masks_wf ty op x y
  have answerWf := float_comparison_answers_wf ty op x y
  have shapeWf := shape_of_wf (lanetype_Fnn ty)
  have resultShapeWf := shape_of_wf (lanetype_Inn (floatCompareInteger ty))
  cases ty <;> cases op
  · apply fun_vrelop_.fun_vrelop__case_24 (v_Inn := .I32) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := floatComparisonMasks .F32 .EQ x y)
    all_goals first | rfl | exact nonX | exact nonY | exact maskWf | exact answerWf | exact shapeWf | exact resultShapeWf | exact lenXY | decide
  · apply fun_vrelop_.fun_vrelop__case_26 (v_Inn := .I32) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := floatComparisonMasks .F32 .NE x y)
    all_goals first | rfl | exact nonX | exact nonY | exact maskWf | exact answerWf | exact shapeWf | exact resultShapeWf | exact lenXY | decide
  · apply fun_vrelop_.fun_vrelop__case_28 (v_Inn := .I32) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := floatComparisonMasks .F32 .LT x y)
    all_goals first | rfl | exact nonX | exact nonY | exact maskWf | exact answerWf | exact shapeWf | exact resultShapeWf | exact lenXY | decide
  · apply fun_vrelop_.fun_vrelop__case_30 (v_Inn := .I32) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := floatComparisonMasks .F32 .GT x y)
    all_goals first | rfl | exact nonX | exact nonY | exact maskWf | exact answerWf | exact shapeWf | exact resultShapeWf | exact lenXY | decide
  · apply fun_vrelop_.fun_vrelop__case_32 (v_Inn := .I32) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := floatComparisonMasks .F32 .LE x y)
    all_goals first | rfl | exact nonX | exact nonY | exact maskWf | exact answerWf | exact shapeWf | exact resultShapeWf | exact lenXY | decide
  · apply fun_vrelop_.fun_vrelop__case_34 (v_Inn := .I32) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := floatComparisonMasks .F32 .GE x y)
    all_goals first | rfl | exact nonX | exact nonY | exact maskWf | exact answerWf | exact shapeWf | exact resultShapeWf | exact lenXY | decide
  · apply fun_vrelop_.fun_vrelop__case_25 (v_Inn := .I64) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := floatComparisonMasks .F64 .EQ x y)
    all_goals first | rfl | exact nonX | exact nonY | exact maskWf | exact answerWf | exact shapeWf | exact resultShapeWf | exact lenXY | decide
  · apply fun_vrelop_.fun_vrelop__case_27 (v_Inn := .I64) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := floatComparisonMasks .F64 .NE x y)
    all_goals first | rfl | exact nonX | exact nonY | exact maskWf | exact answerWf | exact shapeWf | exact resultShapeWf | exact lenXY | decide
  · apply fun_vrelop_.fun_vrelop__case_29 (v_Inn := .I64) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := floatComparisonMasks .F64 .LT x y)
    all_goals first | rfl | exact nonX | exact nonY | exact maskWf | exact answerWf | exact shapeWf | exact resultShapeWf | exact lenXY | decide
  · apply fun_vrelop_.fun_vrelop__case_31 (v_Inn := .I64) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := floatComparisonMasks .F64 .GT x y)
    all_goals first | rfl | exact nonX | exact nonY | exact maskWf | exact answerWf | exact shapeWf | exact resultShapeWf | exact lenXY | decide
  · apply fun_vrelop_.fun_vrelop__case_33 (v_Inn := .I64) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := floatComparisonMasks .F64 .LE x y)
    all_goals first | rfl | exact nonX | exact nonY | exact maskWf | exact answerWf | exact shapeWf | exact resultShapeWf | exact lenXY | decide
  · apply fun_vrelop_.fun_vrelop__case_35 (v_Inn := .I64) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat)) (lane_3_lst := floatComparisonMasks .F64 .GE x y)
    all_goals first | rfl | exact nonX | exact nonY | exact maskWf | exact answerWf | exact shapeWf | exact resultShapeWf | exact lenXY | decide

end Itasca.Runtime.Spec.Simd

end

/-! ## Simd Compare Float Step -/

section

namespace Itasca.Runtime.Spec.Simd

theorem float_comparison_step (ty : Fnn) (op : vrelop_Fnn_N) (x y result : BitVec 128)
    (packed : uN.mk_uN result.toNat = floatComparisonResult ty op x y) :
    Step_pure [.VCONST .V128 (.mk_uN x.toNat),.VCONST .V128 (.mk_uN y.toNat),
      .VRELOP (shapeOf (lanetype_Fnn ty)) (floatCompareSource ty op)]
      [.VCONST .V128 (.mk_uN result.toNat)] := by
  apply Step_pure.vrelop _ _ _ _ _ (some (.mk_uN result.toNat))
  · rw [packed]
    exact float_comparison_relation ty op x y
  · simp
  · rfl
  · exact const_wf x
  · exact const_wf y
  · exact .admininstr_case_28 _ _ (shape_of_wf _) (float_compare_source_wf ty op)
  · exact const_wf result

end Itasca.Runtime.Spec.Simd

end

end

/-! ## ExtendLanes -/

section

/-!
Lane extension and its generated source relation. The signed/unsigned lane bounds feed SIMD source and interpreter proofs.
-/

/-! ## Simd Extend Lanes -/

section

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
  · exact shape_of_wf _
  · exact shape_of_wf _
  · apply wf_vcvtop__.vcvtop___case_0
    · apply wf_vcvtop__Jnn_1_M_1_Jnn_2_M_2.vcvtop__Jnn_1_M_1_Jnn_2_M_2_case_0
      cases ty <;> decide
    · rfl
    · cases ty <;> rfl
end Itasca.Runtime.Spec.Simd

end

/-! ## Simd Extend Source -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

theorem extend_vector (ty : WidenWidth) (high signed : Bool) (x result : BitVec 128)
    (packed : uN.mk_uN result.toNat = widenResult ty false high signed x x) :
    fun_vcvtop__ (shapeOf (lanetype_Jnn ty.input)) (shapeOf (lanetype_Jnn ty.output))
      (extendOperation ty high signed) (.mk_uN x.toNat) (some (.mk_uN result.toNat)) := by
  let choices := setproduct_ lane_ (Map (fun choice => Option.get! choice) (extendChoices ty high signed x))
  have chosen : uN.mk_uN result.toNat ∈ Map (inv_lanes_ (shapeOf (lanetype_Jnn ty.output))) choices :=
    List.mem_map.mpr ⟨_,extend_chosen ty high signed x,packed.symm⟩
  have targetShape : shapeOf (lanetype_Jnn ty.output) = .X (lanetype_Jnn ty.output) (.mk_dim ty.count) := by cases ty <;> rfl
  rw [targetShape] at chosen ⊢
  apply fun_vcvtop__.fun_vcvtop___case_1 (lanetype_Jnn ty.input) (128/ty.width)
    (lanetype_Jnn ty.output) ty.count (extendOperation ty high signed)
    (.mk_uN x.toNat) (.mk_uN result.toNat) (widenHalf high)
    (widenInputs ty high x) choices (extendChoices ty high signed x) (some (some (widenHalf high)))
  · simp [extendChoices,widenWords,widenInputs]
  · rw [←targetShape]; exact extend_choices_relation ty high signed x
  · rw [←targetShape]; exact extend_halfop ty high signed
  · simp
  · rfl
  · exact widen_selected ty high x
  · exact extend_choices_nonempty ty high signed x
  · rfl
  · exact List.length_pos_of_mem chosen
  · exact List.contains_iff_mem.mpr chosen
  · exact unsigned_wf_of_lt 128 result.toNat result.isLt
  · exact shape_of_wf _
  · rw [←targetShape];exact shape_of_wf _

theorem extend_step (ty : WidenWidth) (high signed : Bool) (x result : BitVec 128)
    (packed : uN.mk_uN result.toNat = widenResult ty false high signed x x) :
    Step_pure [.VCONST .V128 (.mk_uN x.toNat),widenSource ty false high signed]
      [.VCONST .V128 (.mk_uN result.toNat)] := by
  apply Step_pure.vcvtop _ _ _ _ _ (some (.mk_uN result.toNat))
  · exact extend_vector ty high signed x result packed
  · simp
  · rfl
  · exact const_wf x
  · exact extend_source_wf ty high signed
  · exact const_wf result
end Itasca.Runtime.Spec.Simd

end

end
