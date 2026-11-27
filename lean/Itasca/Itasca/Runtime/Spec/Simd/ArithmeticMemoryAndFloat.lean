import Itasca.Runtime.Spec.Simd.LaneOperations
import Itasca.Runtime.Spec.TypingAndNumericOperations
import WebAssembly.Builtins.IntegerRepresentation
import WebAssembly.Builtins.Float.Comparison
import Itasca.Runtime.Spec.PrimitiveOperations
import WebAssembly.Builtins.Float.Representation

open WebAssembly

/-!
Proofs for Runtime / Spec / Simd.

This module collects ArithmeticAndExtension, MemoryAndFloatOperations, ArithmeticAndReductions.
Each section documents its contracts and consumers.
-/

/-! ## ArithmeticAndExtension -/

section

/-!
# SIMD arithmetic and lane extension

Integer arithmetic, shifts, widening and float comparisons retain source operation
relations and permitted choices. Lane-extension facts compose those representation and
generated-step arguments.
-/

/-! ## IntegerArithmetic -/

section

/-!
Source-rule algebra for wrapping integer lane arithmetic. Lane/list calculations establish the generated source operation and its reduction step, consumed by source-machine and interpreter correspondence proofs.
-/

/-! ## Simd Integer Arithmetic -/

section

namespace Itasca.Spec.Simd

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

end Itasca.Spec.Simd

end

/-! ## Simd Integer Arithmetic Shape -/

section

namespace Itasca.Spec.Simd

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

end Itasca.Spec.Simd

end

/-! ## Simd Integer Arithmetic Lists -/

section

namespace Itasca.Spec.Simd
open WebAssembly.Builtins

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

end Itasca.Spec.Simd

end

/-! ## Simd Integer Arithmetic Source -/

section

namespace Itasca.Spec.Simd
open WebAssembly.Builtins

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

end Itasca.Spec.Simd

end

/-! ## Simd Integer Arithmetic Step -/

section

namespace Itasca.Spec.Simd

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

end Itasca.Spec.Simd

end

end

/-! ## Shift -/

section

/-!
Source-rule algebra for lane shifts. Lane/list calculations establish the generated source operation and its reduction step, consumed by source-machine and interpreter correspondence proofs.
-/

/-! ## Simd Shift -/

section

namespace Itasca.Spec.Simd
open WebAssembly.Builtins

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
end Itasca.Spec.Simd

end

/-! ## Simd Shift Source -/

section

namespace Itasca.Spec.Simd
open WebAssembly.Builtins

def vectorLane (ty : lanetype) (bits : BitVec 128) (j : Nat) : BitVec (lsize ty) :=
  (bits >>> (lsize ty*j)).setWidth (lsize ty)

def shiftLaneValues (ty : Jnn) (kind : ShiftKind) (bits : BitVec 128) (amount : Nat) : List lane_ :=
  (List.range (128/lsize (lanetype_Jnn ty))).map (fun j =>
    laneOfBits (lanetype_Jnn ty) (shiftBits kind (vectorLane (lanetype_Jnn ty) bits j)
      (amount % lsize (lanetype_Jnn ty))).toNat)

theorem vector_lanes (ty : lanetype) (bits : BitVec 128) :
    lanes_ (shapeOf ty) (.mk_uN bits.toNat) =
      (List.range (128/lsize ty)).map (fun j => laneOfBits ty (vectorLane ty bits j).toNat) := by
  apply unpack_lanes_eq_map
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
end Itasca.Spec.Simd

end

end

/-! ## Widen -/

section

/-!
Source-rule algebra for widening lane arithmetic. Lane/list calculations establish the generated source operation and its reduction step, consumed by source-machine and interpreter correspondence proofs.
-/

/-! ## Simd Widen -/

section

namespace Itasca.Spec.Simd
open WebAssembly.Builtins

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
  · simp only [extendBits,Bool.true_eq,↓reduceIte,extend__,proj_uN_0,Itasca.Spec.signed_value_bitvec]
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
end Itasca.Spec.Simd

end

/-! ## Simd Widen Lists -/

section

namespace Itasca.Spec.Simd
open WebAssembly.Builtins

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
end Itasca.Spec.Simd

end

/-! ## Simd Widen Multiply -/

section

namespace Itasca.Spec.Simd
open WebAssembly.Builtins

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
end Itasca.Spec.Simd

end

end

/-! ## Choices -/

section

/-!
Set-product membership for permitted SIMD source outcomes.

Main declarations: `mem_setproduct2` and `mem_setproduct_map`.
-/

namespace Itasca.Spec.Simd

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

end Itasca.Spec.Simd

end

/-! ## CompareFloat -/

section

/-!
Floating-point SIMD comparison and its lane-mask source step. This preserves the generated floating-point comparison relation used by interpreter correspondence.
-/

/-! ## Simd Compare Float -/

section

namespace Itasca.Spec.Simd
open WebAssembly.Builtins WebAssembly.Builtins.Float

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

end Itasca.Spec.Simd

end

/-! ## Simd Compare Float Lists -/

section

namespace Itasca.Spec.Simd
open WebAssembly.Builtins

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
  | cons head tail ih => simpa [Map₂,WebAssembly.List.ap] using congrArg (List.cons (h (f head) (g head))) ih

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

end Itasca.Spec.Simd

end

/-! ## Simd Compare Float Relation -/

section

namespace Itasca.Spec.Simd
open WebAssembly.Builtins

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

end Itasca.Spec.Simd

end

/-! ## Simd Compare Float Step -/

section

namespace Itasca.Spec.Simd

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

end Itasca.Spec.Simd

end

end

/-! ## ExtendLanes -/

section

/-!
Lane extension and its generated source relation. The signed/unsigned lane bounds feed SIMD source and interpreter proofs.
-/

/-! ## Simd Extend Lanes -/

section

namespace Itasca.Spec.Simd
open WebAssembly.Builtins

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
end Itasca.Spec.Simd

end

/-! ## Simd Extend Source -/

section

namespace Itasca.Spec.Simd
open WebAssembly.Builtins

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
end Itasca.Spec.Simd

end

end

end

/-! ## MemoryAndFloatOperations -/

section

/-!
# Memory And Float Operations

SIMD memory and floating-point operations satisfy their source lane and value rules.
-/

/-! ## MemoryLoad -/

section

/-!
The source result relation for full-vector loads.

Main declarations: `fullLoadResult`.
-/

namespace Itasca.Spec.Simd
open WebAssembly WebAssembly.Builtins

def fullLoadResult (bytes : List byte) (start : Nat) : List admininstr :=
  if start + 16 ≤ bytes.length then [.VCONST .V128 (inv_vbytes_ .V128 ((bytes.drop start).take 16))]
  else [.TRAP]

theorem vector_bytes_roundtrip (bytes : List byte) (valid : Forall wf_byte bytes)
    (sized : bytes.length = 16) : vbytes_ .V128 (inv_vbytes_ .V128 bytes) = bytes := by
  have roundtrip := integer_bytes_of_bytes bytes valid
  simpa [vbytes_,inv_vbytes_,ibytes_,inv_ibytes_,vsize,proj_uN_0,sized] using roundtrip

theorem vector_bytes_wf (bytes : List byte) (valid : Forall wf_byte bytes)
    (sized : bytes.length = 16) : wf_admininstr (.VCONST .V128 (inv_vbytes_ .V128 bytes)) := by
  have bounded := integer_of_bytes_bound bytes valid
  apply wf_admininstr.admininstr_case_20 _ _ (by decide)
  apply unsigned_wf_of_lt
  rw [sized] at bounded
  simpa [inv_vbytes_,inv_ibytes_,vsize,size,valtype_vectype] using bounded

theorem full_load_step (s : store) (f : frame) (argument : memarg) (address : Nat)
    (storeWf : wf_store s) (frameWf : wf_frame f) (addressBound : address < 2^32)
    (operationWf : wf_admininstr (.VLOAD .V128 none argument))
    (bytesWf : Forall wf_byte (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES) :
    StepH ⟨⟨s,f⟩,[Segment.i32 address,.VLOAD .V128 none argument]⟩ []
      ⟨⟨s,f⟩,fullLoadResult (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES
        (address + proj_uN_0 argument.OFFSET)⟩ := by
  have byteCount : rat_to_nat ((Option.get! (size valtype.V128) : Rat) / 8) = 16 := by
    norm_num [size,rat_to_nat]
    rfl
  have input := wf_config_make storeWf frameWf (show Forall wf_admininstr [Segment.i32 address,.VLOAD .V128 none argument] from by
    intro instruction member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact Segment.i32_wf address addressBound
    · exact operationWf)
  unfold fullLoadResult
  split
  · rename_i fits
    let bytes := (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES
    let start := address + proj_uN_0 argument.OFFSET
    have payloadWf : Forall wf_byte ((bytes.drop start).take 16) := by
      intro byte member
      exact bytesWf byte (List.mem_of_mem_drop (List.mem_of_mem_take member))
    have payloadLength : ((bytes.drop start).take 16).length = 16 := by
      simp only [List.length_take,List.length_drop]
      dsimp only [bytes,start]
      omega
    have valueWf := vector_bytes_wf _ payloadWf payloadLength
    have output := wf_config_make storeWf frameWf (show Forall wf_admininstr
      [.VCONST .V128 (inv_vbytes_ .V128 ((bytes.drop start).take 16))] from by
      simpa [Forall] using valueWf)
    apply StepH.step
    apply Step.read _ _ _ ?_ input output
    apply Step_read.vload_val
    · simp [proj_num__0]
    · decide
    · simpa only [byteCount,proj_num__0,proj_uN_0,Option.get!_some,bytes,start] using
        vector_bytes_roundtrip _ payloadWf payloadLength
    · exact input
    · exact valueWf
    · exact Segment.index_wf 0 (by norm_num)
  · rename_i outside
    apply StepH.step
    apply Step.read _ _ _ ?_ input (wf_config_trap storeWf frameWf)
    apply Step_read.vload_oob
    · simp [proj_num__0]
    · decide
    · simpa only [byteCount,proj_num__0,proj_uN_0,Option.get!_some] using Nat.lt_of_not_ge outside
    · exact input
    · exact .admininstr_case_73
    · exact Segment.index_wf 0 (by norm_num)
end Itasca.Spec.Simd

end

/-! ## MemoryChunks -/

section

/-!
Byte slices used by vector memory loads.

Main declarations: `integer_bytes_take` and `integer_bytes_chunk`.
-/

namespace Itasca.Spec.Simd
open WebAssembly.Builtins

theorem integer_bytes_take (count total value : Nat) (le : count ≤ total) :
    (integerBytes total value).take count = integerBytes count value := by
  induction count generalizing total value with
  | zero => simp [integerBytes]
  | succ count ih =>
    cases total with
    | zero => omega
    | succ total =>
      simpa only [integerBytes,List.take_succ_cons] using
        congrArg (List.cons (.mk_byte (value%256))) (ih total (value/256) (by omega))

theorem integer_bytes_drop (start total value : Nat) (le : start ≤ total) :
    (integerBytes total value).drop start = integerBytes (total-start) (value/256^start) := by
  induction start generalizing total value with
  | zero => simp
  | succ start ih =>
    cases total with
    | zero => omega
    | succ total =>
      simp only [integerBytes,List.drop_succ_cons]
      rw [ih total (value/256) (by omega)]
      simp only [Nat.div_div_eq_div_mul,Nat.pow_succ,Nat.mul_comm 256,Nat.add_sub_add_right]

theorem integer_bytes_chunk (width index value : Nat) (fit : index*width+width ≤ 8) :
    (integerBytes 8 value |>.drop (index*width) |>.take width) =
      integerBytes width ((value/256^(index*width))%256^width) := by
  rw [integer_bytes_drop _ _ _ (by omega),integer_bytes_take _ _ _ (by omega),integer_bytes_mod]
end Itasca.Spec.Simd

end

/-! ## MemoryLane -/

section

/-!
Byte widths and source behavior of vector lane loads.

Main declarations: `lane_byte_count` and `lane_load_trap`.
-/

namespace Itasca.Spec.Simd
open WebAssembly WebAssembly.Builtins

theorem lane_byte_count (ty : Jnn) :
    rat_to_nat ((lsize (lanetype_Jnn ty) : Rat)/8) = lsize (lanetype_Jnn ty)/8 := by
  cases ty <;> norm_num [lsize,lanetype_Jnn,rat_to_nat,size,valtype_numtype,psize] <;> rfl

theorem lane_dimension (ty : Jnn) :
    ((128/lsize (lanetype_Jnn ty) : Nat) : Rat) = (128 : Rat)/lsize (lanetype_Jnn ty) := by
  cases ty <;> norm_num [lsize,lanetype_Jnn,size,valtype_numtype,psize]

theorem lane_load_value (ty : Jnn) (s : store) (f : frame) (argument : memarg) (address index : Nat)
    (before result : BitVec 128) (word : BitVec (lsize (lanetype_Jnn ty)))
    (storeWf : wf_store s) (frameWf : wf_frame f) (addressBound : address < 2^32)
    (operationWf : wf_admininstr (.VLOAD_LANE .V128 (.mk_sz (lsize (lanetype_Jnn ty))) argument (.mk_uN index)))
    (bytesEq : ibytes_ (lsize (lanetype_Jnn ty)) (.mk_uN word.toNat) =
      ((fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.drop (address+proj_uN_0 argument.OFFSET)).take (lsize (lanetype_Jnn ty)/8))
    (packed : uN.mk_uN result.toNat = inv_lanes_ (shapeOf (lanetype_Jnn ty))
      ((lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN before.toNat)).set index (.mk_lane__0 ty (.mk_uN word.toNat)))) :
    StepH ⟨⟨s,f⟩,[Segment.i32 address,.VCONST .V128 (.mk_uN before.toNat),
      .VLOAD_LANE .V128 (.mk_sz (lsize (lanetype_Jnn ty))) argument (.mk_uN index)]⟩ []
      ⟨⟨s,f⟩,[.VCONST .V128 (.mk_uN result.toNat)]⟩ := by
  have input := wf_config_make storeWf frameWf (show Forall wf_admininstr
      [Segment.i32 address,.VCONST .V128 (.mk_uN before.toNat),
        .VLOAD_LANE .V128 (.mk_sz (lsize (lanetype_Jnn ty))) argument (.mk_uN index)] from by
    intro instruction member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · exact Segment.i32_wf address addressBound
    · exact const_wf before
    · exact operationWf)
  have output := wf_config_make storeWf frameWf (show Forall wf_admininstr [.VCONST .V128 (.mk_uN result.toNat)] from by
    simpa [Forall] using const_wf result)
  apply StepH.step
  apply Step.read _ _ _ ?_ input output
  apply Step_read.vload_lane_val _ _ _ _ _ _ _ (.mk_uN word.toNat) ty (128/lsize (lanetype_Jnn ty))
  · simp [proj_num__0]
  · simpa only [lane_byte_count,proj_num__0,proj_uN_0,Option.get!_some] using bytesEq
  · cases ty <;> rfl
  · exact lane_dimension ty
  · simpa only [shapeOf,List.modify_eq_set,proj_uN_0] using packed
  · exact input
  · exact const_wf result
  · exact Segment.index_wf 0 (by norm_num)
  · exact shape_of_wf _
  · cases ty <;> exact lane_of_bits_wf _ word.toNat word.isLt

theorem lane_load_trap (ty : Jnn) (s : store) (f : frame) (argument : memarg) (address index : Nat)
    (before : BitVec 128) (storeWf : wf_store s) (frameWf : wf_frame f) (addressBound : address < 2^32)
    (operationWf : wf_admininstr (.VLOAD_LANE .V128 (.mk_sz (lsize (lanetype_Jnn ty))) argument (.mk_uN index)))
    (outside : (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length < address+proj_uN_0 argument.OFFSET+lsize (lanetype_Jnn ty)/8) :
    StepH ⟨⟨s,f⟩,[Segment.i32 address,.VCONST .V128 (.mk_uN before.toNat),
      .VLOAD_LANE .V128 (.mk_sz (lsize (lanetype_Jnn ty))) argument (.mk_uN index)]⟩ [] ⟨⟨s,f⟩,[.TRAP]⟩ := by
  have input := wf_config_make storeWf frameWf (show Forall wf_admininstr
      [Segment.i32 address,.VCONST .V128 (.mk_uN before.toNat),
        .VLOAD_LANE .V128 (.mk_sz (lsize (lanetype_Jnn ty))) argument (.mk_uN index)] from by
    intro instruction member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · exact Segment.i32_wf address addressBound
    · exact const_wf before
    · exact operationWf)
  apply StepH.step
  apply Step.read _ _ _ ?_ input (wf_config_trap storeWf frameWf)
  apply Step_read.vload_lane_oob
  · simp [proj_num__0]
  · simpa only [lane_byte_count,proj_num__0,proj_uN_0,Option.get!_some] using outside
  · exact input
  · exact .admininstr_case_73
  · exact Segment.index_wf 0 (by norm_num)
end Itasca.Spec.Simd

end

/-! ## MemoryExtend -/

section

/-!
The source operation for widening vector loads.

Main declarations: `memoryExtendSource`.
-/

namespace Itasca.Spec.Simd
open WebAssembly WebAssembly.Builtins

def memoryExtendSource (ty : WidenWidth) (signed : Bool) (argument : memarg) : admininstr :=
  .VLOAD .V128 (some (.SHAPEX_ (.mk_sz ty.width) ty.count (widenSign signed))) argument

theorem memory_extend_byte_count (ty : WidenWidth) : rat_to_nat ((ty.width : Rat)*(ty.count : Rat)/8) = 8 := by
  cases ty <;> norm_num [WidenWidth.width,WidenWidth.input,WidenWidth.count,lsize,lanetype_Jnn,size,valtype_numtype,psize,rat_to_nat] <;> rfl

theorem memory_extend_bytes (ty : WidenWidth) : rat_to_nat ((ty.width : Rat)/8) = ty.width/8 := by
  cases ty <;> norm_num [WidenWidth.width,WidenWidth.input,lsize,lanetype_Jnn,size,valtype_numtype,psize,rat_to_nat] <;> rfl

theorem memory_extend_offset (ty : WidenWidth) (j : Nat) : rat_to_nat ((j : Rat)*(ty.width : Rat)/8) = j*(ty.width/8) := by
  have eq : ((j*ty.width : Nat) : Rat)/8 = ((j*(ty.width/8) : Nat) : Rat) := by
    cases ty <;> norm_num [WidenWidth.width,WidenWidth.input,lsize,lanetype_Jnn,size,valtype_numtype,psize] <;> ring
  rw [←Nat.cast_mul,eq]
  simp only [rat_to_nat,Rat.num_natCast,Rat.den_natCast]
  generalize j*(ty.width/8) = n
  change ((n:Int).tdiv (1:Int)).toNat = n
  simp only [Int.tdiv_one,Int.toNat_natCast]

theorem extend_load_value (ty : WidenWidth) (signed : Bool) (s : store) (f : frame) (argument : memarg)
    (address : Nat) (loaded result : BitVec 128)
    (storeWf : wf_store s) (frameWf : wf_frame f) (addressBound : address < 2^32)
    (operationWf : wf_admininstr (memoryExtendSource ty signed argument))
    (bytesEq : ∀ j, j < ty.count → ibytes_ ty.width (.mk_uN (laneWord (lanetype_Jnn ty.input) loaded j).toNat) =
      ((fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.drop (address+proj_uN_0 argument.OFFSET+j*(ty.width/8))).take (ty.width/8))
    (packed : uN.mk_uN result.toNat = widenResult ty false false signed loaded loaded) :
    StepH ⟨⟨s,f⟩,[Segment.i32 address,memoryExtendSource ty signed argument]⟩ []
      ⟨⟨s,f⟩,[.VCONST .V128 (.mk_uN result.toNat)]⟩ := by
  have input := wf_config_make storeWf frameWf (show Forall wf_admininstr [Segment.i32 address,memoryExtendSource ty signed argument] from by
    intro instruction member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact Segment.i32_wf address addressBound
    · exact operationWf)
  have output := wf_config_make storeWf frameWf (show Forall wf_admininstr [.VCONST .V128 (.mk_uN result.toNat)] from by
    simpa [Forall] using const_wf result)
  apply StepH.step
  apply Step.read _ _ _ ?_ input output
  apply Step_read.vload_shape_val _ _ _ _ _ _ _ ((List.range ty.count).map
    (fun j => .mk_uN (laneWord (lanetype_Jnn ty.input) loaded j).toNat)) ty.output
  · intro j member;simp [proj_num__0]
  · have relation := forall2_map (List.range ty.count) id
      (fun j => uN.mk_uN (laneWord (lanetype_Jnn ty.input) loaded j).toNat)
      (fun j word => ibytes_ ty.width word =
        ((fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.drop (address+proj_uN_0 argument.OFFSET+j*(ty.width/8))).take (ty.width/8))
      (by
        intro j member
        simpa only [id_eq,memory_extend_bytes,memory_extend_offset,proj_num__0,proj_uN_0,Option.get!_some] using bytesEq j (List.mem_range.mp member))
    simpa only [List.map_id_fun,id_eq,memory_extend_bytes,memory_extend_offset,proj_num__0,proj_uN_0,Option.get!_some] using relation
  · intro word member
    obtain ⟨index,_,rfl⟩ := List.mem_map.mp member
    exact (laneWord (lanetype_Jnn ty.input) loaded index).isLt
  · cases ty <;> rfl
  · rw [packed]
    unfold widenResult widenWords Map
    simp only [List.map_map]
    congr 1
    · cases ty <;> rfl
    · apply List.map_congr_left
      intro j member
      simp only [widenBits,Bool.false_eq_true,↓reduceIte,Nat.add_zero]
      have ex := extend_bits_source (ty.width*2) signed (laneWord (lanetype_Jnn ty.input) loaded j) (by cases ty <;> decide)
      cases ty <;> exact congrArg (lane_.mk_lane__0 _) ex
  · exact input
  · exact const_wf result
  · exact Segment.index_wf 0 (by norm_num)
  · cases ty <;> exact shape_of_wf _
  · intro word member
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
    have ex := extend_bits_source (ty.width*2) signed (laneWord (lanetype_Jnn ty.input) loaded j) (by cases ty <;> decide)
    have bounded := unsigned_wf_of_lt (ty.width*2) (extendBits signed (ty.width*2) (laneWord (lanetype_Jnn ty.input) loaded j)).toNat (BitVec.isLt _)
    have wf : wf_uN (ty.width*2) (extend__ ty.width (ty.width*2) (widenSign signed)
        (.mk_uN (laneWord (lanetype_Jnn ty.input) loaded j).toNat)) := by
      change wf_uN (ty.width*2) (extend__ (lsize (lanetype_Jnn ty.input)) (ty.width*2) (if signed then .S else .U) _)
      rw [←ex];exact bounded
    cases ty <;> exact .lane__case_0 _ _ _ wf rfl
  · simp
end Itasca.Spec.Simd
namespace Itasca.Spec.Simd
open WebAssembly WebAssembly.Builtins

theorem extend_load_trap (ty : WidenWidth) (signed : Bool) (s : store) (f : frame) (argument : memarg)
    (address : Nat) (storeWf : wf_store s) (frameWf : wf_frame f) (addressBound : address < 2^32)
    (operationWf : wf_admininstr (memoryExtendSource ty signed argument))
    (outside : (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length < address+proj_uN_0 argument.OFFSET+8) :
    StepH ⟨⟨s,f⟩,[Segment.i32 address,memoryExtendSource ty signed argument]⟩ [] ⟨⟨s,f⟩,[.TRAP]⟩ := by
  have input := wf_config_make storeWf frameWf (show Forall wf_admininstr [Segment.i32 address,memoryExtendSource ty signed argument] from by
    intro instruction member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact Segment.i32_wf address addressBound
    · exact operationWf)
  apply StepH.step
  apply Step.read _ _ _ ?_ input (wf_config_trap storeWf frameWf)
  apply Step_read.vload_shape_oob
  · simp [proj_num__0]
  · simpa only [memory_extend_byte_count,proj_num__0,proj_uN_0,Option.get!_some] using outside
  · exact input
  · exact .admininstr_case_73
  · exact Segment.index_wf 0 (by norm_num)
end Itasca.Spec.Simd

end

/-! ## MemoryLaneStore -/

section

/-!
Source reduction for bounded vector lane stores.

Main declarations: `lane_store_step`.
-/

namespace Itasca.Spec.Simd
open WebAssembly WebAssembly.Builtins

theorem lane_store_step (ty : Jnn) (s : store) (f : frame) (argument : memarg) (address index : Nat)
    (before : BitVec 128) (word : BitVec (lsize (lanetype_Jnn ty)))
    (valid : index < 128/lsize (lanetype_Jnn ty))
    (selected : (lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN before.toNat))[index]! = .mk_lane__0 ty (.mk_uN word.toNat))
    (storeWf : wf_store s) (frameWf : wf_frame f) (addressBound : address < 2^32)
    (operationWf : wf_admininstr (.VSTORE_LANE .V128 (.mk_sz (lsize (lanetype_Jnn ty))) argument (.mk_uN index)))
    (mapped : 0 < f.MODULE.MEMS.length) :
    StepH ⟨⟨s,f⟩,[Segment.i32 address,.VCONST .V128 (.mk_uN before.toNat),
      .VSTORE_LANE .V128 (.mk_sz (lsize (lanetype_Jnn ty))) argument (.mk_uN index)]⟩ []
      (if address+proj_uN_0 argument.OFFSET+lsize (lanetype_Jnn ty)/8 ≤ (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length then
        ⟨⟨memoryPayloadWrite s f (address+proj_uN_0 argument.OFFSET)
          (integerBytes (lsize (lanetype_Jnn ty)/8) word.toNat),f⟩,[]⟩
      else ⟨⟨s,f⟩,[.TRAP]⟩) := by
  have input := wf_config_make storeWf frameWf (show Forall wf_admininstr
      [Segment.i32 address,.VCONST .V128 (.mk_uN before.toNat),
        .VSTORE_LANE .V128 (.mk_sz (lsize (lanetype_Jnn ty))) argument (.mk_uN index)] from by
    intro instruction member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · exact Segment.i32_wf address addressBound
    · exact const_wf before
    · exact operationWf)
  split
  · rename_i inside
    have updatedWf := memory_payload_write_wf s f (address+proj_uN_0 argument.OFFSET)
      (integerBytes (lsize (lanetype_Jnn ty)/8) word.toNat) storeWf (integer_bytes_wf _ _)
    apply StepH.step
    apply Step.vstore_lane_val _ _ _ _ _ _ _ ty (128/lsize (lanetype_Jnn ty))
    · simp [proj_num__0]
    · simpa only [lane_byte_count,proj_num__0,proj_uN_0,Option.get!_some,memoryPayloadWrite] using
        fun_with_mem.fun_with_mem_case_0 s f (.mk_uN 0) (address+proj_uN_0 argument.OFFSET)
          (lsize (lanetype_Jnn ty)/8) (integerBytes (lsize (lanetype_Jnn ty)/8) word.toNat) mapped inside
          (.state_case_0 _ _ updatedWf frameWf) (.state_case_0 _ _ storeWf frameWf)
    · simpa only [lane_byte_count,proj_num__0,proj_uN_0,Option.get!_some] using inside
    · cases ty <;> rfl
    · exact lane_dimension ty
    · change proj_lane__0 ((lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN before.toNat))[index]!) ≠ none
      rw [selected]; simp [proj_lane__0]
    · simpa [lanes_,shapeOf,proj_uN_0,unpack_lanes_length] using valid
    · change integerBytes (lsize (lanetype_Jnn ty)/8) word.toNat =
        ibytes_ (lsize (lanetype_Jnn ty)) (.mk_uN (proj_uN_0 (Option.get! (proj_lane__0
          ((lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN before.toNat))[index]!)))))
      rw [selected]
      rfl
    · exact input
    · exact wf_config_make updatedWf frameWf (forall_nil _)
    · exact Segment.index_wf 0 (by norm_num)
    · change wf_uN (lsize (lanetype_Jnn ty)) (.mk_uN (proj_uN_0 (Option.get! (proj_lane__0
        ((lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN before.toNat))[index]!)))))
      rw [selected]
      exact unsigned_wf_of_lt _ word.toNat word.isLt
  · rename_i outside
    apply StepH.step
    apply Step.vstore_lane_oob
    · simp [proj_num__0]
    · simpa only [lane_byte_count,proj_num__0,proj_uN_0,Option.get!_some] using
        (Nat.lt_of_not_ge outside)
    · exact input
    · exact wf_config_trap storeWf frameWf
    · exact Segment.index_wf 0 (by norm_num)
end Itasca.Spec.Simd

end

/-! ## MemorySplat -/

section

/-!
Returned and trapping source behavior of vector splat loads.

Main declarations: `splat_load_value` and `splat_load_trap`.
-/

namespace Itasca.Spec.Simd
open WebAssembly WebAssembly.Builtins
theorem splat_load_value (ty : Jnn) (s : store) (f : frame) (argument : memarg) (address : Nat)
    (result : BitVec 128) (word : BitVec (lsize (lanetype_Jnn ty)))
    (storeWf : wf_store s) (frameWf : wf_frame f) (addressBound : address < 2^32)
    (operationWf : wf_admininstr (.VLOAD .V128 (some (.SPLAT (.mk_sz (lsize (lanetype_Jnn ty))))) argument))
    (bytesEq : ibytes_ (lsize (lanetype_Jnn ty)) (.mk_uN word.toNat) =
      ((fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.drop (address+proj_uN_0 argument.OFFSET)).take (lsize (lanetype_Jnn ty)/8))
    (packed : uN.mk_uN result.toNat = inv_lanes_ (shapeOf (lanetype_Jnn ty))
      (List.replicate (128/lsize (lanetype_Jnn ty)) (.mk_lane__0 ty (.mk_uN word.toNat)))) :
    StepH ⟨⟨s,f⟩,[Segment.i32 address,
      .VLOAD .V128 (some (.SPLAT (.mk_sz (lsize (lanetype_Jnn ty))))) argument]⟩ []
      ⟨⟨s,f⟩,[.VCONST .V128 (.mk_uN result.toNat)]⟩ := by
  have input := wf_config_make storeWf frameWf (show Forall wf_admininstr
      [Segment.i32 address,
        .VLOAD .V128 (some (.SPLAT (.mk_sz (lsize (lanetype_Jnn ty))))) argument] from by
    intro instruction member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact Segment.i32_wf address addressBound
    · exact operationWf)
  have output := wf_config_make storeWf frameWf (show Forall wf_admininstr [.VCONST .V128 (.mk_uN result.toNat)] from by
    simpa [Forall] using const_wf result)
  apply StepH.step
  apply Step.read _ _ _ ?_ input output
  apply Step_read.vload_splat_val _ _ _ _ _ (.mk_uN word.toNat) ty (128/lsize (lanetype_Jnn ty))
  · simp [proj_num__0]
  · simpa only [lane_byte_count,proj_num__0,proj_uN_0,Option.get!_some] using bytesEq
  · cases ty <;> rfl
  · exact lane_dimension ty
  · simpa only [shapeOf,List.modify_eq_set,proj_uN_0] using packed
  · exact input
  · exact const_wf result
  · exact Segment.index_wf 0 (by norm_num)
  · exact shape_of_wf _
  · cases ty <;> exact lane_of_bits_wf _ word.toNat word.isLt

theorem splat_load_trap (ty : Jnn) (s : store) (f : frame) (argument : memarg) (address : Nat)
    (storeWf : wf_store s) (frameWf : wf_frame f) (addressBound : address < 2^32)
    (operationWf : wf_admininstr (.VLOAD .V128 (some (.SPLAT (.mk_sz (lsize (lanetype_Jnn ty))))) argument))
    (outside : (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length < address+proj_uN_0 argument.OFFSET+lsize (lanetype_Jnn ty)/8) :
    StepH ⟨⟨s,f⟩,[Segment.i32 address,
      .VLOAD .V128 (some (.SPLAT (.mk_sz (lsize (lanetype_Jnn ty))))) argument]⟩ [] ⟨⟨s,f⟩,[.TRAP]⟩ := by
  have input := wf_config_make storeWf frameWf (show Forall wf_admininstr
      [Segment.i32 address,
        .VLOAD .V128 (some (.SPLAT (.mk_sz (lsize (lanetype_Jnn ty))))) argument] from by
    intro instruction member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact Segment.i32_wf address addressBound
    · exact operationWf)
  apply StepH.step
  apply Step.read _ _ _ ?_ input (wf_config_trap storeWf frameWf)
  apply Step_read.vload_splat_oob
  · simp [proj_num__0]
  · simpa only [lane_byte_count,proj_num__0,proj_uN_0,Option.get!_some] using outside
  · exact input
  · exact .admininstr_case_73
  · exact Segment.index_wf 0 (by norm_num)
end Itasca.Spec.Simd

end

/-! ## MemoryStore -/

section

/-!
Source reduction for bounded full-vector stores.

Main declarations: `full_store_step`.
-/

namespace Itasca.Spec.Simd
open WebAssembly
theorem full_store_step (s : store) (f : frame) (argument : memarg) (address : Nat) (value : BitVec 128)
    (storeWf : wf_store s) (frameWf : wf_frame f) (addressBound : address < 2^32)
    (operationWf : wf_admininstr (.VSTORE .V128 argument))
    (mapped : 0 < f.MODULE.MEMS.length) :
    StepH ⟨⟨s,f⟩,[Segment.i32 address,.VCONST .V128 (.mk_uN value.toNat),.VSTORE .V128 argument]⟩ []
      (if address + proj_uN_0 argument.OFFSET + 16 ≤ (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES.length then
        ⟨⟨memoryPayloadWrite s f (address + proj_uN_0 argument.OFFSET) (vbytes_ .V128 (.mk_uN value.toNat)),f⟩,[]⟩
      else ⟨⟨s,f⟩,[.TRAP]⟩) := by
  have byteCount : rat_to_nat ((Option.get! (size valtype.V128) : Rat) / 8) = 16 := by
    norm_num [size,rat_to_nat]
    rfl
  have input := wf_config_make storeWf frameWf (show Forall wf_admininstr [Segment.i32 address,.VCONST .V128 (.mk_uN value.toNat),.VSTORE .V128 argument] from by
    intro instruction member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · exact Segment.i32_wf address addressBound
    · exact const_wf value
    · exact operationWf)
  split
  · rename_i inside
    have updatedWf := memory_payload_write_wf s f (address+proj_uN_0 argument.OFFSET) (vbytes_ .V128 (.mk_uN value.toNat))
      storeWf (by exact integer_bytes_wf 16 value.toNat)
    apply StepH.step
    apply Step.vstore_val _ _ _ _ (vbytes_ .V128 (.mk_uN value.toNat))
    · simp [proj_num__0]
    · decide
    · exact .fun_with_mem_case_0 s f (.mk_uN 0) _ _ _ mapped
        (by simpa only [byteCount,proj_num__0,proj_uN_0,Option.get!_some] using inside)
        (.state_case_0 _ _ updatedWf frameWf) (.state_case_0 _ _ storeWf frameWf)
    · rfl
    · exact input
    · exact wf_config_make updatedWf frameWf (forall_nil _)
  · rename_i outside
    apply StepH.step
    apply Step.vstore_oob
    · simp [proj_num__0]
    · decide
    · simpa only [byteCount,proj_num__0,proj_uN_0,Option.get!_some] using Nat.lt_of_not_ge outside
    · exact input
    · exact wf_config_trap storeWf frameWf
    · exact Segment.index_wf 0 (by norm_num)
end Itasca.Spec.Simd

end

/-! ## MemoryZero -/

section

/-!
The source result relation for zero-extending vector loads.

Main declarations: `zeroLoadResult`.
-/

namespace Itasca.Spec.Simd
open WebAssembly WebAssembly.Builtins

def zeroLoadResult (width : Nat) (bytes : List byte) (start : Nat) : List admininstr :=
  if start + width/8 ≤ bytes.length then
    [.VCONST .V128 (.mk_uN (integerOfBytes ((bytes.drop start).take (width/8))))]
  else [.TRAP]

theorem zero_load_step (width : Nat) (supported : width = 32 ∨ width = 64)
    (s : store) (f : frame) (argument : memarg) (address : Nat)
    (storeWf : wf_store s) (frameWf : wf_frame f) (addressBound : address < 2^32)
    (operationWf : wf_admininstr (.VLOAD .V128 (some (.ZERO (.mk_sz width))) argument))
    (bytesWf : Forall wf_byte (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES) :
    StepH ⟨⟨s,f⟩,[Segment.i32 address,.VLOAD .V128 (some (.ZERO (.mk_sz width))) argument]⟩ []
      ⟨⟨s,f⟩,zeroLoadResult width (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES
        (address + proj_uN_0 argument.OFFSET)⟩ := by
  have byteCount : rat_to_nat ((width : Rat) / 8) = width/8 := by
    rcases supported with rfl | rfl <;> norm_num [rat_to_nat] <;> rfl
  have input := wf_config_make storeWf frameWf (show Forall wf_admininstr
      [Segment.i32 address,.VLOAD .V128 (some (.ZERO (.mk_sz width))) argument] from by
    intro instruction member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact Segment.i32_wf address addressBound
    · exact operationWf)
  unfold zeroLoadResult
  split
  · rename_i fits
    let bytes := (fun_mem ⟨s,f⟩ (.mk_uN 0)).BYTES
    let start := address + proj_uN_0 argument.OFFSET
    have payloadWf : Forall wf_byte ((bytes.drop start).take (width/8)) := by
      intro byte member
      exact bytesWf byte (List.mem_of_mem_drop (List.mem_of_mem_take member))
    have payloadLength : ((bytes.drop start).take (width/8)).length = width/8 := by
      simp only [List.length_take,List.length_drop]
      dsimp only [bytes,start]
      omega
    have bounded := integer_of_bytes_bound _ payloadWf
    rw [payloadLength] at bounded
    have narrow : wf_uN width (.mk_uN (integerOfBytes ((bytes.drop start).take (width/8)))) := by
      apply unsigned_wf_of_lt
      rcases supported with rfl | rfl <;> norm_num at bounded ⊢ <;> exact bounded
    have valueWf : wf_admininstr (.VCONST .V128 (.mk_uN (integerOfBytes ((bytes.drop start).take (width/8))))) := by
      apply wf_admininstr.admininstr_case_20 _ _ (by decide)
      apply unsigned_wf_of_lt
      rcases supported with rfl | rfl <;> norm_num [size,valtype_vectype] at bounded ⊢ <;> omega
    have output := wf_config_make storeWf frameWf (show Forall wf_admininstr
      [.VCONST .V128 (.mk_uN (integerOfBytes ((bytes.drop start).take (width/8))))] from by
      simpa [Forall] using valueWf)
    apply StepH.step
    apply Step.read _ _ _ ?_ input output
    apply Step_read.vload_zero_val _ _ _ _ _ (.mk_uN (integerOfBytes ((bytes.drop start).take (width/8))))
    · simp [proj_num__0]
    · have roundtrip := integer_bytes_of_bytes _ payloadWf
      rw [payloadLength] at roundtrip
      simpa only [ibytes_,proj_uN_0,byteCount,proj_num__0,Option.get!_some,bytes,start,payloadLength]
        using roundtrip
    · rfl
    · exact narrow
    · exact input
    · exact valueWf
    · exact Segment.index_wf 0 (by norm_num)
  · rename_i outside
    apply StepH.step
    apply Step.read _ _ _ ?_ input (wf_config_trap storeWf frameWf)
    apply Step_read.vload_zero_oob
    · simp [proj_num__0]
    · simpa only [byteCount,proj_num__0,proj_uN_0,Option.get!_some] using Nat.lt_of_not_ge outside
    · exact input
    · exact .admininstr_case_73
    · exact Segment.index_wf 0 (by norm_num)
end Itasca.Spec.Simd

end

/-! ## FloatUnary -/

section

/-!
Source-rule algebra for unary floating-point lanes. Lane/list calculations establish the generated source operation and its reduction step, consumed by source-machine and interpreter correspondence proofs.
-/

/-! ## Simd Float Unary -/

section

namespace Itasca.Spec.Simd
open WebAssembly.Builtins WebAssembly.Builtins.Float

def floatUnaryChoices (width : Nat) (op : vunop_Fnn_N) (a : fN) : List fN :=
  match op with
  | .ABS => fabs_ width a
  | .NEG => fneg_ width a
  | .SQRT => fsqrt_ width a
  | .CEIL => fceil_ width a
  | .FLOOR => ffloor_ width a
  | .TRUNC => ftrunc_ width a
  | .NEAREST => fnearest_ width a

def floatUnarySource (ty : Fnn) (op : vunop_Fnn_N) : vunop_ :=
  .mk_vunop__1 ty (128/lsize (lanetype_Fnn ty)) op

theorem float_unary_source_wf (ty : Fnn) (op : vunop_Fnn_N) :
    wf_vunop_ (shapeOf (lanetype_Fnn ty)) (floatUnarySource ty op) := by
  cases ty <;> cases op <;> constructor <;> constructor

theorem float_unary_choices_wf (width : Nat) (supported : width = 32 ∨ width = 64)
    (op : vunop_Fnn_N) (a : fN) (inputWf : wf_fN width a) :
    Forall (wf_fN width) (floatUnaryChoices width op a) := by
  cases op with
  | ABS =>
    intro result member
    simp only [floatUnaryChoices,fabs_,List.mem_singleton] at member
    subst result
    exact with_sign_wf (magnitude_wf inputWf) false
  | NEG =>
    intro result member
    simp only [floatUnaryChoices,fneg_,List.mem_singleton] at member
    subst result
    exact with_sign_wf (magnitude_wf inputWf) _
  | SQRT => exact sqrt_wf width supported a inputWf
  | CEIL => exact integral_wf width supported _ a inputWf
  | FLOOR => exact integral_wf width supported _ a inputWf
  | TRUNC => exact integral_wf width supported _ a inputWf
  | NEAREST => exact integral_wf width supported _ a inputWf

end Itasca.Spec.Simd

end

/-! ## Simd Float Unary Source -/

section

namespace Itasca.Spec.Simd
open WebAssembly.Builtins WebAssembly.Builtins.Float

def floatUnaryLaneChoices (ty : Fnn) (op : vunop_Fnn_N) (lane : lane_) : List lane_ :=
  Map (lane_.mk_lane__1 ty) (floatUnaryChoices (lsize (lanetype_Fnn ty)) op (Option.get! (proj_lane__1 lane)))

def floatUnaryResults (ty : Fnn) (op : vunop_Fnn_N) (bits : BitVec 128) : List uN :=
  Map (inv_lanes_ (shapeOf (lanetype_Fnn ty)))
    (setproduct_ lane_ (Map (floatUnaryLaneChoices ty op)
      (lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN bits.toNat))))

theorem float_unary_lanes_wf (ty : Fnn) (op : vunop_Fnn_N) (bits : BitVec 128) :
    Forall (fun lane => Forall (fun value => wf_lane_ (lanetype_Fnn ty) (.mk_lane__1 ty value))
      (floatUnaryChoices (lsize (lanetype_Fnn ty)) op (Option.get! (proj_lane__1 lane))))
      (lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN bits.toNat)) := by
  rw [lanes_map_words]
  intro lane member
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
  have inputWf : wf_fN (lsize (lanetype_Fnn ty))
      (Option.get! (proj_lane__1 (laneOfBits (lanetype_Fnn ty) (laneWord (lanetype_Fnn ty) bits j).toNat))) := by
    cases ty <;> exact float_of_bits_wf _ (by decide) _
  intro value allowed
  have wf := float_unary_choices_wf (lsize (lanetype_Fnn ty)) (by cases ty <;> decide) op _ inputWf value allowed
  cases ty <;> exact .lane__case_1 _ _ _ wf rfl

theorem float_unary_relation (ty : Fnn) (op : vunop_Fnn_N) (bits : BitVec 128) :
    fun_vunop_ (shapeOf (lanetype_Fnn ty)) (floatUnarySource ty op)
      (.mk_uN bits.toNat) (some (floatUnaryResults ty op bits)) := by
  have shapeWf := shape_of_wf (lanetype_Fnn ty)
  have lanesWf := float_unary_lanes_wf ty op bits
  cases ty <;> cases op
  · apply fun_vunop_.fun_vunop__case_12
    all_goals first | rfl | exact shapeWf | exact lanesWf
  · apply fun_vunop_.fun_vunop__case_14
    all_goals first | rfl | exact shapeWf | exact lanesWf
  · apply fun_vunop_.fun_vunop__case_16
    all_goals first | rfl | exact shapeWf | exact lanesWf
  · apply fun_vunop_.fun_vunop__case_18
    all_goals first | rfl | exact shapeWf | exact lanesWf
  · apply fun_vunop_.fun_vunop__case_20
    all_goals first | rfl | exact shapeWf | exact lanesWf
  · apply fun_vunop_.fun_vunop__case_22
    all_goals first | rfl | exact shapeWf | exact lanesWf
  · apply fun_vunop_.fun_vunop__case_24
    all_goals first | rfl | exact shapeWf | exact lanesWf
  · apply fun_vunop_.fun_vunop__case_13
    all_goals first | rfl | exact shapeWf | exact lanesWf
  · apply fun_vunop_.fun_vunop__case_15
    all_goals first | rfl | exact shapeWf | exact lanesWf
  · apply fun_vunop_.fun_vunop__case_17
    all_goals first | rfl | exact shapeWf | exact lanesWf
  · apply fun_vunop_.fun_vunop__case_19
    all_goals first | rfl | exact shapeWf | exact lanesWf
  · apply fun_vunop_.fun_vunop__case_21
    all_goals first | rfl | exact shapeWf | exact lanesWf
  · apply fun_vunop_.fun_vunop__case_23
    all_goals first | rfl | exact shapeWf | exact lanesWf
  · apply fun_vunop_.fun_vunop__case_25
    all_goals first | rfl | exact shapeWf | exact lanesWf

end Itasca.Spec.Simd

end

/-! ## Simd Float Unary Choices -/

section

namespace Itasca.Spec.Simd
open WebAssembly.Builtins

theorem lanes_roundtrip (ty : lanetype) (bits : BitVec 128) :
    inv_lanes_ (shapeOf ty) (lanes_ (shapeOf ty) (.mk_uN bits.toNat)) = .mk_uN bits.toNat := by
  change uN.mk_uN (packLanes ty (unpackLanes ty (128/lsize ty) bits.toNat)) = _
  rw [pack_unpack_lanes,shape_of_covers,Nat.mod_eq_of_lt bits.isLt]

theorem float_unary_result_member (ty : Fnn) (op : vunop_Fnn_N) (x result : BitVec 128)
    (allowed : ∀ j, j < 128/lsize (lanetype_Fnn ty) →
      floatOfBits (lsize (lanetype_Fnn ty)) (laneWord (lanetype_Fnn ty) result j).toNat ∈
        floatUnaryChoices (lsize (lanetype_Fnn ty)) op
          (floatOfBits (lsize (lanetype_Fnn ty)) (laneWord (lanetype_Fnn ty) x j).toNat)) :
    uN.mk_uN result.toNat ∈ floatUnaryResults ty op x := by
  apply List.mem_map.mpr
  refine ⟨lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN result.toNat),?_,lanes_roundtrip _ result⟩
  rw [lanes_map_words,lanes_map_words]
  change List.map _ _ ∈ setproduct_ _ (List.map _ (List.map _ _))
  rw [List.map_map]
  apply mem_setproduct_map
  intro j member
  have chosen := allowed j (List.mem_range.mp member)
  cases ty <;> exact List.mem_map.mpr ⟨_,chosen,rfl⟩

theorem float_unary_step (ty : Fnn) (op : vunop_Fnn_N) (x result : BitVec 128)
    (allowed : ∀ j, j < 128/lsize (lanetype_Fnn ty) →
      floatOfBits (lsize (lanetype_Fnn ty)) (laneWord (lanetype_Fnn ty) result j).toNat ∈
        floatUnaryChoices (lsize (lanetype_Fnn ty)) op
          (floatOfBits (lsize (lanetype_Fnn ty)) (laneWord (lanetype_Fnn ty) x j).toNat)) :
    Step_pure [.VCONST .V128 (.mk_uN x.toNat),
      .VUNOP (shapeOf (lanetype_Fnn ty)) (floatUnarySource ty op)] [.VCONST .V128 (.mk_uN result.toNat)] := by
  have chosen := float_unary_result_member ty op x result allowed
  apply Step_pure.vunop _ _ _ _ (some (floatUnaryResults ty op x)) (float_unary_relation ty op x)
  · exact List.length_pos_of_mem chosen
  · simp
  · simpa only [Option.get!_some,List.contains_iff_mem] using chosen
  · exact const_wf x
  · exact .admininstr_case_25 _ _ (shape_of_wf _) (float_unary_source_wf ty op)
  · exact const_wf result

end Itasca.Spec.Simd

end

end

/-! ## FloatResize -/

section

/-!
Source-rule algebra for floating-point lane promotion and demotion. Lane/list calculations establish the generated source operation and its reduction step, consumed by source-machine and interpreter correspondence proofs.
-/

/-! ## Simd Float Resize -/

section

namespace Itasca.Spec.Simd
open WebAssembly.Builtins WebAssembly.Builtins.Float

inductive FloatResize where | demote | promote

def FloatResize.input : FloatResize → Fnn | .demote => .F64 | .promote => .F32

def FloatResize.output : FloatResize → Fnn | .demote => .F32 | .promote => .F64

def floatResizeChoices : FloatResize → fN → List fN
  | .demote,a => demote__ 64 32 a
  | .promote,a => promote__ 32 64 a

def floatResizeSource (kind : FloatResize) : vcvtop__ :=
  match kind with
  | .demote => .mk_vcvtop___3 .F64 2 .F32 4 (.DEMOTE .ZERO)
  | .promote => .mk_vcvtop___3 .F32 4 .F64 2 .PROMOTELOW

theorem float_resize_source_wf (kind : FloatResize) :
    wf_vcvtop__ (shapeOf (lanetype_Fnn kind.input)) (shapeOf (lanetype_Fnn kind.output)) (floatResizeSource kind) := by
  cases kind <;> apply wf_vcvtop__.vcvtop___case_3
  · exact .vcvtop__Fnn_1_M_1_Fnn_2_M_2_case_0 _ _ _ _ _ (by decide)
  · rfl
  · rfl
  · exact .vcvtop__Fnn_1_M_1_Fnn_2_M_2_case_1 _ _ _ _ (by decide)
  · rfl
  · rfl

end Itasca.Spec.Simd

end

/-! ## Simd Float Resize Source -/

section

namespace Itasca.Spec.Simd
open WebAssembly.Builtins WebAssembly.Builtins.Float

def floatResizeLaneChoices (kind : FloatResize) (a : fN) : List lane_ :=
  Map (lane_.mk_lane__1 kind.output) (floatResizeChoices kind a)

def floatResizeInputs (kind : FloatResize) (x : BitVec 128) : List lane_ :=
  (List.range 2).map (fun j => laneOfBits (lanetype_Fnn kind.input) (laneWord (lanetype_Fnn kind.input) x j).toNat)

def floatResizeChoicesList (kind : FloatResize) (x : BitVec 128) : List (Option (List lane_)) :=
  (List.range 2).map (fun j => some (floatResizeLaneChoices kind
    (floatOfBits (lsize (lanetype_Fnn kind.input)) (laneWord (lanetype_Fnn kind.input) x j).toNat)))

def floatResizePadding (kind : FloatResize) : List (List lane_) :=
  match kind with
  | .demote => List.replicate 2 [.mk_lane__1 .F32 (floatOfBits 32 0)]
  | .promote => []

def floatResizeProducts (kind : FloatResize) (x : BitVec 128) : List (List lane_) :=
  setproduct_ lane_ (Map Option.get! (floatResizeChoicesList kind x) ++ floatResizePadding kind)

theorem float_resize_lane_relation (kind : FloatResize) (value : fN) :
    fun_lcvtop__ (shapeOf (lanetype_Fnn kind.input)) (shapeOf (lanetype_Fnn kind.output)) (floatResizeSource kind)
      (.mk_lane__1 kind.input value) (some (floatResizeLaneChoices kind value)) := by
  have wf : Forall (fun result => wf_lane_ (lanetype_Fnn kind.output) (.mk_lane__1 kind.output result)) (floatResizeChoices kind value) := by
    intro result member
    cases kind
    · exact .lane__case_1 _ _ _ (Itasca.Spec.float_demote_wf 64 32 (by decide) value result member) rfl
    · exact .lane__case_1 _ _ _ (Itasca.Spec.float_demote_wf 32 64 (by decide) value result member) rfl
  cases kind
  · exact .fun_lcvtop___case_29 _ _ _ _ _ _ rfl wf rfl rfl
  · exact .fun_lcvtop___case_34 _ _ _ _ _ _ rfl wf rfl rfl

theorem float_resize_lists_relation (kind : FloatResize) (x : BitVec 128) :
    Forall₂ (fun choices input => fun_lcvtop__ (shapeOf (lanetype_Fnn kind.input))
      (shapeOf (lanetype_Fnn kind.output)) (floatResizeSource kind) input choices)
      (floatResizeChoicesList kind x) (floatResizeInputs kind x) := by
  apply forall2_map
  intro j member
  cases kind <;> exact float_resize_lane_relation _ _

theorem float_resize_product_member (kind : FloatResize) (x result : BitVec 128)
    (allowed : ∀ j, j < 2 →
      floatOfBits (lsize (lanetype_Fnn kind.output)) (laneWord (lanetype_Fnn kind.output) result j).toNat ∈
        floatResizeChoices kind (floatOfBits (lsize (lanetype_Fnn kind.input)) (laneWord (lanetype_Fnn kind.input) x j).toNat))
    (zeroed : ∀ j, 2 ≤ j → j < 128/lsize (lanetype_Fnn kind.output) → laneWord (lanetype_Fnn kind.output) result j = 0) :
    lanes_ (shapeOf (lanetype_Fnn kind.output)) (.mk_uN result.toNat) ∈ floatResizeProducts kind x := by
  rw [lanes_map_words]
  cases kind
  · change (List.range 4).map _ ∈ setproduct_ lane_ ((List.range 4).map (fun j =>
      if j < 2 then floatResizeLaneChoices .demote (floatOfBits 64 (laneWord .F64 x j).toNat)
      else [.mk_lane__1 .F32 (floatOfBits 32 0)]))
    apply mem_setproduct_map
    intro j member
    by_cases valid : j < 2
    · rw [if_pos valid]
      exact List.mem_map.mpr ⟨_,allowed j valid,rfl⟩
    · rw [if_neg valid]
      have zero := zeroed j (by omega) (List.mem_range.mp member)
      change laneWord .F32 result j = 0 at zero
      change lane_.mk_lane__1 .F32 (floatOfBits 32 (laneWord .F32 result j).toNat) ∈ _
      rw [zero]
      exact List.mem_cons_self
  · change (List.range 2).map _ ∈ setproduct_ lane_ ((List.range 2).map (fun j =>
      floatResizeLaneChoices .promote (floatOfBits 32 (laneWord .F32 x j).toNat)))
    apply mem_setproduct_map
    intro j member
    exact List.mem_map.mpr ⟨_,allowed j (List.mem_range.mp member),rfl⟩

end Itasca.Spec.Simd

end

/-! ## Simd Float Resize Step -/

section

namespace Itasca.Spec.Simd
open WebAssembly.Builtins WebAssembly.Builtins.Float

theorem float_resize_vector_relation (kind : FloatResize) (x result : BitVec 128)
    (selected : lanes_ (shapeOf (lanetype_Fnn kind.output)) (.mk_uN result.toNat) ∈ floatResizeProducts kind x) :
    fun_vcvtop__ (shapeOf (lanetype_Fnn kind.input)) (shapeOf (lanetype_Fnn kind.output)) (floatResizeSource kind)
      (.mk_uN x.toNat) (some (.mk_uN result.toNat)) := by
  let choices := floatResizeChoicesList kind x
  let inputs := floatResizeInputs kind x
  let products := floatResizeProducts kind x
  have nonempty : Forall (fun c => c ≠ none) choices := by
    intro c member
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
    simp
  have lengths : choices.length = inputs.length := by
    simp [choices,inputs,floatResizeChoicesList,floatResizeInputs]
  have member : (.mk_uN result.toNat) ∈ Map (inv_lanes_ (shapeOf (lanetype_Fnn kind.output))) products :=
    List.mem_map.mpr ⟨_,selected,lanes_roundtrip _ result⟩
  have wf := unsigned_wf_of_lt 128 result.toNat result.isLt
  cases kind
  · apply fun_vcvtop__.fun_vcvtop___case_2 .F64 2 .F32 4 (floatResizeSource .demote)
      (.mk_uN x.toNat) (.mk_uN result.toNat) inputs products (.mk_num__1 .F32 (floatOfBits 32 0))
      (some (.mk_lane__1 .F32 (floatOfBits 32 0))) choices (some (some .ZERO))
    · apply fun_zero.fun_zero_case_2
      · decide
      · exact .fun_fzero_case_0 _ (float_of_bits_wf 32 (by decide) 0)
      · exact Itasca.Spec.float_num_wf .F32 _ (float_of_bits_wf 32 (by decide) _)
    · constructor; exact .lane__case_1 _ _ _ (float_of_bits_wf 32 (by decide) _) rfl
    · exact lengths
    · exact float_resize_lists_relation .demote x
    · exact .fun_zeroop_case_33 _ _ _ _ _ rfl rfl
    · simp
    · rfl
    · change inputs = lanes_ (shapeOf .F64) (.mk_uN x.toNat)
      rw [lanes_map_words]; rfl
    · exact nonempty
    · simp
    · rfl
    · exact List.length_pos_of_mem member
    · simpa only [List.contains_iff_mem,FloatResize.output,lanetype_Fnn,shapeOf,lsize,size,valtype_numtype,Option.get!_some] using member
    · exact wf
    · exact shape_of_wf _
    · exact shape_of_wf _
  · apply fun_vcvtop__.fun_vcvtop___case_1 .F32 4 .F64 2 (floatResizeSource .promote)
      (.mk_uN x.toNat) (.mk_uN result.toNat) .LOW inputs products choices (some (some .LOW))
    · exact lengths
    · exact float_resize_lists_relation .promote x
    · exact .fun_halfop_case_38 _ _ _ _ rfl rfl
    · simp
    · rfl
    · change inputs = List.take 2 (List.drop (fun_half .LOW 0 2) (lanes_ (shapeOf .F32) (.mk_uN x.toNat)))
      rw [lanes_map_words]; rfl
    · exact nonempty
    · rfl
    · exact List.length_pos_of_mem member
    · simpa only [List.contains_iff_mem,FloatResize.output,lanetype_Fnn,shapeOf,lsize,size,valtype_numtype,Option.get!_some] using member
    · exact wf
    · exact shape_of_wf _
    · exact shape_of_wf _

theorem float_resize_step (kind : FloatResize) (x result : BitVec 128)
    (allowed : ∀ j, j < 2 →
      floatOfBits (lsize (lanetype_Fnn kind.output)) (laneWord (lanetype_Fnn kind.output) result j).toNat ∈
        floatResizeChoices kind (floatOfBits (lsize (lanetype_Fnn kind.input)) (laneWord (lanetype_Fnn kind.input) x j).toNat))
    (zeroed : ∀ j, 2 ≤ j → j < 128/lsize (lanetype_Fnn kind.output) → laneWord (lanetype_Fnn kind.output) result j = 0) :
    Step_pure [.VCONST .V128 (.mk_uN x.toNat),
      .VCVTOP (shapeOf (lanetype_Fnn kind.output)) (shapeOf (lanetype_Fnn kind.input)) (floatResizeSource kind)]
      [.VCONST .V128 (.mk_uN result.toNat)] := by
  have selected := float_resize_product_member kind x result allowed zeroed
  apply Step_pure.vcvtop _ _ _ _ _ (some (.mk_uN result.toNat))
  · exact float_resize_vector_relation kind x result selected
  · simp
  · rfl
  · exact const_wf x
  · apply wf_admininstr.admininstr_case_39
    · exact shape_of_wf _
    · exact shape_of_wf _
    · exact float_resize_source_wf kind
  · exact const_wf result

end Itasca.Spec.Simd

end

end

end

/-! ## ArithmeticAndReductions -/

section

/-!
# SIMD arithmetic and reductions

All-true/bitmask/popcount, unary and floating binary operations supply source value facts.
Average and integer extrema combine lane shapes, list relations and generated source
steps.
-/

/-! ## AllTrue -/

section

/-!
The source operation for all-true lane reduction.

Main declarations: `allTrueSource`.
-/

namespace Itasca.Spec.Simd
open WebAssembly.Builtins

def allTrueSource (ty : Jnn) : admininstr :=
  .VTESTOP (shapeOf (lanetype_Jnn ty)) (.mk_vtestop__0 ty (128/lsize (lanetype_Jnn ty)) .ALL_TRUE)

theorem all_true_prior (ty : Jnn) (bits : BitVec 128)
    (prior : Step_pure_before_vtestop_false [.VCONST .V128 (.mk_uN bits.toNat),allTrueSource ty]) :
    Forall (fun lane => proj_uN_0 (Option.get! (proj_lane__0 lane)) ≠ 0)
      (lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN bits.toNat)) := by
  generalize programEq : [admininstr.VCONST .V128 (.mk_uN bits.toNat),allTrueSource ty] = program at prior
  cases prior <;> simp_all only [allTrueSource, shapeOf, List.cons.injEq,
    admininstr.VCONST.injEq, admininstr.VTESTOP.injEq, shape.X.injEq,
    dim.mk_dim.injEq, vtestop_.mk_vtestop__0.injEq, and_true, true_and]
  rcases programEq with ⟨_,⟨_,sizeEq⟩,_,_⟩
  subst_vars
  assumption

theorem all_true_step (ty : Jnn) (bits : BitVec 128) (answer : Bool)
    (truth : answer = true ↔ ∀ j, j < 128/lsize (lanetype_Jnn ty) →
      (vectorLane (lanetype_Jnn ty) bits j).toNat ≠ 0) :
    Step_pure [.VCONST .V128 (.mk_uN bits.toNat),allTrueSource ty]
      [.CONST .I32 (.mk_num__0 .I32 (.mk_uN (if answer then 1 else 0)))] := by
  let inputs := (List.range (128/lsize (lanetype_Jnn ty))).map
    (fun j => lane_.mk_lane__0 ty (.mk_uN (vectorLane (lanetype_Jnn ty) bits j).toNat))
  have inputEq : inputs = lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN bits.toNat) := by
    rw [vector_lanes]
    cases ty <;> rfl
  have projected : Forall (fun lane => proj_lane__0 lane ≠ none) inputs := by
    intro lane member
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
    simp [proj_lane__0]
  have inputWf : Forall (fun lane => wf_lane_ (lanetype_Jnn ty) lane) inputs := by
    intro lane member
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
    have wf := lane_of_bits_wf (lanetype_Jnn ty) (vectorLane (lanetype_Jnn ty) bits j).toNat
      (BitVec.toNat_lt_twoPow_of_le (by rfl))
    cases ty <;> exact wf
  have sourceWf : wf_admininstr (allTrueSource ty) :=
    .admininstr_case_27 _ _ (shape_of_wf _) (.vtestop__case_0 _ _ _ _ rfl)
  cases answer with
  | true =>
    apply Step_pure.vtestop_true _ _ _ inputs inputEq projected _ inputWf
      (const_wf bits) sourceWf (.admininstr_case_13 _ _ (unsigned_num_wf .I32 1 (by decide))) (shape_of_wf _)
    intro lane member
    obtain ⟨j,valid,rfl⟩ := List.mem_map.mp member
    exact truth.mp rfl j (List.mem_range.mp valid)
  | false =>
    apply Step_pure.vtestop_false _ _ _ _ (const_wf bits) sourceWf
      (.admininstr_case_13 _ _ (unsigned_num_wf .I32 0 (by decide)))
    intro prior
    have nonzero := all_true_prior ty bits prior
    have yes : ∀ j, j < 128/lsize (lanetype_Jnn ty) →
        (vectorLane (lanetype_Jnn ty) bits j).toNat ≠ 0 := by
      intro j valid
      have member : lane_.mk_lane__0 ty (.mk_uN (vectorLane (lanetype_Jnn ty) bits j).toNat) ∈ inputs :=
        List.mem_map.mpr ⟨j,List.mem_range.mpr valid,rfl⟩
      rw [inputEq] at member
      exact nonzero _ member
    have impossible := truth.mpr yes
    cases impossible
end Itasca.Spec.Simd

end

/-! ## Bitmask -/

section

/-!
SIMD lane bitmasks and their bit-level characterization, connecting source operations with the interpreter bit representation.
-/

/-! ## Simd Bitmask Bits -/

section

namespace Itasca.Spec.Simd
open WebAssembly.Builtins

theorem integer_bits_reverse (width : Nat) (bits : BitVec width) :
    integerBits width bits.reverse.toNat = (integerBits width bits.toNat).reverse := by
  apply List.ext_getElem
  · simp [integer_bits_length]
  · intro i left right
    have valid : i < width := by simpa only [integer_bits_length] using left
    rw [integer_bits_get_msb _ _ _ valid,List.getElem_reverse]
    simp only [integer_bits_length]
    rw [integer_bits_get_msb _ _ _ (by omega)]
    simp [BitVec.getMsbD_reverse,BitVec.getLsbD_reverse,BitVec.getMsbD_eq_getLsbD,valid]

theorem irev_reverse (width : Nat) (bits : BitVec width) :
    irev_ width (.mk_uN bits.reverse.toNat) = .mk_uN bits.toNat := by
  unfold irev_ ibits_ inv_ibits_
  simp only [proj_uN_0,integer_bits_reverse,List.reverse_reverse,integer_bits_roundtrip bits.isLt]
end Itasca.Spec.Simd

end

/-! ## Simd Bitmask -/

section

namespace Itasca.Spec.Simd
open WebAssembly.Builtins

def bitmaskSource (ty : Jnn) : admininstr :=
  .VBITMASK (.mk_ishape (shapeOf (lanetype_Jnn ty)))

theorem bitmask_lane (width : Nat) (bits : BitVec width) :
    fun_ilt_ width .S (.mk_uN bits.toNat) (.mk_uN 0) (.mk_uN bits.msb.toNat) := by
  have relation := fun_ilt_.fun_ilt__case_1 width (.mk_uN bits.toNat) (.mk_uN 0)
    (0 : Int) bits.toInt (by simpa only [BitVec.toNat_zero,BitVec.toInt_zero,proj_uN_0] using bitvec_signed width (0#width)) (bitvec_signed width bits)
    (boolean_u32_wf (decide (bits.toInt < 0)))
  have boolean : decide (bits.toInt < 0) = bits.msb := by
    exact Bool.eq_iff_iff.mpr (by simp only [decide_eq_true_eq,BitVec.msb_eq_true_iff_two_mul_ge,BitVec.toInt_neg_iff])
  cases h : bits.msb <;> simpa [nat_of_bool,boolean,h,Bool.toNat] using relation

theorem bitmask_step (ty : Jnn) (bits : BitVec 128) (result : BitVec 32)
    (mask : ∀ i, i<32 → result.getLsbD i =
      if i < 128/lsize (lanetype_Jnn ty) then (vectorLane (lanetype_Jnn ty) bits i).msb else false) :
    Step_pure [.VCONST .V128 (.mk_uN bits.toNat),bitmaskSource ty]
      [.CONST .I32 (.mk_num__0 .I32 (.mk_uN result.toNat))] := by
  let count := 128/lsize (lanetype_Jnn ty)
  have countBound : count ≤ 32 := by cases ty <;> decide
  let inputs := (List.range count).map
    (fun j => lane_.mk_lane__0 ty (.mk_uN (vectorLane (lanetype_Jnn ty) bits j).toNat))
  let outputs := (List.range count).map
    (fun j => uN.mk_uN (vectorLane (lanetype_Jnn ty) bits j).msb.toNat)
  have inputEq : inputs = lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN bits.toNat) := by
    rw [vector_lanes]; cases ty <;> rfl
  have projected : Forall (fun lane => proj_lane__0 lane ≠ none) inputs := by
    intro lane member
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
    simp [proj_lane__0]
  have related : Forall₂ (fun out lane => fun_ilt_ (lsize (lanetype_Jnn ty)) .S
      (Option.get! (proj_lane__0 lane)) (.mk_uN 0) out) outputs inputs := by
    intro pair member
    rw [List.zip_map'] at member
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
    exact bitmask_lane _ _
  have listEq : ibits_ 32 (.mk_uN result.reverse.toNat) =
      outputs.map (fun out => bit.mk_bit (proj_uN_0 out)) ++
        List.replicate (Int.toNat ((32:Int)-count)) (.mk_bit 0) := by
    have countInt : Int.toNat ((32:Int)-count) = 32-count := by omega
    rw [countInt]
    apply List.ext_getElem
    · simp [ibits_,integer_bits_length,outputs]; omega
    · intro i left right
      have valid : i<32 := by simpa only [ibits_,integer_bits_length] using left
      simp only [ibits_,proj_uN_0]
      rw [integer_bits_get_msb 32 result.reverse i valid,BitVec.getMsbD_reverse,mask i valid]
      change bit.mk_bit (if i<count then _ else false).toNat = _
      by_cases within : i<count
      · rw [List.getElem_append_left (by simp only [List.length_map,outputs,List.length_range]; exact within)]
        simp only [outputs,List.getElem_map,List.getElem_range,proj_uN_0,if_pos within]
      · rw [List.getElem_append_right (by simp only [List.length_map,outputs,List.length_range]; omega)]
        simp only [List.getElem_replicate,if_neg within,Bool.toNat_false]
  have outputWf : Forall (fun out => wf_bit (.mk_bit (proj_uN_0 out))) outputs := by
    intro out member
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
    cases (vectorLane (lanetype_Jnn ty) bits j).msb <;> constructor <;> simp [proj_uN_0]
  have reverseEq := irev_reverse 32 result
  rw [←reverseEq]
  apply Step_pure.vbitmask _ ty count _ inputs outputs
  · simp [inputs,outputs]
  · exact projected
  · exact related
  · exact inputEq
  · exact listEq
  · exact const_wf bits
  · apply wf_admininstr.admininstr_case_30
    exact .ishape_case_0 ty _ (shape_of_wf _) rfl
  · rw [reverseEq]
    exact .admininstr_case_13 _ _ (unsigned_num_wf .I32 result.toNat result.isLt)
  · exact shape_of_wf _
  · exact outputWf
  · constructor; simp
end Itasca.Spec.Simd

end

end

/-! ## Popcount -/

section

/-!
Lane-word and source interpretations of population count.

Main declarations: `popcountWords` and `popcountSource`.
-/

namespace Itasca.Spec.Simd
open WebAssembly.Builtins

def popcountWords (bits : BitVec 128) : List uN :=
  (List.range 16).map (fun j => .mk_uN (population (integerBits 8 (vectorLane .I8 bits j).toNat)))

def popcountSource : admininstr :=
  .VUNOP (shapeOf .I8) (.mk_vunop__0 .I8 16 .POPCNT)

theorem popcount_step (bits result : BitVec 128)
    (packed : uN.mk_uN result.toNat = inv_lanes_ (shapeOf .I8)
      ((popcountWords bits).map (lane_.mk_lane__0 .I8))) :
    Step_pure [.VCONST .V128 (.mk_uN bits.toNat),popcountSource]
      [.VCONST .V128 (.mk_uN result.toNat)] := by
  let inputs := (List.range 16).map
    (fun j => lane_.mk_lane__0 .I8 (.mk_uN (vectorLane .I8 bits j).toNat))
  have inputEq : inputs = lanes_ (shapeOf .I8) (.mk_uN bits.toNat) := by
    rw [vector_lanes]; rfl
  have projected : Forall (fun lane => proj_lane__0 lane ≠ none) inputs := by
    intro lane member
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
    simp [proj_lane__0]
  have resultEq : uN.mk_uN result.toNat = inv_lanes_ (shapeOf .I8)
      (inputs.map (fun lane => lane_.mk_lane__0 .I8 (ipopcnt_ 8 (Option.get! (proj_lane__0 lane))))) := by
    simpa only [popcountWords,inputs,List.map_map,Function.comp_def,ipopcnt_,ibits_,proj_lane__0,Option.get!,proj_uN_0] using packed
  have resultWf : Forall (fun lane => wf_lane_ .I8
      (.mk_lane__0 .I8 (ipopcnt_ 8 (Option.get! (proj_lane__0 lane))))) inputs := by
    intro lane member
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
    apply lane_of_bits_wf .I8
    have bound := population_bits_le 8 (vectorLane .I8 bits j).toNat
    change population (integerBits 8 (vectorLane .I8 bits j).toNat) < 256
    omega
  have related : fun_vunop_ (shapeOf .I8) (.mk_vunop__0 .I8 16 .POPCNT)
      (.mk_uN bits.toNat) (some [.mk_uN result.toNat]) :=
    .fun_vunop__case_10 _ _ _ inputs _ inputEq projected resultEq (shape_of_wf _) projected resultWf rfl
  apply Step_pure.vunop _ _ _ _ (some [.mk_uN result.toNat]) related
  · simp
  · simp
  · simp
  · exact const_wf bits
  · apply wf_admininstr.admininstr_case_25 _ _ (shape_of_wf _)
    apply wf_vunop_.vunop__case_0 _ .I8 16 .POPCNT _ rfl
    exact .vunop_Jnn_N_case_2 _ _ rfl
  · exact const_wf result
end Itasca.Spec.Simd

end

/-! ## Unary -/

section

/-!
Source-rule algebra for integer unary lane operations. Lane/list calculations establish the generated source operation and its reduction step, consumed by source-machine and interpreter correspondence proofs.
-/

/-! ## Simd Unary -/

section

namespace Itasca.Spec.Simd
open WebAssembly.Builtins

theorem negate_lane_relation (width : Nat) (bits : BitVec width) :
    fun_ineg_ width (.mk_uN bits.toNat) (.mk_uN (-bits).toNat) := by
  have bitsEq : BitVec.ofInt width ((2^width : Int)-bits.toNat) = -bits := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofInt,BitVec.toNat_neg]
    have bound := bits.isLt
    have power : (2^width : Int) = ((2^width : Nat) : Int) := by norm_cast
    rw [power,←Int.natCast_sub (by omega : bits.toNat ≤ 2^width),←Int.natCast_emod,Int.toNat_natCast]
  have valueEq := congrArg BitVec.toNat bitsEq
  simp only [BitVec.toNat_ofInt] at valueEq
  rw [←valueEq]
  exact .fun_ineg__case_0 _ _ (unsigned_wf_of_lt width _ (by simp only [proj_uN_0]; convert (-bits).isLt using 1; exact valueEq))

theorem absolute_lane_relation (width : Nat) (bits : BitVec width) (positive : 0 < width) :
    fun_iabs_ width (.mk_uN bits.toNat)
      (.mk_uN (if bits.toInt < 0 then (-bits).toNat else bits.toNat)) := by
  have signed := bitvec_signed width bits
  have relation := fun_iabs_.fun_iabs__case_0 width (.mk_uN bits.toNat) (.mk_uN (-bits).toNat)
    bits.toInt (negate_lane_relation width bits) signed
  split
  · rename_i negative
    simpa [show ¬bits.toInt ≥ 0 by omega] using relation
  · rename_i nonnegative
    simpa [show bits.toInt ≥ 0 by omega] using relation
end Itasca.Spec.Simd

end

/-! ## Simd Unary Source -/

section

namespace Itasca.Spec.Simd
open WebAssembly.Builtins

inductive SignedUnaryKind where | absolute | negate

def signedUnaryBits (kind : SignedUnaryKind) {width : Nat} (bits : BitVec width) : BitVec width :=
  match kind with
  | .absolute => if bits.toInt < 0 then -bits else bits
  | .negate => -bits

def signedUnaryOperation : SignedUnaryKind → vunop_Jnn_N
  | .absolute => .ABS | .negate => .NEG

def signedUnaryRelation : SignedUnaryKind → Nat → uN → uN → Prop
  | .absolute => fun_iabs_ | .negate => fun_ineg_

def signedUnaryWords (ty : Jnn) (kind : SignedUnaryKind) (bits : BitVec 128) : List uN :=
  (List.range (128/lsize (lanetype_Jnn ty))).map (fun j =>
    .mk_uN (signedUnaryBits kind (vectorLane (lanetype_Jnn ty) bits j)).toNat)

def signedUnarySource (ty : Jnn) (kind : SignedUnaryKind) : admininstr :=
  .VUNOP (shapeOf (lanetype_Jnn ty)) (.mk_vunop__0 ty (128/lsize (lanetype_Jnn ty)) (signedUnaryOperation kind))

theorem signed_unary_lane (ty : Jnn) (kind : SignedUnaryKind) (bits : BitVec (lsize (lanetype_Jnn ty))) :
    signedUnaryRelation kind (lsize (lanetype_Jnn ty)) (.mk_uN bits.toNat)
      (.mk_uN (signedUnaryBits kind bits).toNat) := by
  cases kind with
  | absolute =>
    simpa only [signedUnaryRelation,signedUnaryBits,apply_ite] using
      absolute_lane_relation (lsize (lanetype_Jnn ty)) bits (by cases ty <;> decide)
  | negate => exact negate_lane_relation _ bits

theorem signed_unary_relation (ty : Jnn) (kind : SignedUnaryKind) (bits result : BitVec 128)
    (packed : uN.mk_uN result.toNat = inv_lanes_ (shapeOf (lanetype_Jnn ty))
      ((signedUnaryWords ty kind bits).map (lane_.mk_lane__0 ty))) :
    fun_vunop_ (shapeOf (lanetype_Jnn ty))
      (.mk_vunop__0 ty (128/lsize (lanetype_Jnn ty)) (signedUnaryOperation kind))
      (.mk_uN bits.toNat) (some [.mk_uN result.toNat]) := by
  let inputs := (List.range (128/lsize (lanetype_Jnn ty))).map
    (fun j => lane_.mk_lane__0 ty (.mk_uN (vectorLane (lanetype_Jnn ty) bits j).toNat))
  let outputs := signedUnaryWords ty kind bits
  have inputEq : inputs = lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN bits.toNat) := by
    rw [vector_lanes]
    cases ty <;> rfl
  have lengthEq : outputs.length = inputs.length := by simp [outputs,inputs,signedUnaryWords]
  have projected : Forall (fun lane => proj_lane__0 lane ≠ none) inputs := by
    intro lane member
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
    simp [proj_lane__0]
  have related : Forall₂ (fun out lane => signedUnaryRelation kind (lsize (lanetype_Jnn ty))
      (Option.get! (proj_lane__0 lane)) out) outputs inputs := by
    dsimp only [outputs,inputs,signedUnaryWords]
    intro pair member
    rw [List.zip_map'] at member
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
    exact signed_unary_lane ty kind (vectorLane (lanetype_Jnn ty) bits j)
  have outputWf : Forall (fun word => wf_lane_ (lanetype_Jnn ty) (.mk_lane__0 ty word)) outputs := by
    intro word member
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
    have wf := lane_of_bits_wf (lanetype_Jnn ty)
      (signedUnaryBits kind (vectorLane (lanetype_Jnn ty) bits j)).toNat (BitVec.toNat_lt_twoPow_of_le (by rfl))
    cases ty <;> exact wf
  cases kind <;> cases ty
  all_goals first
    | exact .fun_vunop__case_0 _ _ _ inputs _ outputs outputs lengthEq projected related lengthEq projected related inputEq packed (shape_of_wf _) outputWf rfl
    | exact .fun_vunop__case_1 _ _ _ inputs _ outputs outputs lengthEq projected related lengthEq projected related inputEq packed (shape_of_wf _) outputWf rfl
    | exact .fun_vunop__case_2 _ _ _ inputs _ outputs outputs lengthEq projected related lengthEq projected related inputEq packed (shape_of_wf _) outputWf rfl
    | exact .fun_vunop__case_3 _ _ _ inputs _ outputs outputs lengthEq projected related lengthEq projected related inputEq packed (shape_of_wf _) outputWf rfl
    | exact .fun_vunop__case_4 _ _ _ inputs _ outputs outputs lengthEq projected related lengthEq projected related inputEq packed (shape_of_wf _) outputWf rfl
    | exact .fun_vunop__case_5 _ _ _ inputs _ outputs outputs lengthEq projected related lengthEq projected related inputEq packed (shape_of_wf _) outputWf rfl
    | exact .fun_vunop__case_6 _ _ _ inputs _ outputs outputs lengthEq projected related lengthEq projected related inputEq packed (shape_of_wf _) outputWf rfl
    | exact .fun_vunop__case_7 _ _ _ inputs _ outputs outputs lengthEq projected related lengthEq projected related inputEq packed (shape_of_wf _) outputWf rfl

theorem signed_unary_step (ty : Jnn) (kind : SignedUnaryKind) (bits result : BitVec 128)
    (packed : uN.mk_uN result.toNat = inv_lanes_ (shapeOf (lanetype_Jnn ty))
      ((signedUnaryWords ty kind bits).map (lane_.mk_lane__0 ty))) :
    Step_pure [.VCONST .V128 (.mk_uN bits.toNat),signedUnarySource ty kind]
      [.VCONST .V128 (.mk_uN result.toNat)] := by
  apply Step_pure.vunop _ _ _ _ (some [.mk_uN result.toNat])
  · exact signed_unary_relation ty kind bits result packed
  · simp
  · simp
  · simp
  · exact const_wf bits
  · apply wf_admininstr.admininstr_case_25 _ _ (shape_of_wf _)
    apply wf_vunop_.vunop__case_0 _ _ _ _ _ rfl
    cases kind <;> constructor
  · exact const_wf result
end Itasca.Spec.Simd

end

end

/-! ## FloatBinary -/

section

/-!
Source-rule algebra for binary floating-point lanes. Lane/list calculations establish the generated source operation and its reduction step, consumed by source-machine and interpreter correspondence proofs.
-/

/-! ## Simd Float Binary -/

section

namespace Itasca.Spec.Simd
open WebAssembly.Builtins WebAssembly.Builtins.Float

def floatBinaryChoices (width : Nat) (op : vbinop_Fnn_N) (a b : fN) : List fN :=
  match op with
  | .ADD => fadd_ width a b
  | .SUB => fsub_ width a b
  | .MUL => fmul_ width a b
  | .DIV => fdiv_ width a b
  | .MIN => fmin_ width a b
  | .MAX => fmax_ width a b
  | .PMIN => fpmin_ width a b
  | .PMAX => fpmax_ width a b

def floatBinarySource (ty : Fnn) (op : vbinop_Fnn_N) : vbinop_ :=
  .mk_vbinop__1 ty (128/lsize (lanetype_Fnn ty)) op

theorem float_binary_source_wf (ty : Fnn) (op : vbinop_Fnn_N) :
    wf_vbinop_ (shapeOf (lanetype_Fnn ty)) (floatBinarySource ty op) := by
  cases ty <;> cases op <;> constructor <;> constructor

theorem float_binary_choices_wf (width : Nat) (supported : width = 32 ∨ width = 64)
    (op : vbinop_Fnn_N) (a b : fN) (firstWf : wf_fN width a) (secondWf : wf_fN width b) :
    Forall (wf_fN width) (floatBinaryChoices width op a b) := by
  cases op with
  | ADD => exact add_wf width supported a b firstWf secondWf
  | SUB => exact sub_wf width supported a b firstWf secondWf
  | MUL => exact mul_wf width supported a b
  | DIV => exact div_wf width supported a b
  | MIN => exact float_min_wf width supported a b firstWf secondWf
  | MAX => exact float_max_wf width supported a b firstWf secondWf
  | PMIN =>
    intro result member
    simp only [floatBinaryChoices,fpmin_,List.mem_singleton] at member
    subst result
    split <;> assumption
  | PMAX =>
    intro result member
    simp only [floatBinaryChoices,fpmax_,List.mem_singleton] at member
    subst result
    split <;> assumption

end Itasca.Spec.Simd

end

/-! ## Simd Float Binary Source -/

section

namespace Itasca.Spec.Simd
open WebAssembly.Builtins WebAssembly.Builtins.Float

def floatBinaryLaneChoices (ty : Fnn) (op : vbinop_Fnn_N) (a b : lane_) : List lane_ :=
  Map (lane_.mk_lane__1 ty) (floatBinaryChoices (lsize (lanetype_Fnn ty)) op
    (Option.get! (proj_lane__1 a)) (Option.get! (proj_lane__1 b)))

def floatBinaryResults (ty : Fnn) (op : vbinop_Fnn_N) (x y : BitVec 128) : List uN :=
  Map (inv_lanes_ (shapeOf (lanetype_Fnn ty)))
    (setproduct_ lane_ (Map₂ (floatBinaryLaneChoices ty op)
      (lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN x.toNat))
      (lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN y.toNat))))

theorem float_binary_lanes_wf (ty : Fnn) (op : vbinop_Fnn_N) (x y : BitVec 128) :
    Forall₂ (fun a b => Forall (fun value => wf_lane_ (lanetype_Fnn ty) (.mk_lane__1 ty value))
      (floatBinaryChoices (lsize (lanetype_Fnn ty)) op
        (Option.get! (proj_lane__1 a)) (Option.get! (proj_lane__1 b))))
      (lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN x.toNat))
      (lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN y.toNat)) := by
  rw [lanes_map_words,lanes_map_words]
  apply forall2_map
  intro j member value allowed
  have wfInput (bits : BitVec 128) : wf_fN (lsize (lanetype_Fnn ty))
      (Option.get! (proj_lane__1 (laneOfBits (lanetype_Fnn ty) (laneWord (lanetype_Fnn ty) bits j).toNat))) := by
    cases ty <;> exact float_of_bits_wf _ (by decide) _
  have wf := float_binary_choices_wf (lsize (lanetype_Fnn ty)) (by cases ty <;> decide)
    op _ _ (wfInput x) (wfInput y) value allowed
  cases ty <;> exact .lane__case_1 _ _ _ wf rfl

theorem float_binary_relation (ty : Fnn) (op : vbinop_Fnn_N) (x y : BitVec 128) :
    fun_vbinop_ (shapeOf (lanetype_Fnn ty)) (floatBinarySource ty op)
      (.mk_uN x.toNat) (.mk_uN y.toNat) (some (floatBinaryResults ty op x y)) := by
  have shapeWf := shape_of_wf (lanetype_Fnn ty)
  have lanesWf := float_binary_lanes_wf ty op x y
  have lengths : (lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN x.toNat)).length =
      (lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN y.toNat)).length := by
    rw [lanes_map_words,lanes_map_words,List.length_map,List.length_map]
  cases ty <;> cases op
  · apply fun_vbinop_.fun_vbinop__case_36
    all_goals first | rfl | exact shapeWf | exact lanesWf | exact lengths
  · apply fun_vbinop_.fun_vbinop__case_38
    all_goals first | rfl | exact shapeWf | exact lanesWf | exact lengths
  · apply fun_vbinop_.fun_vbinop__case_40
    all_goals first | rfl | exact shapeWf | exact lanesWf | exact lengths
  · apply fun_vbinop_.fun_vbinop__case_42
    all_goals first | rfl | exact shapeWf | exact lanesWf | exact lengths
  · apply fun_vbinop_.fun_vbinop__case_44
    all_goals first | rfl | exact shapeWf | exact lanesWf | exact lengths
  · apply fun_vbinop_.fun_vbinop__case_46
    all_goals first | rfl | exact shapeWf | exact lanesWf | exact lengths
  · apply fun_vbinop_.fun_vbinop__case_48
    all_goals first | rfl | exact shapeWf | exact lanesWf | exact lengths
  · apply fun_vbinop_.fun_vbinop__case_50
    all_goals first | rfl | exact shapeWf | exact lanesWf | exact lengths
  · apply fun_vbinop_.fun_vbinop__case_37
    all_goals first | rfl | exact shapeWf | exact lanesWf | exact lengths
  · apply fun_vbinop_.fun_vbinop__case_39
    all_goals first | rfl | exact shapeWf | exact lanesWf | exact lengths
  · apply fun_vbinop_.fun_vbinop__case_41
    all_goals first | rfl | exact shapeWf | exact lanesWf | exact lengths
  · apply fun_vbinop_.fun_vbinop__case_43
    all_goals first | rfl | exact shapeWf | exact lanesWf | exact lengths
  · apply fun_vbinop_.fun_vbinop__case_45
    all_goals first | rfl | exact shapeWf | exact lanesWf | exact lengths
  · apply fun_vbinop_.fun_vbinop__case_47
    all_goals first | rfl | exact shapeWf | exact lanesWf | exact lengths
  · apply fun_vbinop_.fun_vbinop__case_49
    all_goals first | rfl | exact shapeWf | exact lanesWf | exact lengths
  · apply fun_vbinop_.fun_vbinop__case_51
    all_goals first | rfl | exact shapeWf | exact lanesWf | exact lengths

end Itasca.Spec.Simd

end

/-! ## Simd Float Binary Choices -/

section

namespace Itasca.Spec.Simd
open WebAssembly.Builtins

theorem float_binary_result_member (ty : Fnn) (op : vbinop_Fnn_N) (x y result : BitVec 128)
    (allowed : ∀ j, j < 128/lsize (lanetype_Fnn ty) →
      floatOfBits (lsize (lanetype_Fnn ty)) (laneWord (lanetype_Fnn ty) result j).toNat ∈
        floatBinaryChoices (lsize (lanetype_Fnn ty)) op
          (floatOfBits (lsize (lanetype_Fnn ty)) (laneWord (lanetype_Fnn ty) x j).toNat)
          (floatOfBits (lsize (lanetype_Fnn ty)) (laneWord (lanetype_Fnn ty) y j).toNat)) :
    uN.mk_uN result.toNat ∈ floatBinaryResults ty op x y := by
  apply List.mem_map.mpr
  refine ⟨lanes_ (shapeOf (lanetype_Fnn ty)) (.mk_uN result.toNat),?_,lanes_roundtrip _ result⟩
  rw [lanes_map_words,lanes_map_words,lanes_map_words]
  rw [map2_map]
  apply mem_setproduct_map
  intro j member
  have chosen := allowed j (List.mem_range.mp member)
  cases ty <;> exact List.mem_map.mpr ⟨_,chosen,rfl⟩

theorem float_binary_step (ty : Fnn) (op : vbinop_Fnn_N) (x y result : BitVec 128)
    (allowed : ∀ j, j < 128/lsize (lanetype_Fnn ty) →
      floatOfBits (lsize (lanetype_Fnn ty)) (laneWord (lanetype_Fnn ty) result j).toNat ∈
        floatBinaryChoices (lsize (lanetype_Fnn ty)) op
          (floatOfBits (lsize (lanetype_Fnn ty)) (laneWord (lanetype_Fnn ty) x j).toNat)
          (floatOfBits (lsize (lanetype_Fnn ty)) (laneWord (lanetype_Fnn ty) y j).toNat)) :
    Step_pure [.VCONST .V128 (.mk_uN x.toNat),.VCONST .V128 (.mk_uN y.toNat),
      .VBINOP (shapeOf (lanetype_Fnn ty)) (floatBinarySource ty op)] [.VCONST .V128 (.mk_uN result.toNat)] := by
  have chosen := float_binary_result_member ty op x y result allowed
  apply Step_pure.vbinop_val _ _ _ _ _ (some (floatBinaryResults ty op x y)) (float_binary_relation ty op x y)
  · exact List.length_pos_of_mem chosen
  · simp
  · simpa only [Option.get!_some,List.contains_iff_mem] using chosen
  · exact const_wf x
  · exact const_wf y
  · exact .admininstr_case_26 _ _ (shape_of_wf _) (float_binary_source_wf ty op)
  · exact const_wf result

end Itasca.Spec.Simd

end

end

/-! ## Average -/

section

/-!
Rounded lane averages and their supported shapes.

Main declarations: `averageBits` and `averageSupported`.
-/

set_option maxHeartbeats 800000
namespace Itasca.Spec.Simd
open WebAssembly.Builtins

def averageBits {width : Nat} (a b : BitVec width) : BitVec width :=
  BitVec.ofNat width ((a.toNat+b.toNat+1)/2)

theorem average_bits_value {width : Nat} (a b : BitVec width) :
    (averageBits a b).toNat = (a.toNat+b.toNat+1)/2 := by
  have ha := a.isLt
  have hb := b.isLt
  simp only [averageBits,BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega)]

def averageSupported (ty : Jnn) : Prop :=
  match ty with | .I8 | .I16 => True | _ => False

def averageSource (ty : Jnn) : vbinop_ :=
  .mk_vbinop__0 ty (128/lsize (lanetype_Jnn ty)) .AVGRU

theorem average_source_wf (ty : Jnn) (supported : averageSupported ty) :
    wf_vbinop_ (shapeOf (lanetype_Jnn ty)) (averageSource ty) := by
  cases ty <;> simp only [averageSupported] at supported
  all_goals try contradiction
  all_goals constructor <;> constructor
  all_goals decide

def averageWords (ty : Jnn) (x y : BitVec 128) : List uN :=
  (List.range (128/lsize (lanetype_Jnn ty))).map (fun j =>
    .mk_uN (averageBits (laneWord (lanetype_Jnn ty) x j) (laneWord (lanetype_Jnn ty) y j)).toNat)

def averageResult (ty : Jnn) (x y : BitVec 128) : uN :=
  inv_lanes_ (shapeOf (lanetype_Jnn ty)) (Map (lane_.mk_lane__0 ty) (averageWords ty x y))

theorem average_lanes_map (ty : Jnn) (x y : BitVec 128) :
    Map₂ (fun a b => lane_.mk_lane__0 ty (iavgr_ (lsize (lanetype_Jnn ty)) .U
      (Option.get! (proj_lane__0 a)) (Option.get! (proj_lane__0 b))))
      (lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN x.toNat))
      (lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN y.toNat)) =
        Map (lane_.mk_lane__0 ty) (averageWords ty x y) := by
  rw [lanes_map_words,lanes_map_words,map2_map]
  simp only [averageWords,Map,List.map_map]
  apply List.map_congr_left
  intro j member
  cases ty <;> simp only [laneOfBits,proj_lane__0,Option.get!,iavgr_,proj_uN_0,average_bits_value]
  all_goals rfl

theorem average_lanes_wf (ty : Jnn) (x y : BitVec 128) :
    Forall₂ (fun a b => wf_lane_ (lanetype_Jnn ty) (lane_.mk_lane__0 ty (iavgr_ (lsize (lanetype_Jnn ty)) .U
      (Option.get! (proj_lane__0 a)) (Option.get! (proj_lane__0 b)))))
      (lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN x.toNat))
      (lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN y.toNat)) := by
  rw [lanes_map_words,lanes_map_words]
  apply forall2_map
  intro j member
  have wf := unsigned_wf_of_lt (lsize (lanetype_Jnn ty))
    (averageBits (laneWord (lanetype_Jnn ty) x j) (laneWord (lanetype_Jnn ty) y j)).toNat (BitVec.isLt _)
  rw [average_bits_value] at wf
  cases ty <;> exact .lane__case_0 _ _ _ wf rfl

theorem average_vector_relation (ty : Jnn) (x y : BitVec 128) :
    fun_vbinop_ (shapeOf (lanetype_Jnn ty)) (averageSource ty)
      (.mk_uN x.toNat) (.mk_uN y.toNat) (some [averageResult ty x y]) := by
  have shapeWf := shape_of_wf (lanetype_Jnn ty)
  have wf := average_lanes_wf ty x y
  have packed := congrArg (inv_lanes_ (shapeOf (lanetype_Jnn ty))) (average_lanes_map ty x y)
  have nonX := integer_lanes_nonempty ty x
  have nonY := integer_lanes_nonempty ty y
  have lengths : (lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN x.toNat)).length =
      (lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN y.toNat)).length := by
    rw [lanes_map_words,lanes_map_words,List.length_map,List.length_map]
  cases ty with
  | I32 => exact .fun_vbinop__case_28 _ _ _ _ _ _ _ rfl rfl nonX nonY packed.symm shapeWf lengths nonX nonY wf rfl
  | I64 => exact .fun_vbinop__case_29 _ _ _ _ _ _ _ rfl rfl nonX nonY packed.symm shapeWf lengths nonX nonY wf rfl
  | I8 => exact .fun_vbinop__case_30 _ _ _ _ _ _ _ rfl rfl nonX nonY packed.symm shapeWf lengths nonX nonY wf rfl
  | I16 => exact .fun_vbinop__case_31 _ _ _ _ _ _ _ rfl rfl nonX nonY packed.symm shapeWf lengths nonX nonY wf rfl

theorem average_step (ty : Jnn) (x y result : BitVec 128)
    (supported : averageSupported ty) (packed : uN.mk_uN result.toNat = averageResult ty x y) :
    Step_pure [.VCONST .V128 (.mk_uN x.toNat),.VCONST .V128 (.mk_uN y.toNat),
      .VBINOP (shapeOf (lanetype_Jnn ty)) (averageSource ty)] [.VCONST .V128 (.mk_uN result.toNat)] := by
  apply Step_pure.vbinop_val _ _ _ _ _ (some [.mk_uN result.toNat])
  · rw [packed]; exact average_vector_relation ty x y
  · change 0 < 1; decide
  · simp
  · simp
  · exact const_wf x
  · exact const_wf y
  · exact .admininstr_case_26 _ _ (shape_of_wf _) (average_source_wf ty supported)
  · exact const_wf result

end Itasca.Spec.Simd

end

/-! ## IntegerMinMax -/

section

/-!
Source-rule algebra for signed and unsigned integer minima and maxima. Lane/list calculations establish the generated source operation and its reduction step, consumed by source-machine and interpreter correspondence proofs.
-/

/-! ## Simd Integer Min Max -/

section

namespace Itasca.Spec.Simd

inductive IntegerMinMax where | minS | minU | maxS | maxU

def integerMinMaxBits (kind : IntegerMinMax) {width : Nat} (a b : BitVec width) : BitVec width :=
  match kind with
  | .minS => if a.toInt < b.toInt then a else b
  | .minU => if a.toNat < b.toNat then a else b
  | .maxS => if a.toInt > b.toInt then a else b
  | .maxU => if a.toNat > b.toNat then a else b

def IntegerMinMaxRel (kind : IntegerMinMax) (width : Nat) (a b result : uN) : Prop :=
  match kind with
  | .minS => fun_imin_ width .S a b result
  | .minU => fun_imin_ width .U a b result
  | .maxS => fun_imax_ width .S a b result
  | .maxU => fun_imax_ width .U a b result

theorem integer_minmax_relation (kind : IntegerMinMax) {width : Nat} (a b : BitVec width) :
    IntegerMinMaxRel kind width (.mk_uN a.toNat) (.mk_uN b.toNat)
      (.mk_uN (integerMinMaxBits kind a b).toNat) := by
  cases kind with
  | minU =>
    by_cases h : a.toNat < b.toNat
    · simpa [IntegerMinMaxRel,integerMinMaxBits,h] using
        fun_imin_.fun_imin__case_0 width (.mk_uN a.toNat) (.mk_uN b.toNat) (Nat.le_of_lt h)
    · by_cases same : a.toNat = b.toNat
      · have eq := BitVec.eq_of_toNat_eq same
        subst b
        simpa [IntegerMinMaxRel,integerMinMaxBits] using
          fun_imin_.fun_imin__case_0 width (.mk_uN a.toNat) (.mk_uN a.toNat) (Nat.le_refl _)
      · simpa [IntegerMinMaxRel,integerMinMaxBits,h] using
          fun_imin_.fun_imin__case_1 width (.mk_uN a.toNat) (.mk_uN b.toNat) (by simp only [proj_uN_0]; omega)
  | maxU =>
    by_cases h : a.toNat > b.toNat
    · simpa [IntegerMinMaxRel,integerMinMaxBits,h] using
        fun_imax_.fun_imax__case_0 width (.mk_uN a.toNat) (.mk_uN b.toNat) (Nat.le_of_lt h)
    · by_cases same : a.toNat = b.toNat
      · have eq := BitVec.eq_of_toNat_eq same
        subst b
        simpa [IntegerMinMaxRel,integerMinMaxBits] using
          fun_imax_.fun_imax__case_0 width (.mk_uN a.toNat) (.mk_uN a.toNat) (Nat.le_refl _)
      · simpa [IntegerMinMaxRel,integerMinMaxBits,h] using
          fun_imax_.fun_imax__case_1 width (.mk_uN a.toNat) (.mk_uN b.toNat) (by simp only [proj_uN_0]; omega)
  | minS =>
    have source := fun_imin_.fun_imin__case_2 width (.mk_uN a.toNat) (.mk_uN b.toNat) _ _ (bitvec_signed _ b) (bitvec_signed _ a)
    by_cases same : a.toInt = b.toInt
    · have eq := BitVec.eq_of_toInt_eq same
      subst b
      simpa [IntegerMinMaxRel,integerMinMaxBits] using source
    · by_cases h : a.toInt < b.toInt
      · simpa [IntegerMinMaxRel,integerMinMaxBits,h,Int.le_of_lt h] using source
      · simpa [IntegerMinMaxRel,integerMinMaxBits,h,show ¬a.toInt ≤ b.toInt by omega] using source
  | maxS =>
    have source := fun_imax_.fun_imax__case_2 width (.mk_uN a.toNat) (.mk_uN b.toNat) _ _ (bitvec_signed _ b) (bitvec_signed _ a)
    by_cases same : a.toInt = b.toInt
    · have eq := BitVec.eq_of_toInt_eq same
      subst b
      simpa [IntegerMinMaxRel,integerMinMaxBits] using source
    · by_cases h : a.toInt > b.toInt
      · simpa [IntegerMinMaxRel,integerMinMaxBits,h,Int.le_of_lt h] using source
      · simpa [IntegerMinMaxRel,integerMinMaxBits,h,show ¬a.toInt ≥ b.toInt by omega] using source

end Itasca.Spec.Simd

end

/-! ## Simd Integer Min Max Shape -/

section

namespace Itasca.Spec.Simd

def integerMinMaxSupported (ty : Jnn) (_kind : IntegerMinMax) : Prop :=
  match ty with | .I64 => False | _ => True

def integerMinMaxOp (kind : IntegerMinMax) : vbinop_Jnn_N :=
  match kind with | .minS => .MIN .S | .minU => .MIN .U | .maxS => .MAX .S | .maxU => .MAX .U

def integerMinMaxSource (ty : Jnn) (kind : IntegerMinMax) : vbinop_ :=
  .mk_vbinop__0 ty (128/lsize (lanetype_Jnn ty)) (integerMinMaxOp kind)

theorem integer_minmax_source_wf (ty : Jnn) (kind : IntegerMinMax)
    (supported : integerMinMaxSupported ty kind) :
    wf_vbinop_ (shapeOf (lanetype_Jnn ty)) (integerMinMaxSource ty kind) := by
  cases ty <;> cases kind <;> simp only [integerMinMaxSupported] at supported
  all_goals try contradiction
  all_goals constructor <;> constructor
  all_goals decide

end Itasca.Spec.Simd

end

/-! ## Simd Integer Min Max Lists -/

section

namespace Itasca.Spec.Simd
open WebAssembly.Builtins

def minmaxWords (ty : Jnn) (kind : IntegerMinMax) (x y : BitVec 128) : List uN :=
  (List.range (128/lsize (lanetype_Jnn ty))).map (fun j =>
    .mk_uN (integerMinMaxBits kind (laneWord (lanetype_Jnn ty) x j) (laneWord (lanetype_Jnn ty) y j)).toNat)

theorem minmax_words_relation (ty : Jnn) (kind : IntegerMinMax) (x y : BitVec 128) :
    Forall₃ (fun result a b => IntegerMinMaxRel kind (lsize (lanetype_Jnn ty))
      (Option.get! (proj_lane__0 a)) (Option.get! (proj_lane__0 b)) result)
      (minmaxWords ty kind x y)
      (lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN x.toNat))
      (lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN y.toNat)) := by
  rw [lanes_map_words,lanes_map_words]
  apply forall3_map
  intro j member
  have relation := integer_minmax_relation kind (laneWord (lanetype_Jnn ty) x j) (laneWord (lanetype_Jnn ty) y j)
  cases ty <;> exact relation

theorem minmax_words_length (ty : Jnn) (kind : IntegerMinMax) (x y : BitVec 128) :
    (minmaxWords ty kind x y).length = 128/lsize (lanetype_Jnn ty) := by
  simp [minmaxWords]

theorem minmax_words_wf (ty : Jnn) (kind : IntegerMinMax) (x y : BitVec 128) :
    Forall (fun word => wf_lane_ (lanetype_Jnn ty) (.mk_lane__0 ty word)) (minmaxWords ty kind x y) := by
  intro word member
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
  cases ty <;> constructor
  all_goals first | rfl | exact unsigned_wf_of_lt _ _ (BitVec.isLt _)

end Itasca.Spec.Simd

end

/-! ## Simd Integer Min Max Source -/

section

namespace Itasca.Spec.Simd
open WebAssembly.Builtins

def integerMinMaxResult (ty : Jnn) (kind : IntegerMinMax) (x y : BitVec 128) : uN :=
  inv_lanes_ (shapeOf (lanetype_Jnn ty))
    (Map (lane_.mk_lane__0 ty) (minmaxWords ty kind x y))

theorem integer_minmax_vector_relation (ty : Jnn) (kind : IntegerMinMax) (x y : BitVec 128) :
    fun_vbinop_ (shapeOf (lanetype_Jnn ty)) (integerMinMaxSource ty kind)
      (.mk_uN x.toNat) (.mk_uN y.toNat) (some [integerMinMaxResult ty kind x y]) := by
  have lenX : (minmaxWords ty kind x y).length =
      (lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN x.toNat)).length := by
    rw [minmax_words_length,lanes_map_words,List.length_map,List.length_range]
  have lenY : (minmaxWords ty kind x y).length =
      (lanes_ (shapeOf (lanetype_Jnn ty)) (.mk_uN y.toNat)).length := by
    rw [minmax_words_length,lanes_map_words,List.length_map,List.length_range]
  have nonX := integer_lanes_nonempty ty x
  have nonY := integer_lanes_nonempty ty y
  have relation := minmax_words_relation ty kind x y
  have maskWf := minmax_words_wf ty kind x y
  have shapeWf := shape_of_wf (lanetype_Jnn ty)
  cases ty <;> cases kind
  all_goals first
    | apply fun_vbinop_.fun_vbinop__case_8 (var_1_lst := minmaxWords _ _ x y) (var_0_lst := minmaxWords _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat))
    | apply fun_vbinop_.fun_vbinop__case_9 (var_1_lst := minmaxWords _ _ x y) (var_0_lst := minmaxWords _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat))
    | apply fun_vbinop_.fun_vbinop__case_10 (var_1_lst := minmaxWords _ _ x y) (var_0_lst := minmaxWords _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat))
    | apply fun_vbinop_.fun_vbinop__case_11 (var_1_lst := minmaxWords _ _ x y) (var_0_lst := minmaxWords _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat))
    | apply fun_vbinop_.fun_vbinop__case_12 (var_1_lst := minmaxWords _ _ x y) (var_0_lst := minmaxWords _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat))
    | apply fun_vbinop_.fun_vbinop__case_13 (var_1_lst := minmaxWords _ _ x y) (var_0_lst := minmaxWords _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat))
    | apply fun_vbinop_.fun_vbinop__case_14 (var_1_lst := minmaxWords _ _ x y) (var_0_lst := minmaxWords _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat))
    | apply fun_vbinop_.fun_vbinop__case_15 (var_1_lst := minmaxWords _ _ x y) (var_0_lst := minmaxWords _ _ x y) (lane_1_lst := lanes_ (shapeOf _) (.mk_uN x.toNat)) (lane_2_lst := lanes_ (shapeOf _) (.mk_uN y.toNat))
  all_goals first
    | rfl
    | exact lenX
    | exact lenY
    | exact nonX
    | exact nonY
    | exact shapeWf
    | exact maskWf
    | exact relation

end Itasca.Spec.Simd

end

/-! ## Simd Integer Min Max Step -/

section

namespace Itasca.Spec.Simd

theorem integer_minmax_step (ty : Jnn) (kind : IntegerMinMax) (x y result : BitVec 128)
    (supported : integerMinMaxSupported ty kind)
    (packed : uN.mk_uN result.toNat = integerMinMaxResult ty kind x y) :
    Step_pure [.VCONST .V128 (.mk_uN x.toNat),.VCONST .V128 (.mk_uN y.toNat),
      .VBINOP (shapeOf (lanetype_Jnn ty)) (integerMinMaxSource ty kind)]
      [.VCONST .V128 (.mk_uN result.toNat)] := by
  apply Step_pure.vbinop_val _ _ _ _ _ (some [.mk_uN result.toNat])
  · rw [packed]
    exact integer_minmax_vector_relation ty kind x y
  · change 0 < 1
    decide
  · simp
  · simp
  · exact const_wf x
  · exact const_wf y
  · exact .admininstr_case_26 _ _ (shape_of_wf _) (integer_minmax_source_wf ty kind supported)
  · exact const_wf result

end Itasca.Spec.Simd

end

end

end
