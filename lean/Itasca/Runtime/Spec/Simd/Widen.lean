import Itasca.Runtime.Spec.Simd.Shift
import Itasca.Runtime.Spec.Simd.IntegerArithmetic

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
  · simp only [extendBits,Bool.true_eq,↓reduceIte,extend__,proj_uN_0,Itasca.Runtime.Spec.signedValue_bitvec]
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
  · exact .ishape_case_0 _ _ (shapeOf_wf _) rfl
  · exact .ishape_case_0 _ _ (shapeOf_wf _) rfl
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
    · exact shapeOf_wf _
    · exact shapeOf_wf _
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
    · exact shapeOf_wf _
    · exact shapeOf_wf _
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
    · exact shapeOf_wf _
    · exact shapeOf_wf _
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
