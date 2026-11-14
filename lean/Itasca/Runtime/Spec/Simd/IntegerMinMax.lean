import Itasca.Runtime.Spec.Simd.ExtendLanes
import SpecExt.Builtins.Examples
import Itasca.Runtime.Spec.SegmentInitCases
import Itasca.Runtime.Spec.Simd.CompareInteger
import Itasca.Runtime.Spec.Simd.FloatResize
import Itasca.Runtime.Spec.FloatTrunc

/-!
Sections, each formerly its own module: AllTrue, Bitmask, Popcount, Unary, FloatBinary, Average, IntegerMinMax.
-/

/-! ## AllTrue -/

section

/-!
The source operation for all-true lane reduction.

Main declarations: `allTrueSource`. A direct consumer is `Interp.Simd.Integer.AllTrueSound`.
-/

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

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
end Itasca.Runtime.Spec.Simd

end

/-! ## Bitmask -/

section

/-!
SIMD lane bitmasks and their bit-level characterization, connecting source operations with the interpreter bit representation.
-/

/-! ## Simd Bitmask Bits -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

theorem integer_bits_reverse (width : Nat) (bits : BitVec width) :
    integerBits width bits.reverse.toNat = (integerBits width bits.toNat).reverse := by
  apply List.ext_getElem
  · simp [integerBits_length]
  · intro i left right
    have valid : i < width := by simpa only [integerBits_length] using left
    rw [integerBits_getMsb _ _ _ valid,List.getElem_reverse]
    simp only [integerBits_length]
    rw [integerBits_getMsb _ _ _ (by omega)]
    simp [BitVec.getMsbD_reverse,BitVec.getLsbD_reverse,BitVec.getMsbD_eq_getLsbD,valid]

theorem irev_reverse (width : Nat) (bits : BitVec width) :
    irev_ width (.mk_uN bits.reverse.toNat) = .mk_uN bits.toNat := by
  unfold irev_ ibits_ inv_ibits_
  simp only [proj_uN_0,integer_bits_reverse,List.reverse_reverse,integerBits_roundtrip bits.isLt]
end Itasca.Runtime.Spec.Simd

end

/-! ## Simd Bitmask -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

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
    · simp [ibits_,integerBits_length,outputs]; omega
    · intro i left right
      have valid : i<32 := by simpa only [ibits_,integerBits_length] using left
      simp only [ibits_,proj_uN_0]
      rw [integerBits_getMsb 32 result.reverse i valid,BitVec.getMsbD_reverse,mask i valid]
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
end Itasca.Runtime.Spec.Simd

end

end

/-! ## Popcount -/

section

/-!
Lane-word and source interpretations of population count.

Main declarations: `popcountWords` and `popcountSource`. A direct consumer is `Interp.Simd.Integer.PopcountSound`.
-/

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

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
end Itasca.Runtime.Spec.Simd

end

/-! ## Unary -/

section

/-!
Source-rule algebra for integer unary lane operations. Lane/list calculations establish the generated source operation and its reduction step, consumed by source-machine and interpreter correspondence proofs.
-/

/-! ## Simd Unary -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

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
end Itasca.Runtime.Spec.Simd

end

/-! ## Simd Unary Source -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

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
end Itasca.Runtime.Spec.Simd

end

end

/-! ## FloatBinary -/

section

/-!
Source-rule algebra for binary floating-point lanes. Lane/list calculations establish the generated source operation and its reduction step, consumed by source-machine and interpreter correspondence proofs.
-/

/-! ## Simd Float Binary -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins SpecExt.Builtins.Float

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

end Itasca.Runtime.Spec.Simd

end

/-! ## Simd Float Binary Source -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins SpecExt.Builtins.Float

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
    cases ty <;> exact floatOfBits_wf _ (by decide) _
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

end Itasca.Runtime.Spec.Simd

end

/-! ## Simd Float Binary Choices -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

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

end Itasca.Runtime.Spec.Simd

end

end

/-! ## Average -/

section

/-!
Rounded lane averages and their supported shapes.

Main declarations: `averageBits` and `averageSupported`. A direct consumer is `Interp.Simd.Integer.Average`.
-/

set_option maxHeartbeats 800000
namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

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

end Itasca.Runtime.Spec.Simd

end

/-! ## IntegerMinMax -/

section

/-!
Source-rule algebra for signed and unsigned integer minima and maxima. Lane/list calculations establish the generated source operation and its reduction step, consumed by source-machine and interpreter correspondence proofs.
-/

/-! ## Simd Integer Min Max -/

section

namespace Itasca.Runtime.Spec.Simd

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

end Itasca.Runtime.Spec.Simd

end

/-! ## Simd Integer Min Max Shape -/

section

namespace Itasca.Runtime.Spec.Simd

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

end Itasca.Runtime.Spec.Simd

end

/-! ## Simd Integer Min Max Lists -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

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

end Itasca.Runtime.Spec.Simd

end

/-! ## Simd Integer Min Max Source -/

section

namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

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

end Itasca.Runtime.Spec.Simd

end

/-! ## Simd Integer Min Max Step -/

section

namespace Itasca.Runtime.Spec.Simd

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

end Itasca.Runtime.Spec.Simd

end

end
