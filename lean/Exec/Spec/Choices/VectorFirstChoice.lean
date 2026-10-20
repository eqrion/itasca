import Exec.Spec.Choices.VectorChoices
import Exec.Spec.Choices.VectorDeterminism
import Exec.Spec.SimdFloatResizeSource
import Exec.Spec.SimdConvertInteger
import Exec.Spec.SimdTruncSat
import Exec.Spec.SimdWidenLists
namespace Exec.Spec

/-- Format-resizing preferences use the first independent Cartesian product
of source lane replies, including the required zero padding. -/
def vectorConversionFirst (op : vcvtop__) (input : vec_) : Option (Option vec_) :=
  let word := BitVec.ofNat 128 (proj_uN_0 input)
  let signed (sign : sx) := match sign with | .S => true | .U => false
  let high (part : half) := match part with | .HIGH => true | .LOW => false
  let first (kind : Simd.FloatResize) :=
    some ((Simd.floatResizeProducts kind (BitVec.ofNat 128 (proj_uN_0 input))).head?.map
      (inv_lanes_ (Simd.shapeOf (lanetype_Fnn kind.output))))
  match op with
  | .mk_vcvtop___3 .F64 2 .F32 4 (.DEMOTE .ZERO) => first .demote
  | .mk_vcvtop___3 .F32 4 .F64 2 .PROMOTELOW => first .promote
  | .mk_vcvtop___1 .I32 4 .F32 4 (.CONVERT none sign) => some (some (Simd.convertIntegerResult .F32 sign word))
  | .mk_vcvtop___1 .I32 4 .F64 2 (.CONVERT (some .LOW) sign) => some (some (Simd.convertIntegerResult .F64 sign word))
  | .mk_vcvtop___2 .F32 4 .I32 4 (.TRUNC_SAT sign none) => some (some (Simd.truncSatResult .F32 sign word))
  | .mk_vcvtop___2 .F64 2 .I32 4 (.TRUNC_SAT sign (some .ZERO)) => some (some (Simd.truncSatResult .F64 sign word))
  | .mk_vcvtop___0 .I8 16 .I16 8 (.EXTEND part sign) => some (some (Simd.widenResult .i8 false (high part) (signed sign) word word))
  | .mk_vcvtop___0 .I16 8 .I32 4 (.EXTEND part sign) => some (some (Simd.widenResult .i16 false (high part) (signed sign) word word))
  | .mk_vcvtop___0 .I32 4 .I64 2 (.EXTEND part sign) => some (some (Simd.widenResult .i32 false (high part) (signed sign) word word))
  | _ => none

/-- Preferred SIMD replies use the first element of the generated result
list. Format-resizing conversions use the first source lane product. -/
def FirstVectorReply (request : VectorRequest) (reply : Option vec_) : Prop :=
  match request with
  | .unary shape op input => ∃ results, fun_vunop_ shape op input (some results) ∧ results.head? = reply
  | .binary shape op left right => ∃ results, fun_vbinop_ shape op left right (some results) ∧ results.head? = reply
  | .convert _ _ op input => vectorConversionFirst op input = some reply

theorem first_vector_reply_unique {request : VectorRequest} {left right : Option vec_}
    (first : FirstVectorReply request left) (second : FirstVectorReply request right) : left = right := by
  cases request with
  | unary shape op input =>
    obtain ⟨xs,source,leftEq⟩ := first
    obtain ⟨ys,other,rightEq⟩ := second
    have same := vector_unop_results_unique source other
    exact leftEq.symm.trans (same ▸ rightEq)
  | binary shape op left right =>
    obtain ⟨xs,source,leftEq⟩ := first
    obtain ⟨ys,other,rightEq⟩ := second
    have same := vector_binop_results_unique source other
    exact leftEq.symm.trans (same ▸ rightEq)
  | convert => exact Option.some.inj (first.symm.trans second)

/-- A source-only preference, selected only among independently permitted
replies. No interpreter or platform operation occurs in this definition. -/
noncomputable def firstVectorChoice : VectorChoices := by
  classical
  exact fun occurrence request =>
    if preferred : ∃ reply, VectorResultAllowed request reply ∧ FirstVectorReply request reply then
      Classical.choose preferred
    else sourceVectorChoice occurrence request

theorem firstVectorChoice_admissible : firstVectorChoice.Admissible := by
  intro occurrence request possible
  classical
  unfold VectorChoices.AdmissibleAt firstVectorChoice
  split
  · rename_i preferred
    exact (Classical.choose_spec preferred).1
  · exact sourceVectorChoice_admissible occurrence request possible

theorem chosen_vector_from_first (occurrence : Nat) {request : VectorRequest} {reply : Option vec_}
    (allowed : VectorResultAllowed request reply) (first : FirstVectorReply request reply) :
    ChosenVector firstVectorChoice occurrence request reply := by
  classical
  have possible : ∃ reply, VectorResultAllowed request reply ∧ FirstVectorReply request reply := ⟨reply,allowed,first⟩
  have same : firstVectorChoice occurrence request = reply := by
    simp only [firstVectorChoice,dif_pos possible]
    exact first_vector_reply_unique (Classical.choose_spec possible).2 first
  rw [← same]
  exact .selected (firstVectorChoice_admissible occurrence request ⟨reply,allowed⟩)
end Exec.Spec
