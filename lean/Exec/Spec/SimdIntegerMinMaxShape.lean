import Exec.Spec.SimdIntegerMinMax
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
