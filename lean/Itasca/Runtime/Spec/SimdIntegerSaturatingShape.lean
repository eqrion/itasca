import Itasca.Runtime.Spec.SimdIntegerSaturating
namespace Itasca.Runtime.Spec.Simd

def integerSaturatingSupported (ty : Jnn) (_kind : IntegerSaturating) : Prop :=
  match ty with | .I8 | .I16 => True | _ => False

def integerSaturatingOp (kind : IntegerSaturating) : vbinop_Jnn_N :=
  match kind with | .addS => .ADD_SAT .S | .addU => .ADD_SAT .U | .subS => .SUB_SAT .S | .subU => .SUB_SAT .U

def integerSaturatingSource (ty : Jnn) (kind : IntegerSaturating) : vbinop_ :=
  .mk_vbinop__0 ty (128/lsize (lanetype_Jnn ty)) (integerSaturatingOp kind)

theorem integer_saturating_source_wf (ty : Jnn) (kind : IntegerSaturating)
    (supported : integerSaturatingSupported ty kind) :
    wf_vbinop_ (shapeOf (lanetype_Jnn ty)) (integerSaturatingSource ty kind) := by
  cases ty <;> cases kind <;> simp only [integerSaturatingSupported] at supported
  all_goals try contradiction
  all_goals constructor <;> constructor
  all_goals decide

end Itasca.Runtime.Spec.Simd
