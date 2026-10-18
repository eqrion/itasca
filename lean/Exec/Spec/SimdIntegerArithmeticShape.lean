import Exec.Spec.SimdIntegerArithmetic
namespace Exec.Spec.Simd

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

end Exec.Spec.Simd
