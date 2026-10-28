import Exec.Abs.Numeric.Unary

namespace Itasca.Runtime.Abs.Numeric

theorem UnaryOperator.opcode_bound {ty : Inn} (op : UnaryOperator ty) : op.opcode < 65536 := by
  cases ty <;> cases op <;> decide

end Itasca.Runtime.Abs.Numeric
