import Exec.Interp.Numeric.Integer.IntegerDispatch
import Exec.Interp.Relations.Fetch

namespace Exec.Interp
open Aeneas Aeneas.Std Abs.Numeric
variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

 theorem dispatch_integer_eq (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (index inst function base : Usize)
    (op : Instruction) (dst left right : U32) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform index inst function base
      (Code.integerInstruction op dst left right) = (do
        let (r, next) ← runtime.interp.execute_scalar floats exec base
          (Code.integerOpcode op) dst left right
        Result.ok (r, next, store, platform)) := by
  cases op with
  | binary ty binop => cases ty <;> cases binop <;> (try casesm* sx) <;>
    simp [Code.integerInstruction, Code.integerOpcode, runtime.interp.dispatch,
      runtime.interp.dispatch_scalar, runtime.interp.scalar_operands, bind_ok]
  | unary ty unop => cases unop <;> (try cases ty) <;>
    simp [Code.integerInstruction, Code.integerOpcode, runtime.interp.dispatch,
      runtime.interp.dispatch_scalar, runtime.interp.scalar_operands, bind_ok]
  | compare ty relop => cases ty <;> cases relop <;> (try casesm* sx) <;>
    simp [Code.integerInstruction, Code.integerOpcode, runtime.interp.dispatch,
      runtime.interp.dispatch_scalar, runtime.interp.scalar_operands, bind_ok]
  | eqz ty => cases ty <;>
    simp [Code.integerInstruction, Code.integerOpcode, runtime.interp.dispatch,
      runtime.interp.dispatch_scalar, runtime.interp.scalar_operands, bind_ok]
  | conversion conv => cases conv <;>
    simp [Code.integerInstruction, Code.integerOpcode, runtime.interp.dispatch,
      runtime.interp.dispatch_scalar, runtime.interp.scalar_operands, bind_ok]

end Exec.Interp
