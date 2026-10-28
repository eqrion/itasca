import Exec.Interp.Control.StructuredLinear
import Exec.Interp.Relations.LocalCodePoint
import Exec.Interp.Relations.Fetch
import Exec.Interp.Relations.Capacity

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

theorem move_valid_bounds (compiled : runtime.bytecode.CompiledFunction)
    (ty : valtype) (dst src : U32)
    (checked : runtime.bytecode.CompiledFunction.instruction_valid compiled (move ty dst src) = .ok true) :
    dst.val + width ty ≤ compiled.slot_count.val ∧ src.val + width ty ≤ compiled.slot_count.val := by
  cases ty <;> simp only [move, width, reduceIte] at checked ⊢
  all_goals first | exact copy_valid_bounds compiled dst src checked | exact copy2_valid_bounds compiled dst src checked

end Itasca.Runtime.Code

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

end Itasca.Runtime.Interp
