import Itasca.Runtime.Compiler.Body.Callbacks.Prefix.CompilerPrefix
import Itasca.Runtime.Compiler.Body.Reader.Control.Boundary
import Itasca.Runtime.Compiler.Body.Reader.Control.ScopeFronts
import Itasca.Runtime.Compiler.Body.Reader.Control.ReachabilitySteps

/-!
Source-coordinate and body bounds retained by reader and compiler states.

Main declarations: `ReaderBoundaryWasm2.source_bound` and `CompilerStable.body_bound`. A direct consumer is `Compiler.Body.Reader.Control.ClosedInstructionPrefix`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem ReaderBoundaryWasm2.source_bound {data env locals index ft st parents current}
    (boundary : ReaderBoundaryWasm2 data env locals index ft st parents current) :
    data.length ≤ limits.MAX_MODULE_BYTES.val := by
  have bound := boundary.bounds.size
  have cap : limits.MAX_FUNCTION_BYTES.val ≤ limits.MAX_MODULE_BYTES.val := by
    norm_num [limits.MAX_FUNCTION_BYTES, limits.MAX_MODULE_BYTES]
  exact bound.trans cap

/-- All body callbacks retain the absolute source origin, so the initial
entry-span bound remains valid throughout the compiler fold. -/
theorem CompilerStable.body_bound {A : Type}
    {initial current : runtime.compiler.FunctionCompiler A}
    (stable : CompilerStable initial current) {length : Nat}
    (bound : initial.function.body_start.val + length ≤ Usize.max) :
    current.function.body_start.val + length ≤ Usize.max := by
  rw [stable.fields.2.2.2.2.2.2.2.1]
  exact bound
end Itasca.Runtime.Compiler
