import Exec.Code.Body.Reader.Common.ReaderCompilerState
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- The validator's canonical body-size invariant supplies the weaker module
byte cap used by instruction-emission bounds. -/
theorem ReaderBoundaryWasm1.source_bound {data env ctx bt st parents current}
    (boundary : ReaderBoundaryWasm1 data env ctx bt st parents current) :
    data.length ≤ limits.MAX_MODULE_BYTES.val := by
  have bound := boundary.bounds.size
  have cap : limits.MAX_FUNCTION_BYTES.val ≤ limits.MAX_MODULE_BYTES.val := by
    norm_num [limits.MAX_FUNCTION_BYTES, limits.MAX_MODULE_BYTES]
  exact bound.trans cap

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
end Exec.Code
