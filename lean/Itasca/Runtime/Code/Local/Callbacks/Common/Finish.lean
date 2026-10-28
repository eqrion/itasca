import Itasca.Runtime.Code.Local.Relations.Common.Function
import Itasca.Support.Result
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca.ResultFacts

/-- A successful actual finish retains the compiler's function and witnesses
that its final bytecode check returned true. No checker totality is assumed. -/
theorem compiler_finish_accepted {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A)
    (validated : core.result.Result Unit Itasca.error.Error)
    (function : runtime.bytecode.CompiledFunction) (budget : runtime.compiler.Budget A)
    (accepted : runtime.compiler.FunctionCompiler.finish ops compiler validated = .ok (.Ok function, budget)) :
    validated = .Ok () ∧ function = compiler.function ∧ budget = compiler.budget ∧
      compiler.frames.val = [] ∧ runtime.bytecode.CompiledFunction.well_formed function = .ok true := by
  cases validated with
  | Err error => simp [runtime.compiler.FunctionCompiler.finish] at accepted
  | Ok value =>
    cases value
    simp only [runtime.compiler.FunctionCompiler.finish, alloc.vec.Vec.is_empty, bind_ok] at accepted
    split at accepted
    · rename_i empty
      obtain ⟨checked, check, accepted⟩ := bind_ok_inv _ _ _ accepted
      cases checked <;> simp_all
    · simp at accepted
end Itasca.Runtime.Code
