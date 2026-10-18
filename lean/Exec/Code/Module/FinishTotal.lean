import Exec.Code.Module.WellFormedTotal
namespace Exec.Code
open Aeneas Aeneas.Std

/-- Finishing a compiler returns normally for arbitrary internal records and
validation results. Invalid frames or bytecode are rejected by the actual gate. -/
@[step] theorem compiler_finish_total {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A)
    (validated : core.result.Result Unit Itasca.error.Error) :
    runtime.compiler.FunctionCompiler.finish ops compiler validated ⦃ out => out.2 = compiler.budget ⦄ := by
  cases validated with
  | Err error => simp [runtime.compiler.FunctionCompiler.finish]
  | Ok value =>
    cases value
    simp only [runtime.compiler.FunctionCompiler.finish, alloc.vec.Vec.is_empty, bind_ok]
    split
    · step with well_formed_total compiler.function as ⟨checked⟩
      cases checked <;> simp
    · simp
end Exec.Code
