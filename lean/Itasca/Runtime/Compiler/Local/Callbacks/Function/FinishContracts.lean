import Itasca.Runtime.Compiler.Local.Relations.Instructions.WellFormedTotal
import Itasca.Support.Result

/-! Canonical finish contracts preserve validation and bytecode checker gates. -/
namespace Itasca.Runtime.Compiler
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
/-- Finishing a compiler returns normally for arbitrary internal records and
validation results. Invalid frames or bytecode are rejected by the actual gate. -/
theorem _root_.Itasca.runtime.compiler.FunctionCompiler.finish.total {A : Type} (ops : runtime.platform.Alloc A)
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

/-- Every normal finish preserves the budget; successful finishes retain the
validated function and its checked bytecode certificate. -/
theorem _root_.Itasca.runtime.compiler.FunctionCompiler.finish.inv {A : Type}
    (ops : runtime.platform.Alloc A) (compiler : runtime.compiler.FunctionCompiler A)
    (validated : core.result.Result Unit Itasca.error.Error)
    (status : core.result.Result runtime.bytecode.CompiledFunction Itasca.error.Error)
    (budget : runtime.compiler.Budget A)
    (called : runtime.compiler.FunctionCompiler.finish ops compiler validated = .ok (status, budget)) :
    budget = compiler.budget ∧ ∀ function, status = .Ok function →
      validated = .Ok () ∧ function = compiler.function ∧ compiler.frames.val = [] ∧
        runtime.bytecode.CompiledFunction.well_formed function = .ok true := by
  obtain ⟨out, run, same⟩ := WP.spec_imp_exists
    (runtime.compiler.FunctionCompiler.finish.total ops compiler validated)
  rw [called] at run
  rw [← Result.ok_injective run] at same
  refine ⟨same, ?_⟩
  intro function success
  subst status
  obtain ⟨valid, equal, _, closed, checked⟩ :=
    compiler_finish_accepted ops compiler validated function budget called
  exact ⟨valid, equal, closed, checked⟩

/-- Closed frames and a successful actual bytecode check suffice for publication. -/
theorem _root_.Itasca.runtime.compiler.FunctionCompiler.finish.available {A : Type}
    (ops : runtime.platform.Alloc A) (compiler : runtime.compiler.FunctionCompiler A)
    (closed : compiler.frames.val = [])
    (checked : runtime.bytecode.CompiledFunction.well_formed compiler.function = .ok true) :
    runtime.compiler.FunctionCompiler.finish ops compiler (.Ok ()) =
      .ok (.Ok compiler.function, compiler.budget) := by
  simp [runtime.compiler.FunctionCompiler.finish, alloc.vec.Vec.is_empty, closed, checked]

end Itasca.Runtime.Compiler
