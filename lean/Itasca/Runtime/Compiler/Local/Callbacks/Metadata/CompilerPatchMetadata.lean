import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerOrdinaryResults

/-!
Patching only replaces an instruction; all function and control metadata survive every normal return, including a rejected patch site.

Main declarations: `compiler_patch_ordinary_result` and `compiler_pc_ordinary_result`. A direct consumer is `Compiler.Local.Callbacks.Control.CompilerBranchMetadata`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- Patching only replaces an instruction; all function and control metadata
survive every normal return, including a rejected patch site. -/
theorem compiler_patch_ordinary_result {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (pc : Usize) (target : U32)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.control.FunctionCompiler.patch ops before pc target = .ok (status, after)) :
    CompilerOrdinaryStable before after := by
  rcases compiler_patch_cases ops before after pc target status accepted with rfl | ⟨_, _, rfl, _⟩ <;>
    exact ⟨rfl, Nat.le_refl _⟩

/-- PC calculation may reject its range but only updates the budget. -/
theorem compiler_pc_ordinary_result {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A)
    (status : core.result.Result U32 Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.pc ops before = .ok (status, after)) :
    CompilerOrdinaryStable before after := by
  have result := compiler_pc ops before
  rw [accepted, WP.spec_ok] at result
  obtain ⟨_, _, budget, same⟩ := result
  change after = {before with budget} at same
  subst after
  exact ⟨rfl, Nat.le_refl _⟩
end Itasca.Runtime.Compiler
