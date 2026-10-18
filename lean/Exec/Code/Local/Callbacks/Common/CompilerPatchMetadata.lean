import Exec.Code.Local.Callbacks.Common.CompilerOrdinaryResults
namespace Exec.Code
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

private theorem code_update_ordinary {A : Type} (before after : runtime.compiler.FunctionCompiler A)
    (code : alloc.vec.Vec runtime.bytecode.Instr)
    (result status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : Result.ok (result, {before with function := {before.function with code}}) =
      Result.ok (status, after)) : CompilerOrdinaryStable before after := by
  have same := (Prod.mk.inj (Result.ok.injEq.mp accepted)).2
  subst after
  exact ⟨rfl, Nat.le_refl _⟩

/-- Patching only replaces an instruction; all function and control metadata
survive every normal return, including a rejected patch site. -/
theorem compiler_patch_ordinary_result {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (pc : Usize) (target : U32)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.control.FunctionCompiler.patch ops before pc target = .ok (status, after)) :
    CompilerOrdinaryStable before after := by
  unfold runtime.compiler.control.FunctionCompiler.patch at accepted
  obtain ⟨⟨instruction, restore⟩, _, rest⟩ := bind_ok_inv _ _ _ accepted
  cases instruction <;> exact code_update_ordinary before after _ _ status rest

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
end Exec.Code
