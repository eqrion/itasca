import Exec.Code.Module.CompileTotalDriver
namespace Exec.Code
open Aeneas Aeneas.Std Itasca
open runtime.compiler

@[step] theorem compiler_default_limits_total :
    CompileLimits.Insts.CoreDefaultDefault.default ⦃ _ => True ⦄ := by
  unfold CompileLimits.Insts.CoreDefaultDefault.default
  step
  step

theorem compile_default_total_of_entries {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bytes : Slice U8) (profile : ValidationProfile)
    (entries : ReachedEntriesTotal ops profile) :
    runtime.compiler.compile_default_with ops bytes profile ⦃ _ => True ⦄ := by
  unfold runtime.compiler.compile_default_with
  step with compiler_default_limits_total as ⟨limits⟩
  step with compile_with_total_of_entries ops law bytes profile limits entries as ⟨result⟩
  cases result with
  | Ok executable => simp
  | Err error => cases error <;> simp
end Exec.Code
