import Itasca.Runtime.Code.Local.Lowering.Common.NumericSafety
import Itasca.Runtime.Code.Local.Initializer.InitializerProofs
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

@[step] theorem compiler_pair_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (a b : U32) (fits : compiler.function.indirect.val.length < Usize.max) :
    runtime.compiler.FunctionCompiler.pair ops compiler a b ⦃ out =>
      ∃ budget pairs, out.2 = { compiler with budget := budget, function := { compiler.function with indirect := pairs } } ⦄ := by
  unfold runtime.compiler.FunctionCompiler.pair
  step with bounded_index (alloc.vec.Vec.len compiler.function.indirect) as ⟨indexResult, _⟩
  cases indexResult with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, WP.spec_ok]
    exact ⟨compiler.budget, compiler.function.indirect, rfl⟩
  | Ok index =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with budget_push ops law compiler.budget compiler.function.indirect (a,b) fits
      as ⟨answer, budget, pairs, effect⟩
    cases answer <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, WP.spec_ok]

end Itasca.Runtime.Code
