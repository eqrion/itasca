import Itasca.Runtime.Compiler.Local.Relations.Select.SelectSafety

/-!
Normal return of unreachable and return compiler callbacks.

Main declarations: `compiler_on_unreachable_total` and `compiler_on_return_total`. A direct consumer is `Compiler.Body.Reader.Control.ReturnSafety`.
-/

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

@[step] theorem compiler_on_unreachable_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_unreachable compiler state ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  change runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable ops compiler state ⦃ _ ⦄
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable
  by_cases live : compiler.reachable = true
  · rw [if_pos live]
    step with compiler_emit ops law compiler .Unreachable codeFits sourceFits coordinateFits
      as ⟨answer,emitted,_⟩
    cases answer with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok value =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
      exact compiler_observe_stack ops law _ state
  · rw [if_neg live]
    exact compiler_observe_stack ops law compiler state

@[step] theorem compiler_on_return_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (bodyFrame : compiler.reachable = true → 0 < compiler.frames.val.length)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_return compiler state ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  change runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return ops compiler state ⦃ _ ⦄
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return
  by_cases live : compiler.reachable = true
  · rw [if_pos live]
    have bound : 0 < compiler.frames.length := bodyFrame live
    step as ⟨frame, found⟩
    step as ⟨difference, value⟩
    cases difference with
    | none => simp [core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | some source =>
      simp only [core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
      step with compiler_emit ops law compiler (.Return source frame.results) codeFits sourceFits coordinateFits
        as ⟨answer,emitted,_⟩
      cases answer with
      | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok value =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
        exact compiler_observe_stack ops law _ state
  · rw [if_neg live]
    exact compiler_observe_stack ops law compiler state

end Itasca.Runtime.Code
