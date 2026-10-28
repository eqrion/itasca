import Itasca.Runtime.Code.Local.Lowering.Common.Lowering
import Itasca.Runtime.Code.Local.Control.Common.StructuredComposition
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

@[step] theorem callback_unreachable {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (reachable : compiler.reachable = true)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable ops compiler state ⦃ out =>
      out.1 = .Ok () → out.2.reachable = false ∧
        out.2.function.code.val = compiler.function.code.val ++ [.Unreachable] ∧
        out.2.frames = compiler.frames ∧ out.2.function.locals = compiler.function.locals ⦄ := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable
  rw [if_pos reachable]
  step with compiler_emit ops law compiler .Unreachable codeFits sourceFits coordinateFits
    as ⟨result, changed, emitted⟩
  cases result with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok value =>
    cases value
    obtain ⟨budget, code, sources, exactState, appended, sourceAppended⟩ := emitted rfl
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with compiler_observe ops law { changed with reachable := false } state
      as ⟨out, observed, accepted⟩
    obtain ⟨hoff, hh, hl, hls, hlo, hr, hcode, hsources, hnext, hcap, hmono, hframes, hcontrols⟩ := observed accepted
    refine ⟨hr, ?_, ?_, ?_⟩
    · simpa [exactState, hcode] using appended
    · simpa [exactState] using hframes
    · simpa [exactState] using hl

end Itasca.Runtime.Code
