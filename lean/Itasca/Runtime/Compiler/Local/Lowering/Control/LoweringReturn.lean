import Itasca.Runtime.Compiler.Local.Lowering.Emission.Lowering
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredComposition
/-! Actual RETURN callback emission and terminal structured source certificate. -/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

@[step] theorem callback_return {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (body : runtime.compiler.Frame) (source : U32)
    (reachable : compiler.reachable = true)
    (bodyFrame : compiler.frames.val[0]? = some body)
    (height : compiler.height.val = source.val + body.results.val)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return ops compiler state ⦃ out =>
      out.1 = .Ok () → out.2.reachable = false ∧
        out.2.function.code.val = compiler.function.code.val ++ [.Return source body.results] ∧
        out.2.frames = compiler.frames ∧ compilerLocals out.2 = compilerLocals compiler ⦄ := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return
  rw [if_pos reachable]
  have bound : 0 < compiler.frames.length := List.getElem?_eq_some_iff.mp bodyFrame |>.1
  step as ⟨frame, hframe⟩
  have same : frame = body := hframe.trans (List.getElem?_eq_some_iff.mp bodyFrame).2
  rw [same]
  step as ⟨value, hvalue⟩
  cases value with
  | none => simp only at hvalue; omega
  | some word =>
    have valueEq : word = source := by apply UScalar.eq_of_val_eq; simp only at hvalue; omega
    rw [valueEq]
    simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with compiler_emit ops law compiler (.Return source body.results) codeFits sourceFits coordinateFits
      as ⟨result, emitted, emission⟩
    cases result with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok value =>
      cases value
      obtain ⟨budget, code, sources, exactState, codeAppended, sourceAppended⟩ := emission rfl
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step with compiler_observe ops law { emitted with reachable := false } state as ⟨out, observed, accepted⟩
      obtain ⟨hoff, hh, hl, hls, hlo, hr, hcode, hsources, hnext, hcap, hmono, hframes, hcontrols⟩ := observed accepted
      refine ⟨hr, ?_, ?_, ?_⟩
      · simpa [hcode, exactState] using codeAppended
      · simpa [exactState] using hframes
      · simp [compilerLocals, hl, exactState]

end Itasca.Runtime.Compiler
