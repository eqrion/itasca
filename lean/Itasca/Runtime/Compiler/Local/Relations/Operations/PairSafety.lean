import Itasca.Runtime.Compiler.Local.Callbacks.Function.CloseFunction
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CompilerCodeMonotoneControl
import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.FixupBudget
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CallbackBounds
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlObservedLayout
import Itasca.Runtime.Compiler.Local.Relations.Select.SelectSafety
import Itasca.Runtime.Compiler.Local.Lowering.Integer.NumericSafety
import Itasca.Runtime.Compiler.Local.Initializer.InitializerElementAppend

/-!
Sections, each formerly its own module: EndSafety, TerminalSafety, PairSafety.
-/

/-! ## EndSafety -/

section

/-!
END safety needs only retained fixup/map addresses and vector headroom, not a source body typing or final compilation-success hypothesis.

Main declarations: `compiler_end_total`. A direct consumer is `Compiler.Body.Relations.Control.ReachedControlSafety`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- END safety needs only retained fixup/map addresses and vector headroom,
not a source body typing or final compilation-success hypothesis. -/
@[step] theorem compiler_end_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (frame : runtime.compiler.Frame)
    (rest : alloc.vec.Vec runtime.compiler.Frame) (kind : Itasca.code.LabelKind)
    (bt : Itasca.signature.BlockType)
    (frames : compiler.frames.val = rest.val ++ [frame])
    (sites : FrameSites compiler.function.code.val frame)
    (bodyGuard : frame.kind = .Body → frame.if_pc = none)
    (mapFits : frame.map.val < compiler.function.controls.val.length)
    (pcBound : compiler.function.code.val.length < 2^32)
    (coordinateFits : compiler.function.body_start.val + state.pos.val ≤ Usize.max)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (emitCoordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops compiler state kind bt ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  have total : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end
      ops compiler state .Block .Empty ⦃ _ => True ⦄ := by
    let target : U32 := UScalar.ofNatCore compiler.function.code.val.length pcBound
    by_cases body : frame.kind = .Body
    · exact WP.spec_mono (close_function_effect ops law compiler state frame rest target frames
        body (bodyGuard body) rfl sites.branches.branches mapFits coordinateFits codeFits sourceFits
        emitCoordinateFits) (by simp)
    · cases guardEq : frame.if_pc with
      | none =>
        exact WP.spec_mono (close_scope_effect ops law compiler state frame rest target frames body
          guardEq rfl sites.branches.branches mapFits coordinateFits) (by simp)
      | some guard =>
        obtain ⟨condition, old, found⟩ := sites.guard guard guardEq
        exact WP.spec_mono (close_guarded_scope_effect ops law compiler state frame rest target frames
          guard condition old body guardEq found rfl sites.branches.branches mapFits coordinateFits) (by simp)
  have same : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops compiler state kind bt =
      runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops compiler state .Block .Empty := rfl
  rw [same]
  obtain ⟨⟨status, after⟩, call, _⟩ := WP.spec_imp_exists total
  rw [call, WP.spec_ok]
  intro accepted
  change status = .Ok () at accepted
  subst status
  obtain ⟨middle, observed⟩ := compiler_end_observation ops compiler after state .Block .Empty call
  have result := compiler_observe_stack ops law middle state
  rw [observed, WP.spec_ok] at result
  exact result rfl

end Itasca.Runtime.Compiler

end

/-! ## TerminalSafety -/

section

/-!
Normal return of unreachable and return compiler callbacks.

Main declarations: `compiler_on_unreachable_total` and `compiler_on_return_total`. A direct consumer is `Compiler.Body.Reader.Control.ReturnSafety`.
-/

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end

/-! ## PairSafety -/

section

/-!
Normal return of index-pair insertion.

Main declarations: `compiler_pair_total`. A direct consumer is `Compiler.Local.Relations.Calls.CallSafety`.
-/

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end
