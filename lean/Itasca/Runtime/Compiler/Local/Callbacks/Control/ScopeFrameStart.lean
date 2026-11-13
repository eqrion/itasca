import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.FixupPreservation
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CloseScope
import Itasca.Runtime.Compiler.Local.Relations.Function.FunctionEntry
import Itasca.Runtime.Compiler.Local.Source.SourceControlBudget

/-!
Sections, each formerly its own module: FixupBranchPreservation, FixupElsePreservation, ScopeFrameStart.
-/

/-! ## FixupBranchPreservation -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

private theorem emit_paid {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (instruction : runtime.bytecode.Instr) (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.emit ops before instruction = .ok (status,after)) :
    status = .Ok () → after.function.code.val.length = before.function.code.val.length + 1 := by
  intro same; subst status
  simp [compiler_emit_code_success ops law before after instruction accepted]

open Lean Meta Elab Tactic in
elab "paid_fixup_effect " h:ident " using " ops:term ", " law:term : tactic => withMainContext do
  evalTactic (← `(tactic| fixup_effect $h using $ops, $law))
  let hyp ← elabTerm h none
  let ty ← inferType hyp
  let some (_, lhs, _) := ty.eq? | return
  if lhs.getAppFn.constName? == some ``runtime.compiler.FunctionCompiler.emit then
    evalTactic (← `(tactic| have paid := emit_paid $ops $law _ _ _ _ $h))

macro "paid_fixup_step " h:ident " using " ops:term ", " law:term : tactic => `(tactic|
  first
  | solve | (sources_terminal $h; fixup_close)
  | (fail_if_no_progress dsimp only at $h:ident)
  | (fail_if_no_progress simp only [Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, bind_ok, bind_tc_ok] at $h:ident)
  | (sources_nonterminal $h
     obtain ⟨value, called, rest⟩ := bind_ok_inv _ _ _ $h
     clear $h
     rename' rest => $h
     first
     | (guard_hyp value : Prod _ _; rcases value with ⟨firstValue, secondValue⟩)
     | skip
     try paid_fixup_effect called using $ops, $law
     first
     | (guard_hyp firstValue : core.result.Result _ _; cases firstValue)
     | (guard_hyp value : core.result.Result _ _; cases value)
     | skip
     try simp only [uncurry_apply_pair] at $h:ident)
  | sources_split $h)

theorem compiler_branch_fixup_budget {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (depth skip : U32) (conditional : Bool)
    (budget : FixupBudget before.frames.val before.function.code.val.length)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops before depth skip conditional = .ok (.Ok (), after)) :
    FixupBudget after.frames.val after.function.code.val.length := by
  have growth := compiler_branch_code_mono ops law before after depth skip conditional (.Ok ()) accepted
  cases conditional <;>
    simp only [runtime.compiler.control.FunctionCompiler.branch, Bool.false_eq_true, ite_false, ite_true] at accepted
  all_goals repeat' paid_fixup_step accepted using ops, law
  all_goals try paid_fixup_effect accepted using ops, law
  all_goals fixup_close
  all_goals try exact budget.mono (by omega)
  all_goals
    apply (budget.mono (by omega)).set
    have selectedBudget := budget _ (by assumption)
    dsimp only
    try simp_all only [List.length_append, List.length_singleton]
    omega


end Itasca.Runtime.Compiler

end

/-! ## FixupElsePreservation -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

/-- ELSE either keeps the current fixup vector or appends one site while
emitting its corresponding skip jump. -/
theorem compiler_else_fixup_budget {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (budget : FixupBudget before.frames.val before.function.code.val.length)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else
      ops before state bt = .ok (.Ok (), after)) :
    FixupBudget after.frames.val after.function.code.val.length := by
  have growth := compiler_else_code_mono ops law before after state bt accepted
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else at accepted
  simp only [core.option.Option.take] at accepted
  repeat' paid_fixup_step accepted using ops, law
  all_goals try paid_fixup_effect accepted using ops, law
  all_goals fixup_close
  all_goals try exact budget.mono (by omega)
  all_goals
    apply (budget.mono (by omega)).set
    have selectedBudget := budget _ (by assumption)
    dsimp only
    try simp_all only [List.length_append, List.length_singleton]
    omega


end Itasca.Runtime.Compiler

end

/-! ## ScopeFrameStart -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Actual compiler construction and function-start establish the root physical
frame, empty universally planned prefix, and initial source byte budget. -/
theorem compiler_function_start_scope {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (signatures : Slice runtime.compiler.Signature)
    (functionSlots : Slice U32) (budget : runtime.compiler.Budget A) (batchStart : Usize)
    (initial started : runtime.compiler.FunctionCompiler A)
    (ctx : Itasca.code.Context) (typeIndex : U32) (signature : runtime.compiler.Signature)
    (bodyBegin bodyEnd : Usize) (types functions : List functype) (returns : List valtype)
    (lookup : signatures.val[typeIndex.val]? = some signature)
    (resultWidth : signature.result_slots.val = slots returns)
    (beginFits : batchStart.val + bodyBegin.val ≤ Usize.max)
    (endFits : batchStart.val + bodyEnd.val ≤ Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart = .ok initial)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start
      ops initial ctx typeIndex bodyBegin bodyEnd = .ok (.Ok (), started)) :
    ∃ frame, started.frames.val = [frame] ∧
      FrameScope (ctx.locals.val.map Itasca.Translate.valueType) started (SourceScope.initial returns) frame ∧
      UniversalPrefix started types functions returns (ctx.locals.val.map Itasca.Translate.valueType)
        [] (SourceScope.initial returns) [] ∧
      UniversalElse started types functions returns (ctx.locals.val.map Itasca.Translate.valueType)
        [] (SourceScope.initial returns) ∧
      SourceCodeBudget started 0 ∧ SourceControlBudget started 0 ∧
      ScopeFrameStack (ctx.locals.val.map Itasca.Translate.valueType) started [] (SourceScope.initial returns) ∧
      started.reachable = true := by
  have newPost := compiler_new ops signatures functionSlots budget batchStart
  rw [created, WP.spec_ok] at newPost
  obtain ⟨localLayout, emptyLocals, emptyOperands, emptyMaps, emptyFrames, emptyCode,
    reachable, sigs, functionWidths, coordinate⟩ := newPost
  have startPost := compiler_function_start ops law initial ctx typeIndex signature bodyBegin bodyEnd
    (by simpa only [sigs] using lookup) (by simpa only [coordinate] using beginFits)
    (by simpa only [coordinate] using endFits) emptyLocals localLayout emptyOperands
    (by simp [emptyMaps]; scalar_tac) (by simp [emptyFrames]; scalar_tac)
  rw [accepted, WP.spec_ok] at startPost
  obtain ⟨layout, live, capacity, localTypes, params, typeIdx, start, finish, codeEq, framesEq, mapsEq⟩ := startPost rfl
  let frame : runtime.compiler.Frame :=
    ⟨0#usize, .Body, started.function.local_slots, 0#u32, signature.result_slots,
      0#u32, none, true, false, alloc.vec.Vec.new Usize⟩
  have frameEq : started.frames.val = [frame] := by simpa [emptyFrames, frame] using framesEq
  have localEq : compilerLocals started = ctx.locals.val.map Itasca.Translate.valueType := by
    simp only [compilerLocals, localTypes]
  have codeEmpty : started.function.code.val = [] := by rw [codeEq, emptyCode]
  have mapPresent : 0 < started.function.controls.val.length := by simp [mapsEq]
  have frameShape : FrameScope (ctx.locals.val.map Itasca.Translate.valueType) started
      (SourceScope.initial returns) frame :=
    FrameScope.initial _ _ started _ _ (by simpa only [localEq] using layout.localSlots)
      resultWidth mapPresent
  refine ⟨frame, frameEq, frameShape, ?_, UniversalElse.initial _ _ _ _ _,
    SourceCodeBudget.initial codeEmpty, ?_, .initial frame frameEq frameShape, live.trans reachable⟩
  · exact UniversalPrefix.initial started types functions returns _ frame codeEmpty frameEq rfl
      (by simp [frame, alloc.vec.Vec.new]) localEq layout
  · exact SourceControlBudget.initial (by simp [mapsEq, emptyMaps]) (by simp [frameEq])
end Itasca.Runtime.Compiler

end
