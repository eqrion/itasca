import Itasca.Runtime.Compiler.Local.Relations.Control.BranchCertificates
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerAuxiliaryTables
import Itasca.Runtime.Compiler.Local.Source.SourceLengthsTactic
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerTerminalMetadata
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CompilerCodeMonotoneControl
import Itasca.Runtime.Compiler.Local.Relations.Function.FunctionEnvironment
import Itasca.Runtime.Compiler.Local.Callbacks.Control.EnterIf
import Itasca.Runtime.Compiler.Local.Callbacks.Function.EnterDead
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CloseScope
import Itasca.Runtime.Compiler.Local.Capacity.ControlCapacity

/-!
Sections, each formerly its own module: CallbackCursor, CallbackSources, CompilerCallbackMetadata, ScopeCallbackEnter, ScopeCallbackDead, ScopeCallbackIf, CallbackGrowth, CallbackCapacity, CompilerCodeMonotoneCallbacks.
-/

/-! ## CallbackCursor -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem compiler_branch_cursor_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (depth skip : U32) (conditional : Bool) (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops before depth skip conditional = .ok (status, after)) :
    status = .Ok () → after.next_source = before.next_source := by
  intro success
  subst status
  exact compiler_branch_cursor ops law before after depth skip conditional accepted

open Lean Meta Elab Tactic in
elab "control_cursor_effect " h:ident " using " ops:term ", " law:term : tactic => withMainContext do
  let hyp ← elabTerm h none
  let ty ← inferType hyp
  let some (_, lhs, _) := ty.eq? | throwError "not an equation"
  if lhs.getAppFn.constName? = some ``runtime.compiler.control.FunctionCompiler.branch then
    evalTactic (← `(tactic| have effect := compiler_branch_cursor_result $ops $law _ _ _ _ _ _ $h))
  else
    evalTactic (← `(tactic| cursor_effect $h using $ops, $law))
macro "control_cursor_step " h:ident " using " ops:term ", " law:term : tactic => `(tactic|
  first
  | solve | (sources_terminal $h; cursor_close)
  | (fail_if_no_progress dsimp only at $h:ident)
  | solve | (control_cursor_effect $h using $ops, $law; cursor_close)
  | solve | (sources_terminal $h; have output := (Prod.mk.inj (Result.ok.injEq.mp $h)).2; cases output; cursor_close)
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
     try control_cursor_effect called using $ops, $law
     first
     | (guard_hyp firstValue : core.result.Result _ _; cases firstValue)
     | (guard_hyp value : core.result.Result _ _; cases value)
     | skip
     try simp only [uncurry_apply_pair] at $h:ident)
  | (fail_if_no_progress simp only [Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, bind_ok, bind_tc_ok] at $h:ident)
  | sources_split $h)

theorem compiler_unreachable_cursor {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable
      ops before state = .ok (.Ok (), after)) :
    after.next_source = state.pos := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable at accepted
  repeat' control_cursor_step accepted using ops, law

theorem compiler_return_cursor {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return
      ops before state = .ok (.Ok (), after)) :
    after.next_source = state.pos := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return at accepted
  repeat' control_cursor_step accepted using ops, law

theorem compiler_br_cursor {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (depth : U32) (types : Itasca.signature.ResultType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br
      ops before state depth types = .ok (.Ok (), after)) :
    after.next_source = state.pos := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br at accepted
  repeat' control_cursor_step accepted using ops, law

theorem compiler_br_if_cursor {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (depth : U32) (types : Itasca.signature.ResultType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if
      ops before state depth types = .ok (.Ok (), after)) :
    after.next_source = state.pos := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if at accepted
  repeat' control_cursor_step accepted using ops, law

end Itasca.Runtime.Compiler

end

/-! ## CallbackSources -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem compiler_branch_sources_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (depth skip : U32) (conditional : Bool) (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops before depth skip conditional = .ok (status, after)) :
    status = .Ok () → SourceProgress before after := by
  intro success
  subst status
  exact compiler_branch_sources ops law before after depth skip conditional accepted

open Lean Meta Elab Tactic in
elab "control_sources_effect " h:ident " using " ops:term ", " law:term : tactic => withMainContext do
  let hyp ← elabTerm h none
  let ty ← inferType hyp
  let some (_, lhs, _) := ty.eq? | throwError "not an equation"
  if lhs.getAppFn.constName? = some ``runtime.compiler.control.FunctionCompiler.branch then
    evalTactic (← `(tactic| have effect := compiler_branch_sources_result $ops $law _ _ _ _ _ _ $h))
  else
    evalTactic (← `(tactic| sources_effect $h using $ops, $law))
macro "control_sources_step " h:ident " using " ops:term ", " law:term : tactic => `(tactic|
  first
  | solve | (sources_terminal $h; sources_close)
  | (fail_if_no_progress dsimp only at $h:ident)
  | solve | (control_sources_effect $h using $ops, $law; sources_close)
  | solve | (sources_terminal $h; have output := (Prod.mk.inj (Result.ok.injEq.mp $h)).2; cases output; sources_close)
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
     try control_sources_effect called using $ops, $law
     try clear called
     first
     | (guard_hyp firstValue : core.result.Result _ _; cases firstValue)
     | (guard_hyp value : core.result.Result _ _; cases value)
     | skip
     try simp only [uncurry_apply_pair] at $h:ident)
  | (fail_if_no_progress simp only [Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, bind_ok, bind_tc_ok] at $h:ident)
  | sources_split $h)

theorem compiler_unreachable_sources {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable
      ops before state = .ok (.Ok (), after)) :
    SourceProgress before after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable at accepted
  repeat' control_sources_step accepted using ops, law

theorem compiler_return_sources {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return
      ops before state = .ok (.Ok (), after)) :
    SourceProgress before after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return at accepted
  repeat' control_sources_step accepted using ops, law

theorem compiler_br_sources {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (depth : U32) (types : Itasca.signature.ResultType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br
      ops before state depth types = .ok (.Ok (), after)) :
    SourceProgress before after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br at accepted
  repeat' control_sources_step accepted using ops, law

theorem compiler_br_if_sources {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (depth : U32) (types : Itasca.signature.ResultType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if
      ops before state depth types = .ok (.Ok (), after)) :
    SourceProgress before after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if at accepted
  repeat' control_sources_step accepted using ops, law

end Itasca.Runtime.Compiler

end

/-! ## CompilerCallbackMetadata -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
open Lean Meta Elab Tactic in
elab "metadata_control_effect " h:ident " using " ops:term ", " law:term : tactic => withMainContext do
  let hyp ← elabTerm h none
  let ty ← inferType hyp
  let some (_, lhs, _) := ty.eq? | throwError "not an equation"
  if lhs.getAppFn.constName? = some ``runtime.compiler.control.FunctionCompiler.branch then
    evalTactic (← `(tactic| have effect := compiler_branch_stable_result $ops $law _ _ _ _ _ _ $h))
    evalTactic (← `(tactic| have metadataEq := effect.metadata))
    evalTactic (← `(tactic| have capacity := effect.capacity))
  else
    evalTactic (← `(tactic| metadata_effect $h using $ops, $law))

macro "metadata_control_step " h:ident " using " ops:term ", " law:term : tactic => `(tactic|
  first
  | solve | (metadata_control_effect $h using $ops, $law; metadata_close)
  | solve | (simp only [Result.ok.injEq, Prod.mk.injEq] at $h:ident; obtain ⟨_, output⟩ := $h; cases output; metadata_close)
  | (obtain ⟨value, called, rest⟩ := bind_ok_inv _ _ _ $h
     clear $h
     rename' rest => $h
     first
     | (guard_hyp value : Prod _ _; rcases value with ⟨firstValue, secondValue⟩)
     | skip
     try metadata_control_effect called using $ops, $law
     try simp only [uncurry_apply_pair] at $h:ident)
  | (fail_if_no_progress simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, bind_ok, bind_tc_ok] at $h:ident)
  | split at $h:ident)

theorem compiler_unreachable_stable_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable
      ops before state = .ok (status, after)) :
    CompilerStable before after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable at accepted
  repeat' metadata_control_step accepted using ops, law

theorem compiler_return_stable_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return
      ops before state = .ok (status, after)) :
    CompilerStable before after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return at accepted
  repeat' metadata_control_step accepted using ops, law

theorem compiler_br_stable_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (depth : U32) (types : Itasca.signature.ResultType)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br
      ops before state depth types = .ok (status, after)) :
    CompilerStable before after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br at accepted
  repeat' metadata_control_step accepted using ops, law

theorem compiler_br_if_stable_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (depth : U32) (types : Itasca.signature.ResultType)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if
      ops before state depth types = .ok (status, after)) :
    CompilerStable before after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if at accepted
  repeat' metadata_control_step accepted using ops, law

end Itasca.Runtime.Compiler

end

/-! ## ScopeCallbackEnter -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- A successful actual BLOCK callback creates its source-aligned frame
and preserves every retained outer frame's physical entry evidence. -/
theorem callback_block_scope {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (ctrl : Itasca.code.Ctrl) (prior : List Itasca.code.Ctrl)
    (bt : Itasca.signature.BlockType) (signature : runtime.compiler.Signature) (pc : U32)
    (locals front params results : List valtype) (parents : List SourceScope)
    (current : SourceScope) (parentFrame : runtime.compiler.Frame)
    (nested : ScopeNesting parents current) (parentShape : FrameScope locals compiler current parentFrame)
    (localWidth : compiler.function.local_slots.val = slots locals)
    (frontWidth : stackWords (state.vals.val.take ctrl.value_stack_base.val) = slots front)
    (paramsWidth : signature.param_slots.val = slots params)
    (resultsWidth : signature.result_slots.val = slots results)
    (controls : state.ctrls.val = prior ++ [ctrl])
    (selected : SignatureAt compiler.signatures bt signature)
    (valuesFit : ctrl.value_stack_base.val ≤ state.vals.val.length)
    (heightFits : compiler.function.local_slots.val +
      stackWords (state.vals.val.take ctrl.value_stack_base.val) ≤ U32.max)
    (sourceFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max)
    (position : pc.val = compiler.function.code.val.length)
    (mapsFit : compiler.function.controls.val.length < Usize.max)
    (framesFit : compiler.frames.val.length < Usize.max)
    (reachable : compiler.reachable = true)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_block ops compiler state bt =
      .ok (.Ok (), after)) :
    after.function.code = compiler.function.code ∧ after.reachable = true ∧
      ∃ height source,
        source.val = compiler.function.body_start.val + compiler.next_source.val ∧
        after.frames.val = compiler.frames.val ++
          [⟨alloc.vec.Vec.len compiler.function.controls, .Block, height, signature.param_slots,
            signature.result_slots, pc, none, true, false, alloc.vec.Vec.new Usize⟩] ∧
        after.function.controls.val = compiler.function.controls.val ++
          [⟨.Block, source, 0#usize, UScalar.cast .Usize pc, 0#usize,
            ctrl.value_stack_base, signature.params, signature.results⟩] ∧
        FrameScope locals after
          (SourceScope.enterBlock (Itasca.Wasm2.blockType bt) front params results compiler.function.code.val.length true)
          ⟨alloc.vec.Vec.len compiler.function.controls, .Block, height, signature.param_slots,
            signature.result_slots, pc, none, true, false, alloc.vec.Vec.new Usize⟩ ∧
        ScopeNesting (parents ++ [current])
          (SourceScope.enterBlock (Itasca.Wasm2.blockType bt) front params results compiler.function.code.val.length true) ∧
        (∀ scope frame, FrameScope locals compiler scope frame → FrameScope locals after scope frame) := by
  have effect := callback_block ops law compiler state ctrl prior bt signature pc controls selected valuesFit heightFits
    sourceFits position mapsFit framesFit reachable
  rw [accepted, WP.spec_ok] at effect
  dsimp only at effect
  obtain ⟨codeEq, live, height, source, heightEq, sourceEq, framesEq, mapsEq⟩ := effect rfl
  refine ⟨codeEq, live, height, source, sourceEq, framesEq, mapsEq, ?_, ?_, ?_⟩
  · have fresh := FrameScope.enter_block after locals front params results (Itasca.Wasm2.blockType bt)
      (alloc.vec.Vec.len compiler.function.controls) height signature.param_slots signature.result_slots pc true
      paramsWidth resultsWidth (by intro _; simpa only [localWidth, frontWidth] using heightEq)
      (by simp [mapsEq])
      (by simpa only [codeEq, position] using Nat.le_refl compiler.function.code.val.length)
    simpa only [position] using fresh
  · exact nested.enter_block parentShape (Itasca.Wasm2.blockType bt) front params results true
  · intro scope frame old
    exact old.extend [] (by simp only [codeEq, List.append_nil]) (by simp [mapsEq])

/-- A successful actual LOOP callback creates its source-aligned frame
and preserves every retained outer frame's physical entry evidence. -/
theorem callback_loop_scope {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (ctrl : Itasca.code.Ctrl) (prior : List Itasca.code.Ctrl)
    (bt : Itasca.signature.BlockType) (signature : runtime.compiler.Signature) (pc : U32)
    (locals front params results : List valtype) (parents : List SourceScope)
    (current : SourceScope) (parentFrame : runtime.compiler.Frame)
    (nested : ScopeNesting parents current) (parentShape : FrameScope locals compiler current parentFrame)
    (localWidth : compiler.function.local_slots.val = slots locals)
    (frontWidth : stackWords (state.vals.val.take ctrl.value_stack_base.val) = slots front)
    (paramsWidth : signature.param_slots.val = slots params)
    (resultsWidth : signature.result_slots.val = slots results)
    (controls : state.ctrls.val = prior ++ [ctrl])
    (selected : SignatureAt compiler.signatures bt signature)
    (valuesFit : ctrl.value_stack_base.val ≤ state.vals.val.length)
    (heightFits : compiler.function.local_slots.val +
      stackWords (state.vals.val.take ctrl.value_stack_base.val) ≤ U32.max)
    (sourceFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max)
    (position : pc.val = compiler.function.code.val.length)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (offsetsFit : compiler.function.source_offsets.val.length < Usize.max)
    (mapsFit : compiler.function.controls.val.length < Usize.max)
    (framesFit : compiler.frames.val.length < Usize.max)
    (reachable : compiler.reachable = true)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_loop ops compiler state bt =
      .ok (.Ok (), after)) :
    after.function.code.val = compiler.function.code.val ++ [.LoopHead] ∧ after.reachable = true ∧
      ∃ height source,
        source.val = compiler.function.body_start.val + compiler.next_source.val ∧
        after.frames.val = compiler.frames.val ++
          [⟨alloc.vec.Vec.len compiler.function.controls, .Loop, height, signature.param_slots,
            signature.result_slots, pc, none, true, false, alloc.vec.Vec.new Usize⟩] ∧
        after.function.controls.val = compiler.function.controls.val ++
          [⟨.Loop, source, 0#usize, UScalar.cast .Usize pc, 0#usize,
            ctrl.value_stack_base, signature.params, signature.results⟩] ∧
        FrameScope locals after
          (SourceScope.enterLoop (Itasca.Wasm2.blockType bt) front params results compiler.function.code.val.length true)
          ⟨alloc.vec.Vec.len compiler.function.controls, .Loop, height, signature.param_slots,
            signature.result_slots, pc, none, true, false, alloc.vec.Vec.new Usize⟩ ∧
        ScopeNesting (parents ++ [current])
          (SourceScope.enterLoop (Itasca.Wasm2.blockType bt) front params results compiler.function.code.val.length true) ∧
        (∀ scope frame, FrameScope locals compiler scope frame → FrameScope locals after scope frame) := by
  have effect := callback_loop ops law compiler state ctrl prior bt signature pc controls selected valuesFit heightFits
    sourceFits position codeFits offsetsFit mapsFit framesFit reachable
  rw [accepted, WP.spec_ok] at effect
  dsimp only at effect
  obtain ⟨codeEq, live, height, source, heightEq, sourceEq, framesEq, mapsEq⟩ := effect rfl
  refine ⟨codeEq, live, height, source, sourceEq, framesEq, mapsEq, ?_, ?_, ?_⟩
  · have fresh := FrameScope.enter_loop after locals front params results (Itasca.Wasm2.blockType bt)
      (alloc.vec.Vec.len compiler.function.controls) height signature.param_slots signature.result_slots pc true
      paramsWidth resultsWidth (by intro _; simpa only [localWidth, frontWidth] using heightEq)
      (by simp [mapsEq])
      (by simp [codeEq, position])
      (by intro _; simp [codeEq, position])
    simpa only [position] using fresh
  · exact nested.enter_loop parentShape (Itasca.Wasm2.blockType bt) front params results true
  · intro scope frame old
    exact old.extend [.LoopHead] (codeEq) (by simp [mapsEq])

end Itasca.Runtime.Compiler

end

/-! ## ScopeCallbackDead -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Dormant BLOCK entry pushes its exact physical frame and source
scope while emitting no guard or hook and imposing no live height equation. -/
theorem callback_block_dead_scope {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (ctrl : Itasca.code.Ctrl) (prior : List Itasca.code.Ctrl)
    (bt : Itasca.signature.BlockType) (signature : runtime.compiler.Signature) (pc : U32)
    (locals front params results : List valtype) (parents : List SourceScope)
    (current : SourceScope) (parentFrame : runtime.compiler.Frame)
    (nested : ScopeNesting parents current) (parentShape : FrameScope locals compiler current parentFrame)
    (paramsWidth : signature.param_slots.val = slots params)
    (resultsWidth : signature.result_slots.val = slots results)
    (controls : state.ctrls.val = prior ++ [ctrl])
    (selected : SignatureAt compiler.signatures bt signature)
    (valuesFit : ctrl.value_stack_base.val ≤ state.vals.val.length)
    (heightFits : compiler.function.local_slots.val +
      stackWords (state.vals.val.take ctrl.value_stack_base.val) ≤ U32.max)
    (sourceFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max)
    (position : pc.val = compiler.function.code.val.length)
    (mapsFit : compiler.function.controls.val.length < Usize.max)
    (framesFit : compiler.frames.val.length < Usize.max)
    (reachable : compiler.reachable = false)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_block ops compiler state bt =
      .ok (.Ok (), after)) :
    after.function.code = compiler.function.code ∧ after.reachable = false ∧
      ∃ height source,
        source.val = compiler.function.body_start.val + compiler.next_source.val ∧
        after.frames.val = compiler.frames.val ++
          [⟨alloc.vec.Vec.len compiler.function.controls, .Block, height, signature.param_slots,
            signature.result_slots, pc, none, false, false, alloc.vec.Vec.new Usize⟩] ∧
        after.function.controls.val = compiler.function.controls.val ++
          [⟨.Block, source, 0#usize, UScalar.cast .Usize pc, 0#usize,
            ctrl.value_stack_base, signature.params, signature.results⟩] ∧
        FrameScope locals after (SourceScope.enterBlock (Itasca.Wasm2.blockType bt) front params results compiler.function.code.val.length false)
          ⟨alloc.vec.Vec.len compiler.function.controls, .Block, height, signature.param_slots,
            signature.result_slots, pc, none, false, false, alloc.vec.Vec.new Usize⟩ ∧
        ScopeNesting (parents ++ [current]) (SourceScope.enterBlock (Itasca.Wasm2.blockType bt) front params results compiler.function.code.val.length false) ∧
        (∀ scope frame, FrameScope locals compiler scope frame → FrameScope locals after scope frame) := by
  have effect := enter_dead ops law compiler state ctrl prior .Block bt signature pc controls selected
    valuesFit heightFits sourceFits position mapsFit framesFit reachable
  have call : runtime.compiler.control.FunctionCompiler.enter ops compiler state .Block bt = .ok (.Ok (), after) :=
    accepted
  rw [call, WP.spec_ok] at effect
  dsimp only at effect
  obtain ⟨codeEq, live, height, source, heightEq, sourceEq, framesEq, mapsEq⟩ := effect rfl
  refine ⟨codeEq, live, height, source, sourceEq, framesEq, mapsEq, ?_, ?_, ?_⟩
  · have fresh := FrameScope.enter_block after locals front params results (Itasca.Wasm2.blockType bt)
      (alloc.vec.Vec.len compiler.function.controls) height signature.param_slots signature.result_slots pc false
      paramsWidth resultsWidth (by simp) (by simp [mapsEq]) (by simp [codeEq, position])
    simpa only [position, alloc.vec.Vec.len_val, Bool.false_eq_true, ↓reduceIte] using fresh
  · exact nested.enter_block parentShape (Itasca.Wasm2.blockType bt) front params results false
  · intro scope frame old
    exact old.extend [] (by simp only [codeEq, List.append_nil]) (by simp [mapsEq])

/-- Dormant LOOP entry pushes its exact physical frame and source
scope while emitting no guard or hook and imposing no live height equation. -/
theorem callback_loop_dead_scope {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (ctrl : Itasca.code.Ctrl) (prior : List Itasca.code.Ctrl)
    (bt : Itasca.signature.BlockType) (signature : runtime.compiler.Signature) (pc : U32)
    (locals front params results : List valtype) (parents : List SourceScope)
    (current : SourceScope) (parentFrame : runtime.compiler.Frame)
    (nested : ScopeNesting parents current) (parentShape : FrameScope locals compiler current parentFrame)
    (paramsWidth : signature.param_slots.val = slots params)
    (resultsWidth : signature.result_slots.val = slots results)
    (controls : state.ctrls.val = prior ++ [ctrl])
    (selected : SignatureAt compiler.signatures bt signature)
    (valuesFit : ctrl.value_stack_base.val ≤ state.vals.val.length)
    (heightFits : compiler.function.local_slots.val +
      stackWords (state.vals.val.take ctrl.value_stack_base.val) ≤ U32.max)
    (sourceFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max)
    (position : pc.val = compiler.function.code.val.length)
    (mapsFit : compiler.function.controls.val.length < Usize.max)
    (framesFit : compiler.frames.val.length < Usize.max)
    (reachable : compiler.reachable = false)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_loop ops compiler state bt =
      .ok (.Ok (), after)) :
    after.function.code = compiler.function.code ∧ after.reachable = false ∧
      ∃ height source,
        source.val = compiler.function.body_start.val + compiler.next_source.val ∧
        after.frames.val = compiler.frames.val ++
          [⟨alloc.vec.Vec.len compiler.function.controls, .Loop, height, signature.param_slots,
            signature.result_slots, pc, none, false, false, alloc.vec.Vec.new Usize⟩] ∧
        after.function.controls.val = compiler.function.controls.val ++
          [⟨.Loop, source, 0#usize, UScalar.cast .Usize pc, 0#usize,
            ctrl.value_stack_base, signature.params, signature.results⟩] ∧
        FrameScope locals after (SourceScope.enterLoop (Itasca.Wasm2.blockType bt) front params results compiler.function.code.val.length false)
          ⟨alloc.vec.Vec.len compiler.function.controls, .Loop, height, signature.param_slots,
            signature.result_slots, pc, none, false, false, alloc.vec.Vec.new Usize⟩ ∧
        ScopeNesting (parents ++ [current]) (SourceScope.enterLoop (Itasca.Wasm2.blockType bt) front params results compiler.function.code.val.length false) ∧
        (∀ scope frame, FrameScope locals compiler scope frame → FrameScope locals after scope frame) := by
  have effect := enter_dead ops law compiler state ctrl prior .Loop bt signature pc controls selected
    valuesFit heightFits sourceFits position mapsFit framesFit reachable
  have call : runtime.compiler.control.FunctionCompiler.enter ops compiler state .Loop bt = .ok (.Ok (), after) :=
    accepted
  rw [call, WP.spec_ok] at effect
  dsimp only at effect
  obtain ⟨codeEq, live, height, source, heightEq, sourceEq, framesEq, mapsEq⟩ := effect rfl
  refine ⟨codeEq, live, height, source, sourceEq, framesEq, mapsEq, ?_, ?_, ?_⟩
  · have fresh := FrameScope.enter_loop after locals front params results (Itasca.Wasm2.blockType bt)
      (alloc.vec.Vec.len compiler.function.controls) height signature.param_slots signature.result_slots pc false
      paramsWidth resultsWidth (by simp) (by simp [mapsEq]) (by simp [codeEq, position]) (by simp)
    simpa only [position, alloc.vec.Vec.len_val, Bool.false_eq_true, ↓reduceIte] using fresh
  · exact nested.enter_loop parentShape (Itasca.Wasm2.blockType bt) front params results false
  · intro scope frame old
    exact old.extend [] (by simp only [codeEq, List.append_nil]) (by simp [mapsEq])

/-- Dormant IF entry pushes its exact physical frame and source
scope while emitting no guard or hook and imposing no live height equation. -/
theorem callback_if_dead_scope {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (ctrl : Itasca.code.Ctrl) (prior : List Itasca.code.Ctrl)
    (bt : Itasca.signature.BlockType) (signature : runtime.compiler.Signature) (pc : U32)
    (locals front params results : List valtype) (parents : List SourceScope)
    (current : SourceScope) (parentFrame : runtime.compiler.Frame)
    (nested : ScopeNesting parents current) (parentShape : FrameScope locals compiler current parentFrame)
    (paramsWidth : signature.param_slots.val = slots params)
    (resultsWidth : signature.result_slots.val = slots results)
    (controls : state.ctrls.val = prior ++ [ctrl])
    (selected : SignatureAt compiler.signatures bt signature)
    (valuesFit : ctrl.value_stack_base.val ≤ state.vals.val.length)
    (heightFits : compiler.function.local_slots.val +
      stackWords (state.vals.val.take ctrl.value_stack_base.val) ≤ U32.max)
    (sourceFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max)
    (position : pc.val = compiler.function.code.val.length)
    (mapsFit : compiler.function.controls.val.length < Usize.max)
    (framesFit : compiler.frames.val.length < Usize.max)
    (reachable : compiler.reachable = false)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_if ops compiler state bt =
      .ok (.Ok (), after)) :
    after.function.code = compiler.function.code ∧ after.reachable = false ∧
      ∃ height source,
        source.val = compiler.function.body_start.val + compiler.next_source.val ∧
        after.frames.val = compiler.frames.val ++
          [⟨alloc.vec.Vec.len compiler.function.controls, .Then, height, signature.param_slots,
            signature.result_slots, pc, none, false, false, alloc.vec.Vec.new Usize⟩] ∧
        after.function.controls.val = compiler.function.controls.val ++
          [⟨.Then, source, 0#usize, UScalar.cast .Usize pc, 0#usize,
            ctrl.value_stack_base, signature.params, signature.results⟩] ∧
        FrameScope locals after (SourceScope.enterIf (Itasca.Wasm2.blockType bt) 0#u32 front params results compiler.function.code.val.length false)
          ⟨alloc.vec.Vec.len compiler.function.controls, .Then, height, signature.param_slots,
            signature.result_slots, pc, none, false, false, alloc.vec.Vec.new Usize⟩ ∧
        ScopeNesting (parents ++ [current]) (SourceScope.enterIf (Itasca.Wasm2.blockType bt) 0#u32 front params results compiler.function.code.val.length false) ∧
        (∀ scope frame, FrameScope locals compiler scope frame → FrameScope locals after scope frame) := by
  have effect := enter_dead ops law compiler state ctrl prior .Then bt signature pc controls selected
    valuesFit heightFits sourceFits position mapsFit framesFit reachable
  have call : runtime.compiler.control.FunctionCompiler.enter ops compiler state .Then bt = .ok (.Ok (), after) :=
    accepted
  rw [call, WP.spec_ok] at effect
  dsimp only at effect
  obtain ⟨codeEq, live, height, source, heightEq, sourceEq, framesEq, mapsEq⟩ := effect rfl
  refine ⟨codeEq, live, height, source, sourceEq, framesEq, mapsEq, ?_, ?_, ?_⟩
  · have fresh := FrameScope.enter_if after locals front params results (Itasca.Wasm2.blockType bt)
      0#u32 (alloc.vec.Vec.len compiler.function.controls) (alloc.vec.Vec.len compiler.function.code)
      height signature.param_slots signature.result_slots pc false paramsWidth resultsWidth
      (by simp) (by simp [mapsEq]) (by simpa using position)
      (by simp [codeEq, position]) (by simp)
    simpa only [position, alloc.vec.Vec.len_val, Bool.false_eq_true, ↓reduceIte] using fresh
  · exact nested.enter_if parentShape (Itasca.Wasm2.blockType bt) 0#u32 front params results false
  · intro scope frame old
    exact old.extend [] (by simp only [codeEq, List.append_nil]) (by simp [mapsEq])

end Itasca.Runtime.Compiler

end

/-! ## ScopeCallbackIf -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- A successful live IF callback retains its actual condition slot and guard,
then pushes the source-aligned THEN frame without changing any outer entry. -/
theorem callback_if_scope {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (ctrl : Itasca.code.Ctrl) (prior : List Itasca.code.Ctrl)
    (bt : Itasca.signature.BlockType) (signature : runtime.compiler.Signature) (pc : U32)
    (locals front params results stack : List valtype) (parents : List SourceScope)
    (current : SourceScope) (parentFrame : runtime.compiler.Frame)
    (nested : ScopeNesting parents current) (parentShape : FrameScope locals compiler current parentFrame)
    (localWidth : compiler.function.local_slots.val = slots locals)
    (frontWidth : stackWords (state.vals.val.take ctrl.value_stack_base.val) = slots front)
    (paramsWidth : signature.param_slots.val = slots params)
    (resultsWidth : signature.result_slots.val = slots results)
    (layout : CompilerLayout compiler (stack ++ [.I32]))
    (codeFits : compiler.function.code.val.length < Usize.max)
    (offsetsFit : compiler.function.source_offsets.val.length < Usize.max)
    (controls : state.ctrls.val = prior ++ [ctrl])
    (selected : SignatureAt compiler.signatures bt signature)
    (valuesFit : ctrl.value_stack_base.val ≤ state.vals.val.length)
    (heightFits : compiler.function.local_slots.val +
      stackWords (state.vals.val.take ctrl.value_stack_base.val) ≤ U32.max)
    (sourceFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max)
    (position : pc.val = compiler.function.code.val.length + 1)
    (mapsFit : compiler.function.controls.val.length < Usize.max)
    (framesFit : compiler.frames.val.length < Usize.max)
    (reachable : compiler.reachable = true)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_if ops compiler state bt =
      .ok (.Ok (), after)) :
    after.reachable = true ∧ ∃ condition height source,
      condition.val = slots (compilerLocals compiler) + slots stack ∧
      source.val = compiler.function.body_start.val + compiler.next_source.val ∧
      after.function.code.val = compiler.function.code.val ++ [.JumpIfZero condition core.num.U32.MAX] ∧
      after.frames.val = compiler.frames.val ++
        [⟨alloc.vec.Vec.len compiler.function.controls, .Then, height, signature.param_slots,
          signature.result_slots, pc, some (alloc.vec.Vec.len compiler.function.code), true, false, alloc.vec.Vec.new Usize⟩] ∧
      after.function.controls.val = compiler.function.controls.val ++
        [⟨.Then, source, 0#usize, UScalar.cast .Usize pc, 0#usize,
          ctrl.value_stack_base, signature.params, signature.results⟩] ∧
      FrameScope locals after
        (SourceScope.enterIf (Itasca.Wasm2.blockType bt) condition front params results compiler.function.code.val.length true)
        ⟨alloc.vec.Vec.len compiler.function.controls, .Then, height, signature.param_slots,
          signature.result_slots, pc, some (alloc.vec.Vec.len compiler.function.code), true, false, alloc.vec.Vec.new Usize⟩ ∧
      ScopeNesting (parents ++ [current])
        (SourceScope.enterIf (Itasca.Wasm2.blockType bt) condition front params results compiler.function.code.val.length true) ∧
      (∀ scope frame, FrameScope locals compiler scope frame → FrameScope locals after scope frame) := by
  have effect := callback_if ops law compiler state ctrl prior bt signature pc stack layout codeFits offsetsFit
    controls selected valuesFit heightFits sourceFits position mapsFit framesFit reachable
  rw [accepted, WP.spec_ok] at effect
  dsimp only at effect
  obtain ⟨live, condition, height, source, coordinate, codeEq, heightEq, sourceEq, framesEq, mapsEq⟩ := effect rfl
  refine ⟨live, condition, height, source, coordinate, sourceEq, codeEq, framesEq, mapsEq, ?_, ?_, ?_⟩
  · have fresh := FrameScope.enter_if after locals front params results (Itasca.Wasm2.blockType bt)
      condition (alloc.vec.Vec.len compiler.function.controls) (alloc.vec.Vec.len compiler.function.code)
      height signature.param_slots signature.result_slots pc true paramsWidth resultsWidth
      (by intro _; simpa only [localWidth, frontWidth] using heightEq)
      (by simp [mapsEq]) (by simpa using position) (by simp [codeEq, position])
      (by intro _; simp [codeEq])
    simpa using fresh
  · exact nested.enter_if parentShape (Itasca.Wasm2.blockType bt) condition front params results true
  · intro scope frame old
    exact old.extend [.JumpIfZero condition core.num.U32.MAX] codeEq (by simp [mapsEq])

end Itasca.Runtime.Compiler

end

/-! ## CallbackGrowth -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
open Lean Meta Elab Tactic in
elab "growth_control_effect " h:ident " using " ops:term ", " law:term : tactic => withMainContext do
  let hyp ← elabTerm h none
  let ty ← inferType hyp
  let some (_, lhs, _) := ty.eq? | throwError "not an equation"
  if lhs.getAppFn.constName? = some ``runtime.compiler.control.FunctionCompiler.branch then
    evalTactic (← `(tactic| have effect := compiler_branch_growth $ops $law _ _ _ _ _ _ $h;
      simp only [Bool.false_eq_true, ite_false, ite_true] at effect))

  else
    evalTactic (← `(tactic| growth_effect $h using $ops, $law))

macro "growth_control_step " h:ident " using " ops:term ", " law:term : tactic => `(tactic|
  first
  | solve | (growth_control_effect $h using $ops, $law; growth_close)
  | solve | (simp only [Result.ok.injEq, Prod.mk.injEq] at $h:ident; obtain ⟨_, output⟩ := $h; cases output; growth_close)
  | (obtain ⟨value, called, rest⟩ := bind_ok_inv _ _ _ $h
     clear $h
     rename' rest => $h
     first
     | (guard_hyp value : Prod _ _; rcases value with ⟨firstValue, secondValue⟩)
     | skip
     try growth_control_effect called using $ops, $law
     try simp only [uncurry_apply_pair] at $h:ident)
  | (fail_if_no_progress simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, bind_ok, bind_tc_ok] at $h:ident)
  | split at $h:ident)

end Itasca.Runtime.Compiler

end

/-! ## CallbackCapacity -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem compiler_branch_capacity_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (depth skip : U32) (conditional : Bool) (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops before depth skip conditional = .ok (status, after)) :
    status = .Ok () → capacityMetadata after = capacityMetadata before := by
  intro success
  subst status
  exact compiler_branch_capacity ops law before after depth skip conditional accepted

open Lean Meta Elab Tactic in
elab "control_capacity_effect " h:ident " using " ops:term ", " law:term : tactic => withMainContext do
  let hyp ← elabTerm h none
  let ty ← inferType hyp
  let some (_, lhs, _) := ty.eq? | throwError "not an equation"
  if lhs.getAppFn.constName? = some ``runtime.compiler.control.FunctionCompiler.branch then
    evalTactic (← `(tactic| have effect := compiler_branch_capacity_result $ops $law _ _ _ _ _ _ $h))
  else
    evalTactic (← `(tactic| capacity_effect $h using $ops, $law))
macro "control_capacity_step " h:ident " using " ops:term ", " law:term : tactic => `(tactic|
  first
  | solve | (sources_terminal $h; capacity_close)
  | (fail_if_no_progress dsimp only at $h:ident)
  | solve | (control_capacity_effect $h using $ops, $law; capacity_close)
  | solve | (sources_terminal $h; have output := (Prod.mk.inj (Result.ok.injEq.mp $h)).2; cases output; capacity_close)
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
     try control_capacity_effect called using $ops, $law
     first
     | (guard_hyp firstValue : core.result.Result _ _; cases firstValue)
     | (guard_hyp value : core.result.Result _ _; cases value)
     | skip
     try simp only [uncurry_apply_pair] at $h:ident)
  | (fail_if_no_progress simp only [Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, bind_ok, bind_tc_ok] at $h:ident)
  | sources_split $h)

theorem compiler_unreachable_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable
      ops before state = .ok (.Ok (), after)) :
    CapacityStep before after state := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable at accepted
  repeat' control_capacity_step accepted using ops, law

theorem compiler_return_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return
      ops before state = .ok (.Ok (), after)) :
    CapacityStep before after state := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return at accepted
  repeat' control_capacity_step accepted using ops, law

theorem compiler_br_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (depth : U32) (types : Itasca.signature.ResultType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br
      ops before state depth types = .ok (.Ok (), after)) :
    CapacityStep before after state := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br at accepted
  repeat' control_capacity_step accepted using ops, law

theorem compiler_br_if_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (depth : U32) (types : Itasca.signature.ResultType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if
      ops before state depth types = .ok (.Ok (), after)) :
    CapacityStep before after state := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if at accepted
  repeat' control_capacity_step accepted using ops, law


theorem compiler_block_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_block
      ops before state bt = .ok (.Ok (), after)) : CapacityStep before after state := by
  exact compiler_enter_capacity ops law before after state .Block bt accepted

theorem compiler_loop_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_loop
      ops before state bt = .ok (.Ok (), after)) : CapacityStep before after state := by
  exact compiler_enter_capacity ops law before after state .Loop bt accepted

theorem compiler_if_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_if
      ops before state bt = .ok (.Ok (), after)) : CapacityStep before after state := by
  exact compiler_enter_capacity ops law before after state .Then bt accepted

end Itasca.Runtime.Compiler

end

/-! ## CompilerCodeMonotoneCallbacks -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
theorem compiler_unreachable_code_mono {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable
      ops before state = .ok (.Ok (), after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable at accepted
  repeat' code_mono_step accepted using ops, law

theorem compiler_return_code_mono {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return
      ops before state = .ok (.Ok (), after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return at accepted
  repeat' code_mono_step accepted using ops, law

theorem compiler_br_code_mono {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (depth : U32) (types : Itasca.signature.ResultType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br
      ops before state depth types = .ok (.Ok (), after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br at accepted
  repeat' code_mono_step accepted using ops, law

theorem compiler_br_if_code_mono {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (depth : U32) (types : Itasca.signature.ResultType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if
      ops before state depth types = .ok (.Ok (), after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if at accepted
  repeat' code_mono_step accepted using ops, law


theorem compiler_block_code_mono {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_block
      ops before state bt = .ok (.Ok (), after)) : before.function.code.val.length ≤ after.function.code.val.length := by
  exact compiler_enter_code_mono ops law before after state .Block bt accepted

theorem compiler_loop_code_mono {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_loop
      ops before state bt = .ok (.Ok (), after)) : before.function.code.val.length ≤ after.function.code.val.length := by
  exact compiler_enter_code_mono ops law before after state .Loop bt accepted

theorem compiler_if_code_mono {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_if
      ops before state bt = .ok (.Ok (), after)) : before.function.code.val.length ≤ after.function.code.val.length := by
  exact compiler_enter_code_mono ops law before after state .Then bt accepted

end Itasca.Runtime.Compiler

end
