import Exec.Code.Local.Callbacks.Calls.ScopeCallbackIf
import Exec.Code.Local.Callbacks.Calls.ScopeCallbackDead
import Exec.Code.Local.Callbacks.Control.ScopeFrameStack

namespace Exec.Code
open Aeneas Aeneas.Std

/-- The actual BLOCK callback preserves the complete physical/source
frame-stack alignment when it pushes the new control scope. -/
theorem callback_block_scope_stack {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (ctrl : Itasca.code.Ctrl) (prior : List Itasca.code.Ctrl)
    (bt : Itasca.signature.BlockType) (signature : runtime.compiler.Signature) (pc : U32)
    (locals front params results : List valtype) (parents : List SourceScope)
    (current : SourceScope) (aligned : ScopeFrameStack locals compiler parents current)
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
    ScopeFrameStack locals after (parents ++ [current]) (SourceScope.enterBlock (Itasca.Wasm2.blockType bt) front params results compiler.function.code.val.length true) ∧
      after.reachable = true ∧ after.function.code = compiler.function.code := by
  obtain ⟨oldFrames, parentFrame, oldFramesEq, paired, parentShape⟩ := aligned.split
  obtain ⟨codeEq, live, height, source, sourceEq, framesEq, mapsEq, fresh, nested, retained⟩ := callback_block_scope
    ops law compiler after state ctrl prior bt signature pc locals front params results parents current parentFrame aligned.nested parentShape
    localWidth frontWidth paramsWidth resultsWidth controls selected valuesFit heightFits sourceFits position mapsFit framesFit reachable accepted
  refine ⟨?_, live, codeEq⟩
  exact aligned.push _ _ framesEq retained fresh parentShape.bodyBound
    (by simp [SourceScope.enterBlock])

/-- The actual LOOP callback preserves the complete physical/source
frame-stack alignment when it pushes the new control scope. -/
theorem callback_loop_scope_stack {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (ctrl : Itasca.code.Ctrl) (prior : List Itasca.code.Ctrl)
    (bt : Itasca.signature.BlockType) (signature : runtime.compiler.Signature) (pc : U32)
    (locals front params results : List valtype) (parents : List SourceScope)
    (current : SourceScope) (aligned : ScopeFrameStack locals compiler parents current)
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
    ScopeFrameStack locals after (parents ++ [current]) (SourceScope.enterLoop (Itasca.Wasm2.blockType bt) front params results compiler.function.code.val.length true) ∧
      after.reachable = true ∧ after.function.code.val = compiler.function.code.val ++ [.LoopHead] := by
  obtain ⟨oldFrames, parentFrame, oldFramesEq, paired, parentShape⟩ := aligned.split
  obtain ⟨codeEq, live, height, source, sourceEq, framesEq, mapsEq, fresh, nested, retained⟩ := callback_loop_scope
    ops law compiler after state ctrl prior bt signature pc locals front params results parents current parentFrame aligned.nested parentShape
    localWidth frontWidth paramsWidth resultsWidth controls selected valuesFit heightFits sourceFits position codeFits offsetsFit mapsFit framesFit reachable accepted
  refine ⟨?_, live, codeEq⟩
  exact aligned.push _ _ framesEq retained fresh parentShape.bodyBound
    (by simp [SourceScope.enterLoop])

/-- The actual IF callback preserves the complete physical/source
frame-stack alignment when it pushes the new control scope. -/
theorem callback_if_scope_stack {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (ctrl : Itasca.code.Ctrl) (prior : List Itasca.code.Ctrl)
    (bt : Itasca.signature.BlockType) (signature : runtime.compiler.Signature) (pc : U32)
    (locals front params results stack : List valtype) (parents : List SourceScope)
    (current : SourceScope) (aligned : ScopeFrameStack locals compiler parents current)
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
    ∃ condition, condition.val = slots (compilerLocals compiler) + slots stack ∧
      ScopeFrameStack locals after (parents ++ [current]) (SourceScope.enterIf (Itasca.Wasm2.blockType bt) condition front params results compiler.function.code.val.length true) ∧
      after.reachable = true ∧ after.function.code.val = compiler.function.code.val ++ [.JumpIfZero condition core.num.U32.MAX] := by
  obtain ⟨oldFrames, parentFrame, oldFramesEq, paired, parentShape⟩ := aligned.split
  obtain ⟨live, condition, height, source, coordinate, sourceEq, codeEq, framesEq, mapsEq, fresh, nested, retained⟩ := callback_if_scope
    ops law compiler after state ctrl prior bt signature pc locals front params results stack parents current parentFrame aligned.nested parentShape
    localWidth frontWidth paramsWidth resultsWidth layout codeFits offsetsFit controls selected valuesFit heightFits sourceFits position mapsFit framesFit reachable accepted
  refine ⟨condition, coordinate, ?_, live, codeEq⟩
  exact aligned.push _ _ framesEq retained fresh parentShape.bodyBound
    (by simp [SourceScope.enterIf])

/-- The actual dormant BLOCK callback preserves the complete physical/source
frame-stack alignment when it pushes the new control scope. -/
theorem callback_block_dead_scope_stack {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (ctrl : Itasca.code.Ctrl) (prior : List Itasca.code.Ctrl)
    (bt : Itasca.signature.BlockType) (signature : runtime.compiler.Signature) (pc : U32)
    (locals front params results : List valtype) (parents : List SourceScope)
    (current : SourceScope) (aligned : ScopeFrameStack locals compiler parents current)
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
    ScopeFrameStack locals after (parents ++ [current]) (SourceScope.enterBlock (Itasca.Wasm2.blockType bt) front params results compiler.function.code.val.length false) ∧
      after.reachable = false ∧ after.function.code = compiler.function.code := by
  obtain ⟨oldFrames, parentFrame, oldFramesEq, paired, parentShape⟩ := aligned.split
  obtain ⟨codeEq, live, height, source, sourceEq, framesEq, mapsEq, fresh, nested, retained⟩ := callback_block_dead_scope
    ops law compiler after state ctrl prior bt signature pc locals front params results parents current parentFrame aligned.nested parentShape
    paramsWidth resultsWidth controls selected valuesFit heightFits sourceFits position mapsFit framesFit reachable accepted
  refine ⟨?_, live, codeEq⟩
  exact aligned.push _ _ framesEq retained fresh parentShape.bodyBound
    (by simp [SourceScope.enterBlock])

/-- The actual dormant LOOP callback preserves the complete physical/source
frame-stack alignment when it pushes the new control scope. -/
theorem callback_loop_dead_scope_stack {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (ctrl : Itasca.code.Ctrl) (prior : List Itasca.code.Ctrl)
    (bt : Itasca.signature.BlockType) (signature : runtime.compiler.Signature) (pc : U32)
    (locals front params results : List valtype) (parents : List SourceScope)
    (current : SourceScope) (aligned : ScopeFrameStack locals compiler parents current)
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
    ScopeFrameStack locals after (parents ++ [current]) (SourceScope.enterLoop (Itasca.Wasm2.blockType bt) front params results compiler.function.code.val.length false) ∧
      after.reachable = false ∧ after.function.code = compiler.function.code := by
  obtain ⟨oldFrames, parentFrame, oldFramesEq, paired, parentShape⟩ := aligned.split
  obtain ⟨codeEq, live, height, source, sourceEq, framesEq, mapsEq, fresh, nested, retained⟩ := callback_loop_dead_scope
    ops law compiler after state ctrl prior bt signature pc locals front params results parents current parentFrame aligned.nested parentShape
    paramsWidth resultsWidth controls selected valuesFit heightFits sourceFits position mapsFit framesFit reachable accepted
  refine ⟨?_, live, codeEq⟩
  exact aligned.push _ _ framesEq retained fresh parentShape.bodyBound
    (by simp [SourceScope.enterLoop])

/-- The actual dormant IF callback preserves the complete physical/source
frame-stack alignment when it pushes the new control scope. -/
theorem callback_if_dead_scope_stack {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (ctrl : Itasca.code.Ctrl) (prior : List Itasca.code.Ctrl)
    (bt : Itasca.signature.BlockType) (signature : runtime.compiler.Signature) (pc : U32)
    (locals front params results : List valtype) (parents : List SourceScope)
    (current : SourceScope) (aligned : ScopeFrameStack locals compiler parents current)
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
    ScopeFrameStack locals after (parents ++ [current]) (SourceScope.enterIf (Itasca.Wasm2.blockType bt) 0#u32 front params results compiler.function.code.val.length false) ∧
      after.reachable = false ∧ after.function.code = compiler.function.code := by
  obtain ⟨oldFrames, parentFrame, oldFramesEq, paired, parentShape⟩ := aligned.split
  obtain ⟨codeEq, live, height, source, sourceEq, framesEq, mapsEq, fresh, nested, retained⟩ := callback_if_dead_scope
    ops law compiler after state ctrl prior bt signature pc locals front params results parents current parentFrame aligned.nested parentShape
    paramsWidth resultsWidth controls selected valuesFit heightFits sourceFits position mapsFit framesFit reachable accepted
  refine ⟨?_, live, codeEq⟩
  exact aligned.push _ _ framesEq retained fresh parentShape.bodyBound
    (by simp [SourceScope.enterIf])

end Exec.Code
