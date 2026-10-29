import Itasca.Runtime.Compiler.Local.Relations.Function.Signatures
import Itasca.Runtime.Compiler.Local.Callbacks.Control.EnterIf
import Itasca.Runtime.Compiler.Local.Callbacks.Function.EnterDead
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ScopeNesting

namespace Itasca.Runtime.Code
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

end Itasca.Runtime.Code
