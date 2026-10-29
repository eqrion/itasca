import Itasca.Runtime.Compiler.Local.Callbacks.Calls.ScopeCallbackEnter

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
