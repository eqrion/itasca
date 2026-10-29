import Itasca.Runtime.Compiler.Local.Callbacks.Calls.ScopeCallbackEnter

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
