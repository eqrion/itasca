import Itasca.Runtime.Compiler.Local.Callbacks.Control.EnterContracts
import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.FixupAlgebra
import Itasca.Runtime.Compiler.Local.Callbacks.Observation.Frame
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlLayout

/-!
Sections, each formerly its own module: CloseBlock, EnterBlock, EnterLoop, EnterIf.
-/

/-! ## CloseBlock -/

section

/-! Closing a reachable ordinary block removes its compiler frame, resolves
its complete forward-fixup list, records the source/bytecode exit coordinates,
and preserves reachability. The proof follows the actual extracted callback. -/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

theorem compiler_pc_eq {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (target : U32)
    (position : target.val = compiler.function.code.val.length) :
    runtime.compiler.FunctionCompiler.pc ops compiler = .ok (.Ok target, compiler) := by
  have bound : compiler.function.code.length ≤ U32.max := by
    simp only [alloc.vec.Vec.length, ← position]
    scalar_tac
  obtain ⟨output, run, effect⟩ :=
    WP.spec_imp_exists (compiler_pc_available ops compiler bound)
  rcases output with ⟨status, after⟩
  dsimp only at effect
  obtain ⟨same, pc, success, pcLength⟩ := effect
  rw [same, success] at run
  have pcEq : pc = target := by
    apply UScalar.eq_of_val_eq
    exact pcLength.trans position.symm
  subst pc
  exact run

end Itasca.Runtime.Compiler

end

/-! ## EnterBlock -/

section

/-! Exact control-signature selection and the actual ordinary BLOCK callback.
The callback retains the validator control height, source coordinate, signature
widths and forward-fixup frame while leaving bytecode unchanged. -/
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

@[step] theorem enter_block {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (ctrl : Itasca.code.Ctrl) (prior : List Itasca.code.Ctrl)
    (bt : Itasca.signature.BlockType) (signature : runtime.compiler.Signature) (pc : U32)
    (controls : state.ctrls.val = prior ++ [ctrl])
    (selected : SignatureAt compiler.signatures bt signature)
    (valuesFit : ctrl.value_stack_base.val ≤ state.vals.val.length)
    (heightFits : compiler.function.local_slots.val +
      stackWords (state.vals.val.take ctrl.value_stack_base.val) ≤ U32.max)
    (sourceFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max)
    (position : pc.val = compiler.function.code.val.length)
    (mapsFit : compiler.function.controls.val.length < Usize.max)
    (framesFit : compiler.frames.val.length < Usize.max)
    (reachable : compiler.reachable = true) :
    runtime.compiler.control.FunctionCompiler.enter ops compiler state .Block bt ⦃ out =>
      out.1 = .Ok () → out.2.function.code = compiler.function.code ∧
        out.2.reachable = true ∧
        ∃ height source,
          height.val = compiler.function.local_slots.val + stackWords (state.vals.val.take ctrl.value_stack_base.val) ∧
          source.val = compiler.function.body_start.val + compiler.next_source.val ∧
          out.2.frames.val = compiler.frames.val ++
            [⟨alloc.vec.Vec.len compiler.function.controls, .Block, height, signature.param_slots,
              signature.result_slots, pc, none, true, false, alloc.vec.Vec.new Usize⟩] ∧
          out.2.function.controls.val = compiler.function.controls.val ++
            [⟨.Block, source, 0#usize, UScalar.cast .Usize pc, 0#usize,
              ctrl.value_stack_base, signature.params, signature.results⟩] ⦄ := by
  have bounds : EnterTotalBounds compiler .Block := by
    refine ⟨?_, ?_, sourceFits, mapsFit, framesFit, ?_⟩
    · have bounded := pc.hmax
      scalar_tac
    · intro _ impossible
      cases impossible
    · intro _ impossible
      rcases impossible with impossible | impossible <;> cases impossible
  have total := runtime.compiler.control.FunctionCompiler.enter.total ops compiler state .Block bt
    ⟨prior, ctrl, signature, controls, selected, valuesFit, heightFits⟩ (Or.inl ⟨law, bounds⟩)
  obtain ⟨⟨status, after⟩, called, _⟩ := WP.spec_imp_exists total
  rw [called, WP.spec_ok]
  intro success
  change status = .Ok () at success
  subst status
  obtain ⟨priorFound, ctrlFound, sigFound, height, startPc, condition, source, middle,
    controlsFound, selectedFound, heightEq, sourceEq, operand, publish, observed⟩ :=
      (runtime.compiler.control.FunctionCompiler.enter.inv ops compiler after state .Block bt (.Ok ()) called).2.2 rfl
  have controlEq : ctrlFound = ctrl := by
    have last := congrArg List.getLast? (controlsFound.symm.trans controls)
    simpa only [List.getLast?_append, List.getLast?_singleton, Option.or, Option.some.injEq] using last
  subst ctrlFound
  have signatureEq := block_signature compiler.signatures bt signature selected
  rw [selectedFound, WP.spec_ok] at signatureEq
  change sigFound = signature at signatureEq
  subst sigFound
  have publication := publish law
  have heightExact := control_stack_height_success state.vals.deref ctrl.value_stack_base
    compiler.function.local_slots height (by simpa only [alloc.vec.Vec.deref, Slice.from_val] using valuesFit) heightEq
  simp only [alloc.vec.Vec.deref, Slice.from_val] at heightExact
  have pcEq : startPc = pc := by
    apply UScalar.eq_of_val_eq
    have start := publication.start
    simp only [enterPcAdvance, reachable] at start
    omega
  subst startPc
  have observedFrame := compiler_observe_frame ops law middle state
  rw [observed, WP.spec_ok] at observedFrame
  change after = _ at observedFrame
  have middleFrame := publication.frame
  change middle = _ at middleFrame
  rw [observedFrame]
  refine ⟨?_, ?_, height, source, heightExact, sourceEq, ?_, ?_⟩
  · apply alloc.vec.Vec.ext
    simpa only [enterPrefix, reachable, List.append_nil] using publication.code
  · rw [middleFrame]
    exact reachable
  · simpa only [enterIfPc, reachable] using publication.frames
  · exact publication.controls


@[step] theorem callback_block {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (ctrl : Itasca.code.Ctrl) (prior : List Itasca.code.Ctrl)
    (bt : Itasca.signature.BlockType) (signature : runtime.compiler.Signature) (pc : U32)
    (controls : state.ctrls.val = prior ++ [ctrl])
    (selected : SignatureAt compiler.signatures bt signature)
    (valuesFit : ctrl.value_stack_base.val ≤ state.vals.val.length)
    (heightFits : compiler.function.local_slots.val +
      stackWords (state.vals.val.take ctrl.value_stack_base.val) ≤ U32.max)
    (sourceFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max)
    (position : pc.val = compiler.function.code.val.length)
    (mapsFit : compiler.function.controls.val.length < Usize.max)
    (framesFit : compiler.frames.val.length < Usize.max)
    (reachable : compiler.reachable = true) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_block ops compiler state bt ⦃ out =>
      out.1 = .Ok () → out.2.function.code = compiler.function.code ∧
        out.2.reachable = true ∧
        ∃ height source,
          height.val = compiler.function.local_slots.val + stackWords (state.vals.val.take ctrl.value_stack_base.val) ∧
          source.val = compiler.function.body_start.val + compiler.next_source.val ∧
          out.2.frames.val = compiler.frames.val ++
            [⟨alloc.vec.Vec.len compiler.function.controls, .Block, height, signature.param_slots,
              signature.result_slots, pc, none, true, false, alloc.vec.Vec.new Usize⟩] ∧
          out.2.function.controls.val = compiler.function.controls.val ++
            [⟨.Block, source, 0#usize, UScalar.cast .Usize pc, 0#usize,
              ctrl.value_stack_base, signature.params, signature.results⟩] ⦄ := by
  simpa only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_block] using
    enter_block ops law compiler state ctrl prior bt signature pc controls selected valuesFit heightFits
      sourceFits position mapsFit framesFit reachable
end Itasca.Runtime.Compiler

end

/-! ## EnterLoop -/

section

/-! Actual LOOP entry emits its charged hook instruction and retains exact
control-map and compiler-label coordinates before observing the typed stack. -/
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
@[step] theorem enter_loop {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (ctrl : Itasca.code.Ctrl) (prior : List Itasca.code.Ctrl)
    (bt : Itasca.signature.BlockType) (signature : runtime.compiler.Signature) (pc : U32)
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
    (reachable : compiler.reachable = true) :
    runtime.compiler.control.FunctionCompiler.enter ops compiler state .Loop bt ⦃ out =>
      out.1 = .Ok () → out.2.function.code.val = compiler.function.code.val ++ [.LoopHead] ∧
        out.2.reachable = true ∧
        ∃ height source,
          height.val = compiler.function.local_slots.val + stackWords (state.vals.val.take ctrl.value_stack_base.val) ∧
          source.val = compiler.function.body_start.val + compiler.next_source.val ∧
          out.2.frames.val = compiler.frames.val ++
            [⟨alloc.vec.Vec.len compiler.function.controls, .Loop, height, signature.param_slots,
              signature.result_slots, pc, none, true, false, alloc.vec.Vec.new Usize⟩] ∧
          out.2.function.controls.val = compiler.function.controls.val ++
            [⟨.Loop, source, 0#usize, UScalar.cast .Usize pc, 0#usize,
              ctrl.value_stack_base, signature.params, signature.results⟩] ⦄ := by
  have bounds : EnterTotalBounds compiler .Loop := by
    refine ⟨?_, ?_, sourceFits, mapsFit, framesFit, ?_⟩
    · have bounded := pc.hmax
      scalar_tac
    · intro _ impossible
      cases impossible
    · intro _ _
      exact ⟨codeFits, offsetsFit⟩
  have total := runtime.compiler.control.FunctionCompiler.enter.total ops compiler state .Loop bt
    ⟨prior, ctrl, signature, controls, selected, valuesFit, heightFits⟩ (Or.inl ⟨law, bounds⟩)
  obtain ⟨⟨status, after⟩, called, _⟩ := WP.spec_imp_exists total
  rw [called, WP.spec_ok]
  intro success
  change status = .Ok () at success
  subst status
  obtain ⟨priorFound, ctrlFound, sigFound, height, startPc, condition, source, middle,
    controlsFound, selectedFound, heightEq, sourceEq, operand, publish, observed⟩ :=
      (runtime.compiler.control.FunctionCompiler.enter.inv ops compiler after state .Loop bt (.Ok ()) called).2.2 rfl
  have controlEq : ctrlFound = ctrl := by
    have last := congrArg List.getLast? (controlsFound.symm.trans controls)
    simpa only [List.getLast?_append, List.getLast?_singleton, Option.or, Option.some.injEq] using last
  subst ctrlFound
  have signatureEq := block_signature compiler.signatures bt signature selected
  rw [selectedFound, WP.spec_ok] at signatureEq
  change sigFound = signature at signatureEq
  subst sigFound
  have publication := publish law
  have heightExact := control_stack_height_success state.vals.deref ctrl.value_stack_base
    compiler.function.local_slots height (by simpa only [alloc.vec.Vec.deref, Slice.from_val] using valuesFit) heightEq
  simp only [alloc.vec.Vec.deref, Slice.from_val] at heightExact
  have pcEq : startPc = pc := by
    apply UScalar.eq_of_val_eq
    have start := publication.start
    simp only [enterPcAdvance, reachable] at start
    omega
  subst startPc
  have observedFrame := compiler_observe_frame ops law middle state
  rw [observed, WP.spec_ok] at observedFrame
  change after = _ at observedFrame
  have middleFrame := publication.frame
  change middle = _ at middleFrame
  rw [observedFrame]
  refine ⟨?_, ?_, height, source, heightExact, sourceEq, ?_, ?_⟩
  · simpa only [enterPrefix, reachable] using publication.code
  · rw [middleFrame]
    exact reachable
  · simpa only [enterIfPc, reachable] using publication.frames
  · exact publication.controls


@[step] theorem callback_loop {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (ctrl : Itasca.code.Ctrl) (prior : List Itasca.code.Ctrl)
    (bt : Itasca.signature.BlockType) (signature : runtime.compiler.Signature) (pc : U32)
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
    (reachable : compiler.reachable = true) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_loop ops compiler state bt ⦃ out =>
      out.1 = .Ok () → out.2.function.code.val = compiler.function.code.val ++ [.LoopHead] ∧
        out.2.reachable = true ∧
        ∃ height source,
          height.val = compiler.function.local_slots.val + stackWords (state.vals.val.take ctrl.value_stack_base.val) ∧
          source.val = compiler.function.body_start.val + compiler.next_source.val ∧
          out.2.frames.val = compiler.frames.val ++
            [⟨alloc.vec.Vec.len compiler.function.controls, .Loop, height, signature.param_slots,
              signature.result_slots, pc, none, true, false, alloc.vec.Vec.new Usize⟩] ∧
          out.2.function.controls.val = compiler.function.controls.val ++
            [⟨.Loop, source, 0#usize, UScalar.cast .Usize pc, 0#usize,
              ctrl.value_stack_base, signature.params, signature.results⟩] ⦄ := by
  simpa only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_loop] using
    enter_loop ops law compiler state ctrl prior bt signature pc controls selected valuesFit heightFits
      sourceFits position codeFits offsetsFit mapsFit framesFit reachable
end Itasca.Runtime.Compiler

end

/-! ## EnterIf -/

section

/-! The actual IF callback emits its condition guard and records its fixup
coordinate separately from the body entry, using the live compiler slot layout. -/
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
@[step] theorem enter_if {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (ctrl : Itasca.code.Ctrl) (prior : List Itasca.code.Ctrl)
    (bt : Itasca.signature.BlockType) (signature : runtime.compiler.Signature) (pc : U32)
    (stack : List valtype) (layout : CompilerLayout compiler (stack ++ [.I32]))
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
    (reachable : compiler.reachable = true) :
    runtime.compiler.control.FunctionCompiler.enter ops compiler state .Then bt ⦃ out =>
      out.1 = .Ok () → out.2.reachable = true ∧
        ∃ condition height source,
          condition.val = slots (compilerLocals compiler) + slots stack ∧
          out.2.function.code.val = compiler.function.code.val ++ [.JumpIfZero condition core.num.U32.MAX] ∧
          height.val = compiler.function.local_slots.val + stackWords (state.vals.val.take ctrl.value_stack_base.val) ∧
          source.val = compiler.function.body_start.val + compiler.next_source.val ∧
          out.2.frames.val = compiler.frames.val ++
            [⟨alloc.vec.Vec.len compiler.function.controls, .Then, height, signature.param_slots,
              signature.result_slots, pc, some (alloc.vec.Vec.len compiler.function.code), true, false, alloc.vec.Vec.new Usize⟩] ∧
          out.2.function.controls.val = compiler.function.controls.val ++
            [⟨.Then, source, 0#usize, UScalar.cast .Usize pc, 0#usize,
              ctrl.value_stack_base, signature.params, signature.results⟩] ⦄ := by
  have bounds : EnterTotalBounds compiler .Then := by
    refine ⟨?_, ?_, sourceFits, mapsFit, framesFit, ?_⟩
    · have bounded := pc.hmax
      scalar_tac
    · intro _ _
      have bounded := pc.hmax
      scalar_tac
    · intro _ _
      exact ⟨codeFits, offsetsFit⟩
  have total := runtime.compiler.control.FunctionCompiler.enter.total ops compiler state .Then bt
    ⟨prior, ctrl, signature, controls, selected, valuesFit, heightFits⟩ (Or.inl ⟨law, bounds⟩)
  obtain ⟨⟨status, after⟩, called, _⟩ := WP.spec_imp_exists total
  rw [called, WP.spec_ok]
  intro success
  change status = .Ok () at success
  subst status
  obtain ⟨priorFound, ctrlFound, sigFound, height, startPc, condition, source, middle,
    controlsFound, selectedFound, heightEq, sourceEq, operand, publish, observed⟩ :=
      (runtime.compiler.control.FunctionCompiler.enter.inv ops compiler after state .Then bt (.Ok ()) called).2.2 rfl
  have controlEq : ctrlFound = ctrl := by
    have last := congrArg List.getLast? (controlsFound.symm.trans controls)
    simpa only [List.getLast?_append, List.getLast?_singleton, Option.or, Option.some.injEq] using last
  subst ctrlFound
  have signatureEq := block_signature compiler.signatures bt signature selected
  rw [selectedFound, WP.spec_ok] at signatureEq
  change sigFound = signature at signatureEq
  subst sigFound
  have publication := publish law
  have heightExact := control_stack_height_success state.vals.deref ctrl.value_stack_base
    compiler.function.local_slots height (by simpa only [alloc.vec.Vec.deref, Slice.from_val] using valuesFit) heightEq
  simp only [alloc.vec.Vec.deref, Slice.from_val] at heightExact
  have pcEq : startPc = pc := by
    apply UScalar.eq_of_val_eq
    have start := publication.start
    simp only [enterPcAdvance, reachable] at start
    omega
  subst startPc
  have observedFrame := compiler_observe_frame ops law middle state
  rw [observed, WP.spec_ok] at observedFrame
  change after = _ at observedFrame
  have middleFrame := publication.frame
  change middle = _ at middleFrame
  have conditionSpec := compiler_operand ops compiler (stack ++ [.I32]) layout 1#usize
    (by decide) (by change 1 ≤ (stack ++ [valtype.I32]).length; simp only [List.length_append, List.length_singleton]; omega)
  rw [operand reachable rfl, WP.spec_ok] at conditionSpec
  obtain ⟨actualCondition, conditionEq, coordinate⟩ := conditionSpec
  have sameCondition : condition = actualCondition := core.result.Result.Ok.inj conditionEq
  subst actualCondition
  have conditionCoordinate : condition.val = slots (compilerLocals compiler) + slots stack := by
    simpa only [offset, show (1#usize).val = 1 from rfl, List.length_append, List.length_singleton, Nat.add_sub_cancel,
      List.take_left, List.take_length] using coordinate
  rw [observedFrame]
  refine ⟨?_, condition, height, source, conditionCoordinate, ?_, heightExact, sourceEq, ?_, ?_⟩
  · rw [middleFrame]
    exact reachable
  · simpa only [enterPrefix, reachable] using publication.code
  · simpa only [enterIfPc, reachable] using publication.frames
  · exact publication.controls


@[step] theorem callback_if {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (ctrl : Itasca.code.Ctrl) (prior : List Itasca.code.Ctrl)
    (bt : Itasca.signature.BlockType) (signature : runtime.compiler.Signature) (pc : U32)
    (stack : List valtype) (layout : CompilerLayout compiler (stack ++ [.I32]))
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
    (reachable : compiler.reachable = true) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_if ops compiler state bt ⦃ out =>
      out.1 = .Ok () → out.2.reachable = true ∧
        ∃ condition height source,
          condition.val = slots (compilerLocals compiler) + slots stack ∧
          out.2.function.code.val = compiler.function.code.val ++ [.JumpIfZero condition core.num.U32.MAX] ∧
          height.val = compiler.function.local_slots.val + stackWords (state.vals.val.take ctrl.value_stack_base.val) ∧
          source.val = compiler.function.body_start.val + compiler.next_source.val ∧
          out.2.frames.val = compiler.frames.val ++
            [⟨alloc.vec.Vec.len compiler.function.controls, .Then, height, signature.param_slots,
              signature.result_slots, pc, some (alloc.vec.Vec.len compiler.function.code), true, false, alloc.vec.Vec.new Usize⟩] ∧
          out.2.function.controls.val = compiler.function.controls.val ++
            [⟨.Then, source, 0#usize, UScalar.cast .Usize pc, 0#usize,
              ctrl.value_stack_base, signature.params, signature.results⟩] ⦄ := by
  simpa only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_if] using
    enter_if ops law compiler state ctrl prior bt signature pc stack layout codeFits offsetsFit
      controls selected valuesFit heightFits sourceFits position mapsFit framesFit reachable
end Itasca.Runtime.Compiler

end
