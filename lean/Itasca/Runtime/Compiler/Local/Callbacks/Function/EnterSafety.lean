import Itasca.Runtime.Compiler.Local.Callbacks.Control.EnterIf
import Itasca.Runtime.Compiler.Local.Lowering.Control.LoweringTrap
import Itasca.Runtime.Compiler.Local.Callbacks.Function.EnterDead
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CallbackBounds
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlObservedLayout

/-! The actual IF callback emits its condition guard and records its fixup
coordinate separately from the body entry, using the live compiler slot layout. -/
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
@[step] theorem enter_if_raw {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (ctrl : Itasca.code.Ctrl) (prior : List Itasca.code.Ctrl)
    (bt : Itasca.signature.BlockType) (signature : runtime.compiler.Signature) (pc : U32)
    (conditionWord : U32)
    (conditionAt : compiler.before.val[compiler.before.val.length - 1]? = some conditionWord)
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
          condition = conditionWord ∧
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
  have conditionEq := compiler_condition ops compiler conditionWord conditionAt
  rw [operand reachable rfl, WP.spec_ok] at conditionEq
  have sameCondition : condition = conditionWord := core.result.Result.Ok.inj conditionEq
  rw [observedFrame]
  refine ⟨?_, condition, height, source, sameCondition, ?_, heightExact, sourceEq, ?_, ?_⟩
  · rw [middleFrame]
    exact reachable
  · simpa only [enterPrefix, reachable] using publication.code
  · simpa only [enterIfPc, reachable] using publication.frames
  · exact publication.controls


private theorem enter_if_empty {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (ctrl : Itasca.code.Ctrl) (prior : List Itasca.code.Ctrl)
    (bt : Itasca.signature.BlockType) (signature : runtime.compiler.Signature)
    (controls : state.ctrls.val = prior ++ [ctrl])
    (selected : SignatureAt compiler.signatures bt signature)
    (valuesFit : ctrl.value_stack_base.val ≤ state.vals.val.length)
    (heightFits : compiler.function.local_slots.val + stackWords (state.vals.val.take ctrl.value_stack_base.val) ≤ U32.max)
    (sourceFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max)
    (reachable : compiler.reachable = true) (empty : compiler.before.val = []) :
    runtime.compiler.control.FunctionCompiler.enter ops compiler state .Then bt ⦃ _ => True ⦄ := by
  exact runtime.compiler.control.FunctionCompiler.enter.total ops compiler state .Then bt
    ⟨prior, ctrl, signature, controls, selected, valuesFit, heightFits⟩
    (Or.inr ⟨reachable, rfl, empty, sourceFits⟩)


@[step] theorem compiler_enter_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (ctrl : Itasca.code.Ctrl) (prior : List Itasca.code.Ctrl)
    (kind : Itasca.code.LabelKind) (bt : Itasca.signature.BlockType)
    (signature : runtime.compiler.Signature)
    (controls : state.ctrls.val = prior ++ [ctrl])
    (selected : SignatureAt compiler.signatures bt signature)
    (valuesFit : ctrl.value_stack_base.val ≤ state.vals.val.length)
    (heightFits : compiler.function.local_slots.val +
      stackWords (state.vals.val.take ctrl.value_stack_base.val) ≤ U32.max)
    (sourceFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max)
    (pcBound : compiler.function.code.val.length + 1 < 2^32)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (offsetsFit : compiler.function.source_offsets.val.length < Usize.max)
    (mapsFit : compiler.function.controls.val.length < Usize.max)
    (framesFit : compiler.frames.val.length < Usize.max)
    (ordinary : kind = .Block ∨ kind = .Loop ∨ kind = .Then) :
    runtime.compiler.control.FunctionCompiler.enter ops compiler state kind bt ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  have total : runtime.compiler.control.FunctionCompiler.enter ops compiler state kind bt ⦃ _ => True ⦄ := by
    let pc : U32 := UScalar.ofNatCore compiler.function.code.val.length (by simpa using (show compiler.function.code.val.length < 2^32 by omega))
    have position : pc.val = compiler.function.code.val.length := rfl
    by_cases live : compiler.reachable = true
    · rcases ordinary with rfl | rfl | rfl
      · exact WP.spec_mono (enter_block ops law compiler state ctrl prior bt signature pc controls
          selected valuesFit heightFits sourceFits position mapsFit framesFit live) (by simp)
      · exact WP.spec_mono (enter_loop ops law compiler state ctrl prior bt signature pc controls
          selected valuesFit heightFits sourceFits position codeFits offsetsFit mapsFit framesFit live) (by simp)
      · by_cases empty : compiler.before.val = []
        · exact enter_if_empty ops compiler state ctrl prior bt signature controls selected valuesFit
            heightFits sourceFits live empty
        · let next : U32 := UScalar.ofNatCore (compiler.function.code.val.length + 1) pcBound
          have positive : 0 < compiler.before.val.length := List.length_pos_iff.mpr empty
          have inside : compiler.before.val.length - 1 < compiler.before.val.length := by omega
          have found := List.getElem?_eq_getElem inside
          exact WP.spec_mono (enter_if_raw ops law compiler state ctrl prior bt signature next
            compiler.before.val[compiler.before.val.length - 1] found codeFits offsetsFit controls
            selected valuesFit heightFits sourceFits rfl mapsFit framesFit live) (by simp)
    · have dead : compiler.reachable = false := by simpa using live
      exact WP.spec_mono (enter_dead ops law compiler state ctrl prior kind bt signature pc
        controls selected valuesFit heightFits sourceFits position mapsFit framesFit dead) (by simp)
  obtain ⟨⟨status, after⟩, call, _⟩ := WP.spec_imp_exists total
  rw [call, WP.spec_ok]
  intro accepted
  change status = .Ok () at accepted
  subst status
  obtain ⟨middle, observed⟩ := compiler_enter_observation ops compiler after state kind bt call
  have result := compiler_observe_stack ops law middle state
  rw [observed, WP.spec_ok] at result
  exact result rfl

end Itasca.Runtime.Compiler
