import Itasca.Runtime.Compiler.Local.Callbacks.Function.FinishContracts
import Itasca.Runtime.Compiler.Local.Relations.Function.Function
import Itasca.Support.Result
import Itasca.Runtime.Compiler.Local.Callbacks.Control.EnterIf

/-!
Sections, each formerly its own module: Finish, EnterDead.
-/

/-! ## Finish -/

section

/-!
A successful actual finish retains the compiler's function and witnesses that its final bytecode check returned true. No checker totality is assumed.

Main declarations: `compiler_finish_accepted`. A direct consumer is `Compiler.Local.Callbacks.Metadata.CompilerMetadata`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts

end Itasca.Runtime.Compiler

end

/-! ## EnterDead -/

section

/-!
Compiler scope entry when the source is unreachable.

Main declarations: `enter_dead`. A direct consumer is `Compiler.Local.Callbacks.Calls.ScopeCallbackEnter`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
@[step] theorem enter_dead {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (ctrl : Itasca.code.Ctrl) (prior : List Itasca.code.Ctrl)
    (kind : Itasca.code.LabelKind) (bt : Itasca.signature.BlockType) (signature : runtime.compiler.Signature) (pc : U32)
    (controls : state.ctrls.val = prior ++ [ctrl])
    (selected : SignatureAt compiler.signatures bt signature)
    (valuesFit : ctrl.value_stack_base.val ≤ state.vals.val.length)
    (heightFits : compiler.function.local_slots.val +
      stackWords (state.vals.val.take ctrl.value_stack_base.val) ≤ U32.max)
    (sourceFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max)
    (position : pc.val = compiler.function.code.val.length)
    (mapsFit : compiler.function.controls.val.length < Usize.max)
    (framesFit : compiler.frames.val.length < Usize.max)
    (reachable : compiler.reachable = false) :
    runtime.compiler.control.FunctionCompiler.enter ops compiler state kind bt ⦃ out =>
      out.1 = .Ok () → out.2.function.code = compiler.function.code ∧
        out.2.reachable = false ∧
        ∃ height source,
          height.val = compiler.function.local_slots.val + stackWords (state.vals.val.take ctrl.value_stack_base.val) ∧
          source.val = compiler.function.body_start.val + compiler.next_source.val ∧
          out.2.frames.val = compiler.frames.val ++
            [⟨alloc.vec.Vec.len compiler.function.controls, kind, height, signature.param_slots,
              signature.result_slots, pc, none, false, false, alloc.vec.Vec.new Usize⟩] ∧
          out.2.function.controls.val = compiler.function.controls.val ++
            [⟨kind, source, 0#usize, UScalar.cast .Usize pc, 0#usize,
              ctrl.value_stack_base, signature.params, signature.results⟩] ⦄ := by
  have bounds : EnterTotalBounds compiler kind := by
    refine ⟨?_, ?_, sourceFits, mapsFit, framesFit, ?_⟩
    · have bounded := pc.hmax
      scalar_tac
    · intro live
      simp only [reachable, Bool.false_eq_true] at live
    · intro live
      simp only [reachable, Bool.false_eq_true] at live
  have total := runtime.compiler.control.FunctionCompiler.enter.total ops compiler state kind bt
    ⟨prior, ctrl, signature, controls, selected, valuesFit, heightFits⟩ (Or.inl ⟨law, bounds⟩)
  obtain ⟨⟨status, after⟩, called, _⟩ := WP.spec_imp_exists total
  rw [called, WP.spec_ok]
  intro success
  change status = .Ok () at success
  subst status
  obtain ⟨priorFound, ctrlFound, sigFound, height, startPc, condition, source, middle,
    controlsFound, selectedFound, heightEq, sourceEq, operand, publish, observed⟩ :=
      (runtime.compiler.control.FunctionCompiler.enter.inv ops compiler after state kind bt (.Ok ()) called).2.2 rfl
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


end Itasca.Runtime.Compiler

end
