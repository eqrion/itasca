import Itasca.Runtime.Compiler.Local.Relations.Control.ControlLayout
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CloseBlock
/-! Exact control-signature selection and the actual ordinary BLOCK callback.
The callback retains the validator control height, source coordinate, signature
widths and forward-fixup frame while leaving bytecode unchanged. -/
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

inductive SignatureAt (signatures : Slice runtime.compiler.Signature) :
    Itasca.signature.BlockType → runtime.compiler.Signature → Prop where
  | empty : SignatureAt signatures .Empty ⟨0#usize, 0#usize, 0#u32, 0#u32⟩
  | value (ty : Itasca.types.ValueType) (word : U32)
      (width : word.val = Compiler.width (Itasca.Translate.valueType ty)) :
      SignatureAt signatures (.Value ty) ⟨0#usize, 1#usize, 0#u32, word⟩
  | index (i : U32) (signature : runtime.compiler.Signature)
      (found : signatures.val[i.val]? = some signature) :
      SignatureAt signatures (.TypeIndex i) signature

@[step] theorem block_signature (signatures : Slice runtime.compiler.Signature)
    (bt : Itasca.signature.BlockType) (signature : runtime.compiler.Signature)
    (selected : SignatureAt signatures bt signature) :
    runtime.compiler.control.block_signature signatures bt ⦃ out => out = signature ⦄ := by
  cases selected with
  | empty => simp [runtime.compiler.control.block_signature, WP.spec_ok]
  | value ty word width =>
    unfold runtime.compiler.control.block_signature
    step with compiler_width ty as ⟨out, hout⟩
    have same : out = word := by apply UScalar.eq_of_val_eq; omega
    simp [same]
  | index i signature found =>
    unfold runtime.compiler.control.block_signature
    have bound := (List.getElem?_eq_some_iff.mp found).1
    step as ⟨index, hindex⟩
    step as ⟨out, hout⟩
    simpa [List.getElem?_eq_getElem bound, hindex, hout] using found

@[step] theorem charge_control {A : Type} (ops : runtime.platform.Alloc A)
    (budget : runtime.compiler.Budget A) :
    runtime.compiler.Budget.charge ops budget .Controls ⦃ out => True ⦄ := by
  simp only [runtime.compiler.Budget.charge]
  split
  · simp [runtime.compiler.Budget.reject, WP.spec_ok]
  · step

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
  have nonempty : alloc.vec.Vec.len state.ctrls ≠ 0#usize := by
    intro eq
    have := congrArg UScalar.val eq
    simp [alloc.vec.Vec.len, controls] at this
  unfold runtime.compiler.control.FunctionCompiler.enter
  rw [if_neg nonempty]
  step as ⟨last, hlast⟩
  have atLast : last.val = prior.length := by simp [alloc.vec.Vec.len, controls] at hlast; omega
  step as ⟨actual, hactual⟩
  have actualEq : actual = ctrl := by simpa [atLast, controls] using hactual
  rw [actualEq]
  step with block_signature compiler.signatures bt signature selected as ⟨sig, hsig⟩
  subst sig
  step with control_stack_height state.vals.deref ctrl.value_stack_base compiler.function.local_slots (by simpa [alloc.vec.Vec.deref] using valuesFit) (by simpa [alloc.vec.Vec.deref] using heightFits) as ⟨height, hheight⟩
  step as ⟨source, hsource⟩
  simp only [bind_ok,
    reachable, Bool.false_eq_true, ite_false, ite_true]
  rw [compiler_pc_eq ops compiler pc position]
  simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch, reachable,
    Bool.false_eq_true, ite_false, ite_true]
  step with charge_control ops compiler.budget as ⟨charged, budget, _⟩
  cases charged with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok value =>
    cases value
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step as ⟨start, hstart⟩
    step with budget_push ops law budget compiler.function.controls
      ⟨.Block, source, 0#usize, start, 0#usize, ctrl.value_stack_base, signature.params, signature.results⟩ mapsFit
      as ⟨result, budget1, maps, pushed⟩
    rcases pushed with ⟨rfl, rfl, mapAppend⟩ | ⟨rfl, rfl, rejected⟩
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step with budget_push ops law budget1 compiler.frames
        ⟨alloc.vec.Vec.len compiler.function.controls, .Block, height, signature.param_slots,
          signature.result_slots, pc, none, compiler.reachable, false, alloc.vec.Vec.new Usize⟩ framesFit
        as ⟨result, budget2, frames, pushed⟩
      rcases pushed with ⟨rfl, rfl, frameAppend⟩ | ⟨rfl, rfl, rejected⟩
      · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        step with compiler_observe ops law
          { compiler with budget := budget2, function := { compiler.function with controls := maps }, frames }
          state as ⟨output, observed, accepted⟩
        obtain ⟨hoff, hh, hl, hls, hlo, hr, hcode, hsources, hnext, hcap, hmono, hframes, hcontrols⟩ := observed accepted
        refine ⟨hcode, ?_, height, source, (by simpa [alloc.vec.Vec.deref] using hheight), hsource, ?_, ?_⟩
        · simpa [reachable] using hr
        · simpa [hframes, reachable] using frameAppend
        · rw [hcontrols]
          rw [mapAppend]
          have startEq : start = UScalar.cast .Usize pc := by
            apply UScalar.eq_of_val_eq
            rw [hstart]
          rw [startEq]
      · simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    · simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
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
