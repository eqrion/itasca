import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.Fixups
import Itasca.Runtime.Compiler.Local.Callbacks.Observation.Observe
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
  unfold runtime.compiler.FunctionCompiler.pc
  simp only [lift, bind_ok]
  split
  · rename_i tooLarge
    have bound := target.hmax
    simp only [alloc.vec.Vec.len, core.num.U32.MAX, U32.rMax] at tooLarge
    scalar_tac
  · congr 3
    apply UScalar.eq_of_val_eq
    simp only [UScalar.cast_val_eq, alloc.vec.Vec.len]
    scalar_tac

end Itasca.Runtime.Compiler

end

/-! ## EnterBlock -/

section

/-! Exact control-signature selection and the actual ordinary BLOCK callback.
The callback retains the validator control height, source coordinate, signature
widths and forward-fixup frame while leaving bytecode unchanged. -/
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

inductive SignatureAt (signatures : Slice runtime.compiler.Signature) :
    Itasca.signature.BlockType → runtime.compiler.Signature → Prop where
  | empty : SignatureAt signatures .Empty ⟨0#usize, 0#usize, 0#u32, 0#u32⟩
  | value (ty : Itasca.wasm_types.ValueType) (word : U32)
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
  simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok, reachable, ite_true]
  step with compiler_emit ops law compiler .LoopHead codeFits offsetsFit sourceFits
    as ⟨result, emitted, emission⟩
  cases result with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok unit =>
    cases unit
    obtain ⟨emittedBudget, emittedCode, emittedSources, rfl, codeAppend, sourceAppend⟩ := emission rfl
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with charge_control ops emittedBudget as ⟨charged, budget, _⟩
    cases charged with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok value =>
      cases value
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step as ⟨start, hstart⟩
      step with budget_push ops law budget compiler.function.controls
        ⟨.Loop, source, 0#usize, start, 0#usize, ctrl.value_stack_base, signature.params, signature.results⟩ mapsFit
        as ⟨result, budget1, maps, pushed⟩
      rcases pushed with ⟨rfl, rfl, mapAppend⟩ | ⟨rfl, rfl, rejected⟩
      · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        step with budget_push ops law budget1 compiler.frames
          ⟨alloc.vec.Vec.len compiler.function.controls, .Loop, height, signature.param_slots,
            signature.result_slots, pc, none, compiler.reachable, false, alloc.vec.Vec.new Usize⟩ framesFit
          as ⟨result, budget2, frames, pushed⟩
        rcases pushed with ⟨rfl, rfl, frameAppend⟩ | ⟨rfl, rfl, rejected⟩
        · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
          step with compiler_observe ops law
            { compiler with budget := budget2, function := { compiler.function with code := emittedCode, source_offsets := emittedSources, controls := maps }, frames }
            state as ⟨output, observed, accepted⟩
          obtain ⟨hoff, hh, hl, hls, hlo, hr, hcode, hsources, hnext, hcap, hmono, hframes, hcontrols⟩ := observed accepted
          refine ⟨?_, ?_, height, source, (by simpa [alloc.vec.Vec.deref] using hheight), hsource, ?_, ?_⟩
          · rw [hcode]
            exact codeAppend
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
  step with compiler_operand ops compiler (stack ++ [.I32]) layout 1#usize (by simp) (by simp)
    as ⟨result, condition, hresult, hcondition⟩
  subst result
  have coordinate : condition.val = slots (compilerLocals compiler) + slots stack := by
    simpa [offset, List.take_length] using hcondition

  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  step with compiler_emit ops law compiler (.JumpIfZero condition core.num.U32.MAX) codeFits offsetsFit sourceFits
    as ⟨result, emitted, emission⟩
  cases result with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok unit =>
    cases unit
    obtain ⟨emittedBudget, emittedCode, emittedSources, rfl, codeAppend, sourceAppend⟩ := emission rfl
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    rw [compiler_pc_eq ops
      { compiler with budget := emittedBudget, function := { compiler.function with code := emittedCode, source_offsets := emittedSources } }
      pc (by simpa [codeAppend] using position)]
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok, reachable, ite_true, Bool.false_eq_true, ite_false]
    step with charge_control ops emittedBudget as ⟨charged, budget, _⟩
    cases charged with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok value =>
      cases value
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step as ⟨start, hstart⟩
      step with budget_push ops law budget compiler.function.controls
        ⟨.Then, source, 0#usize, start, 0#usize, ctrl.value_stack_base, signature.params, signature.results⟩ mapsFit
        as ⟨result, budget1, maps, pushed⟩
      rcases pushed with ⟨rfl, rfl, mapAppend⟩ | ⟨rfl, rfl, rejected⟩
      · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        step with budget_push ops law budget1 compiler.frames
          ⟨alloc.vec.Vec.len compiler.function.controls, .Then, height, signature.param_slots,
            signature.result_slots, pc, some (alloc.vec.Vec.len compiler.function.code), true, false, alloc.vec.Vec.new Usize⟩ framesFit
          as ⟨result, budget2, frames, pushed⟩
        rcases pushed with ⟨rfl, rfl, frameAppend⟩ | ⟨rfl, rfl, rejected⟩
        · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
          step with compiler_observe ops law
            { compiler with reachable := true, budget := budget2, function := { compiler.function with code := emittedCode, source_offsets := emittedSources, controls := maps }, frames }
            state as ⟨output, observed, accepted⟩
          obtain ⟨hoff, hh, hl, hls, hlo, hr, hcode, hsources, hnext, hcap, hmono, hframes, hcontrols⟩ := observed accepted
          refine ⟨?_, condition, height, source, coordinate, ?_, (by simpa [alloc.vec.Vec.deref] using hheight), hsource, ?_, ?_⟩
          · simpa [reachable] using hr
          · rw [hcode]
            exact codeAppend
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
