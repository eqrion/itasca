import Exec.Code.Local.Callbacks.Control.EnterLoop
/-! The actual IF callback emits its condition guard and records its fixup
coordinate separately from the body entry, using the live compiler slot layout. -/
namespace Itasca.Runtime.Code
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
end Itasca.Runtime.Code
