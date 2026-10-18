import Exec.Code.Local.Callbacks.Control.EnterBlock
namespace Exec.Code
open Aeneas Aeneas.Std
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
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
  cases kindEq : kind
  all_goals
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
    simp only [runtime.compiler.control.is_then, runtime.compiler.control.is_loop, kindEq, bind_ok,
      reachable, Bool.false_eq_true, ite_false, ite_true]
    rw [compiler_pc_eq ops compiler pc position]
    simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch, reachable,
      Bool.false_eq_true, ite_false, ite_true]
    change WP.spec (Aeneas.Std.bind (core.result.Result.Insts.CoreOpsTry.branch (.Ok pc)) _) _
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    try (change WP.spec (if compiler.reachable = true then _ else _) _; rw [if_neg (by simp [reachable])])
    step with charge_control ops compiler.budget as ⟨charged, budget⟩
    cases charged with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok value =>
      cases value
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step as ⟨start, hstart⟩
      have pushMap := budget_push ops law budget compiler.function.controls
        ⟨kind, source, 0#usize, start, 0#usize, ctrl.value_stack_base, signature.params, signature.results⟩ mapsFit
      simp only [kindEq] at pushMap
      step with pushMap as ⟨result, budget1, maps, pushed⟩
      rcases pushed with ⟨rfl, rfl, mapAppend⟩ | ⟨rfl, rfl, rejected⟩
      · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        have pushFrame := budget_push ops law budget1 compiler.frames
          ⟨alloc.vec.Vec.len compiler.function.controls, kind, height, signature.param_slots,
            signature.result_slots, pc, none, compiler.reachable, false, alloc.vec.Vec.new Usize⟩ framesFit
        simp only [kindEq] at pushFrame
        step with pushFrame as ⟨result, budget2, frames, pushed⟩
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

end Exec.Code
