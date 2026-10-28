import Itasca.Runtime.Code.Local.Lowering.Control.LoweringForwardBranch
import Itasca.Runtime.Code.Local.Lowering.Control.LoweringLoopBranch
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

@[step] theorem compiler_condition {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (condition : U32)
    (found : compiler.before.val[compiler.before.val.length - 1]? = some condition) :
    runtime.compiler.FunctionCompiler.operand ops compiler 1#usize ⦃ out => out = .Ok condition ⦄ := by
  have bound := (List.getElem?_eq_some_iff.mp found).1
  have exact := (List.getElem?_eq_some_iff.mp found).2
  unfold runtime.compiler.FunctionCompiler.operand
  step with operand_at compiler.before.deref 1#usize (by simp)
    (by simpa [alloc.vec.Vec.deref] using (show 1 ≤ compiler.before.val.length by omega)) as ⟨out, effect⟩
  simpa [alloc.vec.Vec.deref, exact] using effect

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
@[step] theorem branch_if_elided_forward {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source condition : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (forward : frame.kind ≠ .Loop) (elided : frame.results = 0#u32 ∨ source = frame.height)
    (sourcePosition : source.val + frame.results.val + 1 = compiler.height.val)
    (conditionAt : compiler.before.val[compiler.before.val.length - 1]? = some condition)
    (fixupsFit : frame.fixups.val.length < Usize.max)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (offsetsFit : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.control.FunctionCompiler.branch ops compiler depth 1#u32 true ⦃ out =>
      out.1 = .Ok () →
        out.2.function.code.val = compiler.function.code.val ++
          [.JumpIfNonZero condition core.num.U32.MAX] ∧
        ∃ fixups site, site.val = compiler.function.code.val.length ∧
          out.2.frames.val = compiler.frames.val.set index.val { frame with end_reachable := true, fixups } ∧
          fixups.val = frame.fixups.val ++ [site] ⦄ := by
  cases kindEq : frame.kind
  all_goals try exact (forward kindEq).elim
  all_goals
    unfold runtime.compiler.control.FunctionCompiler.branch
    step as ⟨last, hlast⟩
    step as ⟨d, hd⟩
    step as ⟨actualIndex, hindex⟩
    have indexEq : actualIndex = index := by apply UScalar.eq_of_val_eq; simp [alloc.vec.Vec.len] at hlast; scalar_tac
    subst actualIndex
    have inBounds := (List.getElem?_eq_some_iff.mp lookup).1
    step as ⟨found, hfound⟩
    have foundEq : found = frame := by simpa [List.getElem?_eq_getElem inBounds, hfound] using lookup
    rw [foundEq]
    simp only [kindEq, bind_ok, Bool.false_eq_true, ite_false, ite_true]
    step as ⟨sum, hsum⟩
    cases sum with
    | none => simp at hsum; scalar_tac
    | some sum =>
      simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step as ⟨operand, hoperand⟩
      cases operand with
      | none => simp at hoperand; scalar_tac
      | some operand =>
        have sourceEq : operand = source := by apply UScalar.eq_of_val_eq; simp at hoperand; omega
        rw [sourceEq]
        simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
          Bool.false_eq_true, ite_false, ite_true]
        step with compiler_condition ops compiler condition conditionAt as ⟨selected, selectedEq⟩
        subst selected
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        have copyFalse : (if frame.results != 0#u32 then (Result.ok (source != frame.height) : Result Bool)
            else Result.ok false) = Result.ok false := by rcases elided with h | h <;> simp [h]
        rw [copyFalse]
        simp only [bind_ok, Bool.false_eq_true, ite_false, ite_true]
        step as ⟨current, back, hcurrent, hback⟩
        have currentEq : current = frame := by simpa [List.getElem?_eq_getElem inBounds, hcurrent] using lookup
        rw [currentEq]
        simp only [kindEq, bind_ok, uncurry_apply_pair, Bool.false_eq_true, ite_false, ite_true]
        step with budget_push ops law compiler.budget frame.fixups (alloc.vec.Vec.len compiler.function.code) fixupsFit
          as ⟨result, budget, fixups, pushed⟩
        rcases pushed with ⟨rfl, rfl, appended⟩ | ⟨rfl, rfl, rejected⟩
        · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, uncurry_apply_pair,
            Bool.false_eq_true, ite_false, ite_true]
          have emit := compiler_emit ops law
            { compiler with frames := back { frame with end_reachable := true, fixups } }
            (.JumpIfNonZero condition core.num.U32.MAX) codeFits offsetsFit coordinateFits
          simp only [kindEq] at emit
          step with emit
            as ⟨result, afterJump, emitted⟩
          cases result with
          | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          | Ok value =>
            cases value
            simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, WP.spec_ok]
            intro accepted
            obtain ⟨budget, code, offsets, exactState, finalCode, finalOffsets⟩ := emitted rfl
            refine ⟨?_, fixups, alloc.vec.Vec.len compiler.function.code, ?_, ?_, appended⟩
            · simpa [exactState] using finalCode
            · simp [alloc.vec.Vec.len]
            · simp [exactState, hback, alloc.vec.Vec.set_val_eq, kindEq]
        · simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

@[step] theorem branch_if_elided_loop {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source condition : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (kind : frame.kind = .Loop) (elided : frame.params = 0#u32 ∨ source = frame.height)
    (sourcePosition : source.val + frame.params.val + 1 = compiler.height.val)
    (conditionAt : compiler.before.val[compiler.before.val.length - 1]? = some condition)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (offsetsFit : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.control.FunctionCompiler.branch ops compiler depth 1#u32 true ⦃ out =>
      out.1 = .Ok () →
        out.2.function.code.val = compiler.function.code.val ++
          [.JumpIfNonZero condition frame.start_pc] ∧
        out.2.frames = compiler.frames ⦄ := by
  unfold runtime.compiler.control.FunctionCompiler.branch
  step as ⟨last, hlast⟩
  step as ⟨d, hd⟩
  step as ⟨actualIndex, hindex⟩
  have indexEq : actualIndex = index := by apply UScalar.eq_of_val_eq; simp [alloc.vec.Vec.len] at hlast; scalar_tac
  subst actualIndex
  have inBounds := (List.getElem?_eq_some_iff.mp lookup).1
  step as ⟨found, hfound⟩
  have foundEq : found = frame := by simpa [List.getElem?_eq_getElem inBounds, hfound] using lookup
  rw [foundEq]
  simp only [kind, bind_ok, Bool.false_eq_true, ite_false, ite_true]
  step as ⟨sum, hsum⟩
  cases sum with
  | none => simp at hsum; scalar_tac
  | some sum =>
    simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step as ⟨operand, hoperand⟩
    cases operand with
    | none => simp at hoperand; scalar_tac
    | some operand =>
      have sourceEq : operand = source := by apply UScalar.eq_of_val_eq; simp at hoperand; omega
      rw [sourceEq]
      simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        Bool.false_eq_true, ite_false, ite_true]
      step with compiler_condition ops compiler condition conditionAt as ⟨selected, selectedEq⟩
      subst selected
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      have copyFalse : (if frame.params != 0#u32 then (Result.ok (source != frame.height) : Result Bool)
          else Result.ok false) = Result.ok false := by rcases elided with h | h <;> simp [h]
      rw [copyFalse]
      simp only [bind_ok, Bool.false_eq_true, ite_false, ite_true]
      step as ⟨current, back, hcurrent, hback⟩
      have currentEq : current = frame := by simpa [List.getElem?_eq_getElem inBounds, hcurrent] using lookup
      rw [currentEq]
      simp only [kind, bind_ok, uncurry_apply_pair, Bool.false_eq_true, ite_false, ite_true]
      step with compiler_emit ops law
        { compiler with frames := back { frame with kind := .Loop } }
        (.JumpIfNonZero condition frame.start_pc) codeFits offsetsFit coordinateFits
        as ⟨result, afterJump, emitted⟩
      cases result with
      | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok value =>
        cases value
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, WP.spec_ok]
        intro accepted
        obtain ⟨budget, code, offsets, exactState, finalCode, finalOffsets⟩ := emitted rfl
        refine ⟨?_, ?_⟩
        · simpa [exactState] using finalCode
        · simp [exactState, hback]
          apply alloc.vec.Vec.ext
          simp only [alloc.vec.Vec.set_val_eq]
          have atIndex := (List.getElem?_eq_some_iff.mp lookup).2
          simpa only [← kind, ← atIndex] using List.set_getElem_self inBounds

end Itasca.Runtime.Code
