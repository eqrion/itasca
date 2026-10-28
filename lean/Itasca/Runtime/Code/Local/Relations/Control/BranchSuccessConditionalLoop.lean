import Itasca.Runtime.Code.Local.Relations.Control.BranchSuccessConditionalTransfer
import Itasca.Runtime.Code.Local.Relations.Control.BranchSuccessLoop
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096
theorem branch_if_elided_loop_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source condition : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (kindEq : frame.kind = .Loop) (elided : frame.params = 0#u32 ∨ source = frame.height)
    (sourcePosition : source.val + frame.params.val + 1 = compiler.height.val)
    (conditionAt : compiler.before.val[compiler.before.val.length - 1]? = some condition)
    (after : runtime.compiler.FunctionCompiler A)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops compiler depth 1#u32 true = .ok (.Ok (), after)) :
        after.function.code.val = compiler.function.code.val ++
          [.JumpIfNonZero condition frame.start_pc] ∧
        after.frames = compiler.frames := by
  unfold runtime.compiler.control.FunctionCompiler.branch at accepted
  obtain ⟨last, hlast, rest⟩ := bind_ok_inv _ _ _ accepted
  clear accepted
  obtain ⟨d, hd, rest⟩ := bind_ok_inv _ _ _ rest
  obtain ⟨actualIndex, hindex, rest⟩ := bind_ok_inv _ _ _ rest
  obtain ⟨found, hfound, rest⟩ := bind_ok_inv _ _ _ rest
  have indexSpec := branch_index compiler frame index depth lookup position
  simp only [hlast, hd, hindex, hfound, bind_ok, WP.spec_ok] at indexSpec
  have indexEq := (Prod.mk.inj indexSpec).1
  have foundEq := (Prod.mk.inj indexSpec).2
  subst actualIndex found
  have inBounds := (List.getElem?_eq_some_iff.mp lookup).1
  simp only [kindEq, bind_ok, Bool.false_eq_true, ite_false, ite_true] at rest
  have sumSpec : lift (U32.checked_add 1#u32 frame.params) ⦃ out => ∃ sum, out = some sum ∧ sum.val = 1 + frame.params.val ⦄ := by
    step as ⟨sum, hsum⟩
    cases sum with
    | none => simp at hsum; scalar_tac
    | some sum => exact ⟨sum, rfl, by simpa using hsum.2.1⟩
  obtain ⟨_, sumCall, sum, rfl, sumVal⟩ := WP.spec_imp_exists sumSpec
  rw [sumCall] at rest
  simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
  have sourceSpec : lift (U32.checked_sub compiler.height sum) ⦃ out => out = some source ⦄ := by
    step as ⟨operand, hoperand⟩
    cases operand with
    | none => simp at hoperand; scalar_tac
    | some operand => congr 1; apply UScalar.eq_of_val_eq; simp at hoperand; omega
  obtain ⟨_, sourceCall, rfl⟩ := WP.spec_imp_exists sourceSpec
  rw [sourceCall] at rest
  simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
    Bool.false_eq_true, ite_false, ite_true] at rest
  obtain ⟨_, conditionCall, rfl⟩ := WP.spec_imp_exists (compiler_condition ops compiler condition conditionAt)
  rw [conditionCall] at rest
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
  have copyFalse : (if frame.params != 0#u32 then (Result.ok (source != frame.height) : Result Bool)
      else Result.ok false) = Result.ok false := by rcases elided with h | h <;> simp [h]
  rw [copyFalse] at rest
  simp only [bind_ok, Bool.false_eq_true, ite_false, ite_true] at rest
  obtain ⟨⟨current, back⟩, read, rest⟩ := bind_ok_inv _ _ _ rest
  have readSpec : alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice runtime.compiler.Frame)
      compiler.frames index ⦃ out => out.1 = frame ∧ ∀ replacement, (out.2 replacement).val = compiler.frames.val.set index.val replacement ⦄ := by
    step as ⟨out, hcurrent, hback⟩
    have same : out.1 = frame := by simpa [List.getElem?_eq_getElem inBounds, hcurrent] using lookup
    exact ⟨same, by intro replacement; simp [hback, alloc.vec.Vec.set_val_eq]⟩
  rw [read, WP.spec_ok] at readSpec
  have currentEq := readSpec.1
  have hback := readSpec.2
  dsimp only at currentEq hback
  subst current
  simp only [kindEq, bind_ok, uncurry_apply_pair, Bool.false_eq_true, ite_false, ite_true] at rest
  obtain ⟨⟨result, afterJump⟩, emittedCall, rest⟩ := bind_ok_inv _ _ _ rest
  cases result with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok value =>
    cases value
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Bool.false_eq_true, ite_false, ite_true, Result.ok.injEq, Prod.mk.injEq] at rest
    obtain ⟨_, rfl⟩ := rest
    have emitted := compiler_emit_success ops law _ afterJump (.JumpIfNonZero condition frame.start_pc) emittedCall
    obtain ⟨finalBudget, code, offsets, exactState, finalCode, finalOffsets⟩ := emitted
    refine ⟨?_, ?_⟩
    · simpa [exactState] using finalCode
    · simp only [exactState]
      apply alloc.vec.Vec.ext
      rw [hback]
      have atIndex := (List.getElem?_eq_some_iff.mp lookup).2
      simpa only [← kindEq, ← atIndex] using List.set_getElem_self inBounds

theorem branch_if_transfer_loop_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source condition resume : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (kindEq : frame.kind = .Loop) (nonempty : frame.params ≠ 0#u32)
    (different : source ≠ frame.height)
    (sourcePosition : source.val + frame.params.val + 1 = compiler.height.val)
    (conditionAt : compiler.before.val[compiler.before.val.length - 1]? = some condition)
    (resumePosition : resume.val = compiler.function.code.val.length + 3)
    (after : runtime.compiler.FunctionCompiler A)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops compiler depth 1#u32 true = .ok (.Ok (), after)) :
        after.function.code.val = compiler.function.code.val ++
          [.JumpIfZero condition resume, transferInstruction frame.height source frame.params, .Jump frame.start_pc] ∧
        after.frames = compiler.frames := by
  unfold runtime.compiler.control.FunctionCompiler.branch at accepted
  obtain ⟨last, hlast, rest⟩ := bind_ok_inv _ _ _ accepted
  clear accepted
  obtain ⟨d, hd, rest⟩ := bind_ok_inv _ _ _ rest
  obtain ⟨actualIndex, hindex, rest⟩ := bind_ok_inv _ _ _ rest
  obtain ⟨found, hfound, rest⟩ := bind_ok_inv _ _ _ rest
  have indexSpec := branch_index compiler frame index depth lookup position
  simp only [hlast, hd, hindex, hfound, bind_ok, WP.spec_ok] at indexSpec
  have indexEq := (Prod.mk.inj indexSpec).1
  have foundEq := (Prod.mk.inj indexSpec).2
  subst actualIndex found
  have inBounds := (List.getElem?_eq_some_iff.mp lookup).1
  simp only [kindEq, bind_ok, Bool.false_eq_true, ite_false, ite_true] at rest
  have sumSpec : lift (U32.checked_add 1#u32 frame.params) ⦃ out => ∃ sum, out = some sum ∧ sum.val = 1 + frame.params.val ⦄ := by
    step as ⟨sum, hsum⟩
    cases sum with
    | none => simp at hsum; scalar_tac
    | some sum => exact ⟨sum, rfl, by simpa using hsum.2.1⟩
  obtain ⟨_, sumCall, sum, rfl, sumVal⟩ := WP.spec_imp_exists sumSpec
  rw [sumCall] at rest
  simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
  have sourceSpec : lift (U32.checked_sub compiler.height sum) ⦃ out => out = some source ⦄ := by
    step as ⟨operand, hoperand⟩
    cases operand with
    | none => simp at hoperand; scalar_tac
    | some operand => congr 1; apply UScalar.eq_of_val_eq; simp at hoperand; omega
  obtain ⟨_, sourceCall, rfl⟩ := WP.spec_imp_exists sourceSpec
  rw [sourceCall] at rest
  simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
    Bool.false_eq_true, ite_false, ite_true] at rest
  obtain ⟨_, conditionCall, rfl⟩ := WP.spec_imp_exists (compiler_condition ops compiler condition conditionAt)
  rw [conditionCall] at rest
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
  simp only [bne_iff_ne, if_pos nonempty, bind_ok, if_pos different, ite_true] at rest
  obtain ⟨⟨guardResult, guarded⟩, guardCall, rest⟩ := bind_ok_inv _ _ _ rest
  cases guardResult with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok value =>
    cases value
    obtain ⟨guardBudget, guardCode, guardOffsets, rfl, guardedCode, guardedOffsets⟩ :=
      compiler_emit_success ops law compiler guarded (.JumpIfZero condition core.num.U32.MAX) guardCall
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok, ite_true] at rest
    obtain ⟨⟨copied, afterCopy⟩, copiedCall, rest⟩ := bind_ok_inv _ _ _ rest
    cases copied with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
    | Ok value =>
      cases value
      obtain ⟨copyBudget, copyCode, copyOffsets, rfl, copiedCode, copiedOffsets⟩ :=
        compiler_copy_success ops law { compiler with budget := guardBudget, function := { compiler.function with code := guardCode, source_offsets := guardOffsets } } afterCopy frame.height source frame.params nonempty different copiedCall
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
      obtain ⟨⟨current, back⟩, read, rest⟩ := bind_ok_inv _ _ _ rest
      have readSpec : alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice runtime.compiler.Frame)
          compiler.frames index ⦃ out => out.1 = frame ∧ ∀ replacement, (out.2 replacement).val = compiler.frames.val.set index.val replacement ⦄ := by
        step as ⟨out, hcurrent, hback⟩
        have same : out.1 = frame := by simpa [List.getElem?_eq_getElem inBounds, hcurrent] using lookup
        exact ⟨same, by intro replacement; simp [hback, alloc.vec.Vec.set_val_eq]⟩
      rw [read, WP.spec_ok] at readSpec
      have currentEq := readSpec.1
      have hback := readSpec.2
      dsimp only at currentEq hback
      subst current
      simp only [kindEq, bind_ok, uncurry_apply_pair, Bool.false_eq_true, ite_false, ite_true] at rest
      obtain ⟨⟨result, afterJump⟩, emittedCall, rest⟩ := bind_ok_inv _ _ _ rest
      cases result with
      | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
      | Ok value =>
        cases value
        have emitted := compiler_emit_success ops law _ afterJump (.Jump frame.start_pc) emittedCall
        obtain ⟨finalBudget, code, offsets, exactState, finalCode, finalOffsets⟩ := emitted
        subst afterJump
        simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
        have resumeAt : resume.val = code.val.length := by simp [finalCode, copiedCode, guardedCode, resumePosition]
        rw [compiler_pc_eq ops _ resume resumeAt] at rest
        simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
        obtain ⟨⟨patchedResult, patchedCompiler⟩, patchCall, rest⟩ := bind_ok_inv _ _ _ rest
        have patch := compiler_patch ops
          { compiler with budget := finalBudget, function := { compiler.function with code := code, source_offsets := offsets }, frames := back { frame with kind := .Loop } }
          (alloc.vec.Vec.len compiler.function.code)
          (.zero condition) core.num.U32.MAX resume
          (by simp [BranchKind.instruction, finalCode, copiedCode, guardedCode, alloc.vec.Vec.len])
        simp only [kindEq] at patch
        rw [patchCall, WP.spec_ok] at patch
        obtain ⟨rfl, patchedCode, exactState, patchCode⟩ := patch
        dsimp only at exactState patchCode
        subst patchedCompiler
        simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Result.ok.injEq, Prod.mk.injEq] at rest
        obtain ⟨_, rfl⟩ := rest
        refine ⟨?_, ?_⟩
        · simp [patchCode, BranchKind.instruction, finalCode, copiedCode, guardedCode,
            alloc.vec.Vec.len, List.append_assoc]
        · apply alloc.vec.Vec.ext
          rw [hback]
          have atIndex := (List.getElem?_eq_some_iff.mp lookup).2
          simpa only [← kindEq, ← atIndex] using List.set_getElem_self inBounds

end Itasca.Runtime.Code
