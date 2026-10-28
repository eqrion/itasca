import Exec.Code.Local.Lowering.Control.LoweringBranchIf
import Exec.Code.Local.Callbacks.Control.CloseBlock
/-! Exact conditional branches with nonempty slot transfers. The guard skips
the copy and jump on false; the final patch fixes its exact resume address. -/
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
@[step] theorem branch_if_transfer_forward {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source condition resume : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (forward : frame.kind ≠ .Loop) (nonempty : frame.results ≠ 0#u32)
    (different : source ≠ frame.height)
    (sourcePosition : source.val + frame.results.val + 1 = compiler.height.val)
    (conditionAt : compiler.before.val[compiler.before.val.length - 1]? = some condition)
    (resumePosition : resume.val = compiler.function.code.val.length + 3)
    (fixupsFit : frame.fixups.val.length < Usize.max)
    (codeFits : compiler.function.code.val.length + 3 ≤ Usize.max)
    (offsetsFit : compiler.function.source_offsets.val.length + 3 ≤ Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.control.FunctionCompiler.branch ops compiler depth 1#u32 true ⦃ out =>
      out.1 = .Ok () →
        out.2.function.code.val = compiler.function.code.val ++
          [.JumpIfZero condition resume, transferInstruction frame.height source frame.results, .Jump core.num.U32.MAX] ∧
        ∃ fixups site, site.val = compiler.function.code.val.length + 2 ∧
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
    simp only [kindEq, bind_ok, Bool.false_eq_true, ite_false]
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
        have copyTrue : (if frame.results != 0#u32 then (Result.ok (source != frame.height) : Result Bool)
            else Result.ok false) = Result.ok true := by simp [nonempty, different]
        rw [copyTrue]
        simp only [bind_ok, Bool.false_eq_true, ite_false, ite_true]
        step with compiler_emit ops law compiler (.JumpIfZero condition core.num.U32.MAX)
          (by omega) (by omega) coordinateFits as ⟨guardResult, guarded, guardEffect⟩
        cases guardResult with
        | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok value =>
          cases value
          obtain ⟨guardBudget, guardCode, guardOffsets, rfl, guardedCode, guardedOffsets⟩ := guardEffect rfl
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
          have guardCodeFits : guardCode.val.length < Usize.max := by simp [guardedCode]; omega
          have guardOffsetsFits : guardOffsets.val.length < Usize.max := by
            have lengths := congrArg List.length guardedOffsets
            simp only [List.length_map, List.length_append, List.length_singleton] at lengths
            omega
          step with compiler_copy ops law
            { compiler with budget := guardBudget, function := { compiler.function with code := guardCode, source_offsets := guardOffsets } }
            frame.height source frame.results nonempty different guardCodeFits guardOffsetsFits coordinateFits as ⟨copied, afterCopy, emitted⟩
          cases copied with
          | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          | Ok value =>
            cases value
            obtain ⟨copyBudget, copyCode, copyOffsets, rfl, copiedCode, copiedOffsets⟩ := emitted rfl
            simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
            step as ⟨current, back, hcurrent, hback⟩
            have currentEq : current = frame := by simpa [List.getElem?_eq_getElem inBounds, hcurrent] using lookup
            rw [currentEq]
            simp only [kindEq, bind_ok, uncurry_apply_pair, Bool.false_eq_true, ite_false]
            step with budget_push ops law copyBudget frame.fixups (alloc.vec.Vec.len copyCode) fixupsFit
              as ⟨result, budget, fixups, pushed⟩
            rcases pushed with ⟨rfl, rfl, appended⟩ | ⟨rfl, rfl, rejected⟩
            · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, uncurry_apply_pair,
                Bool.false_eq_true, ite_false]
              have copyCodeFits : copyCode.val.length < Usize.max := by simp [copiedCode, guardedCode]; omega
              have copyOffsetsFits : copyOffsets.val.length < Usize.max := by
                have lengths := congrArg List.length copiedOffsets
                have guardLengths := congrArg List.length guardedOffsets
                simp only [List.length_map, List.length_append, List.length_singleton] at lengths guardLengths
                omega
              have emit := compiler_emit ops law
                { compiler with budget := budget, function := { compiler.function with code := copyCode, source_offsets := copyOffsets }, frames := back { frame with end_reachable := true, fixups } }
                (.Jump core.num.U32.MAX) copyCodeFits copyOffsetsFits coordinateFits
              simp only [kindEq] at emit
              step with emit
                as ⟨result, afterJump, emitted⟩
              cases result with
              | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
              | Ok value =>
                cases value
                obtain ⟨budget, code, offsets, exactState, finalCode, finalOffsets⟩ := emitted rfl
                subst afterJump
                simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
                have resumeAt : resume.val = code.val.length := by simp [finalCode, copiedCode, guardedCode, resumePosition]
                rw [compiler_pc_eq ops _ resume resumeAt]
                simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
                have patch := compiler_patch ops
                  { compiler with budget := budget, function := { compiler.function with code := code, source_offsets := offsets }, frames := back { frame with end_reachable := true, fixups } }
                  (alloc.vec.Vec.len compiler.function.code)
                  (.zero condition) core.num.U32.MAX resume
                  (by simp [BranchKind.instruction, finalCode, copiedCode, guardedCode, alloc.vec.Vec.len])
                simp only [kindEq] at patch
                step with patch as ⟨patchedResult, patchedCompiler, patchedOk, patched⟩
                subst patchedResult
                simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, WP.spec_ok]
                intro accepted
                obtain ⟨patchedCode, rfl, patchCode⟩ := patched
                refine ⟨?_, fixups, alloc.vec.Vec.len copyCode, ?_, ?_, appended⟩
                · simp [patchCode, BranchKind.instruction, finalCode, copiedCode, guardedCode,
                    alloc.vec.Vec.len, List.append_assoc]
                · simp [alloc.vec.Vec.len, copiedCode, guardedCode]
                · simp [hback, alloc.vec.Vec.set_val_eq, kindEq]
            · simp [core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
@[step] theorem branch_if_transfer_loop {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source condition resume : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (kindEq : frame.kind = .Loop) (nonempty : frame.params ≠ 0#u32)
    (different : source ≠ frame.height)
    (sourcePosition : source.val + frame.params.val + 1 = compiler.height.val)
    (conditionAt : compiler.before.val[compiler.before.val.length - 1]? = some condition)
    (resumePosition : resume.val = compiler.function.code.val.length + 3)
    (codeFits : compiler.function.code.val.length + 3 ≤ Usize.max)
    (offsetsFit : compiler.function.source_offsets.val.length + 3 ≤ Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.control.FunctionCompiler.branch ops compiler depth 1#u32 true ⦃ out =>
      out.1 = .Ok () →
        out.2.function.code.val = compiler.function.code.val ++
          [.JumpIfZero condition resume, transferInstruction frame.height source frame.params, .Jump frame.start_pc] ∧
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
      have copyTrue : (if frame.params != 0#u32 then (Result.ok (source != frame.height) : Result Bool)
          else Result.ok false) = Result.ok true := by simp [nonempty, different]
      rw [copyTrue]
      simp only [bind_ok, Bool.false_eq_true, ite_false, ite_true]
      step with compiler_emit ops law compiler (.JumpIfZero condition core.num.U32.MAX)
        (by omega) (by omega) coordinateFits as ⟨guardResult, guarded, guardEffect⟩
      cases guardResult with
      | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok value =>
        cases value
        obtain ⟨guardBudget, guardCode, guardOffsets, rfl, guardedCode, guardedOffsets⟩ := guardEffect rfl
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        have guardCodeFits : guardCode.val.length < Usize.max := by simp [guardedCode]; omega
        have guardOffsetsFits : guardOffsets.val.length < Usize.max := by
          have lengths := congrArg List.length guardedOffsets
          simp only [List.length_map, List.length_append, List.length_singleton] at lengths
          omega
        step with compiler_copy ops law
          { compiler with budget := guardBudget, function := { compiler.function with code := guardCode, source_offsets := guardOffsets } }
          frame.height source frame.params nonempty different guardCodeFits guardOffsetsFits coordinateFits as ⟨copied, afterCopy, emitted⟩
        cases copied with
        | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok value =>
          cases value
          obtain ⟨copyBudget, copyCode, copyOffsets, rfl, copiedCode, copiedOffsets⟩ := emitted rfl
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
          step as ⟨current, back, hcurrent, hback⟩
          have currentEq : current = frame := by simpa [List.getElem?_eq_getElem inBounds, hcurrent] using lookup
          rw [currentEq]
          simp only [kindEq, bind_ok, uncurry_apply_pair, Bool.false_eq_true, ite_false, ite_true]
          have copyCodeFits : copyCode.val.length < Usize.max := by simp [copiedCode, guardedCode]; omega
          have copyOffsetsFits : copyOffsets.val.length < Usize.max := by
            have lengths := congrArg List.length copiedOffsets
            have guardLengths := congrArg List.length guardedOffsets
            simp only [List.length_map, List.length_append, List.length_singleton] at lengths guardLengths
            omega
          have emit := compiler_emit ops law
            { compiler with budget := copyBudget, function := { compiler.function with code := copyCode, source_offsets := copyOffsets }, frames := back { frame with kind := .Loop } }
            (.Jump frame.start_pc) copyCodeFits copyOffsetsFits coordinateFits
          simp only [kindEq] at emit
          step with emit
            as ⟨result, afterJump, emitted⟩
          cases result with
          | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          | Ok value =>
            cases value
            obtain ⟨budget, code, offsets, exactState, finalCode, finalOffsets⟩ := emitted rfl
            subst afterJump
            simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
            have resumeAt : resume.val = code.val.length := by simp [finalCode, copiedCode, guardedCode, resumePosition]
            rw [compiler_pc_eq ops _ resume resumeAt]
            simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
            have patch := compiler_patch ops
              { compiler with budget := budget, function := { compiler.function with code := code, source_offsets := offsets }, frames := back { frame with kind := .Loop } }
              (alloc.vec.Vec.len compiler.function.code)
              (.zero condition) core.num.U32.MAX resume
              (by simp [BranchKind.instruction, finalCode, copiedCode, guardedCode, alloc.vec.Vec.len])
            simp only [kindEq] at patch
            step with patch as ⟨patchedResult, patchedCompiler, patchedOk, patched⟩
            subst patchedResult
            simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, WP.spec_ok]
            intro accepted
            obtain ⟨patchedCode, rfl, patchCode⟩ := patched
            refine ⟨?_, ?_⟩
            · simp [patchCode, BranchKind.instruction, finalCode, copiedCode, guardedCode,
                alloc.vec.Vec.len, List.append_assoc]
            · simp only [hback]
              apply alloc.vec.Vec.ext
              simp only [alloc.vec.Vec.set_val_eq]
              have atIndex := (List.getElem?_eq_some_iff.mp lookup).2
              simpa only [← kindEq, ← atIndex] using List.set_getElem_self inBounds
end Itasca.Runtime.Code
