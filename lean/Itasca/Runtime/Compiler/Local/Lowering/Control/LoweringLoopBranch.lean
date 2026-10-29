import Itasca.Runtime.Compiler.Local.Lowering.Emission.Copy
import Itasca.Runtime.Compiler.Local.Relations.Control.BranchCertificates
import Itasca.Runtime.Compiler.Local.Initializer.InitializerExpression
import Itasca.Runtime.Compiler.Local.Callbacks.Observation.Observe
/-! Exact backward loop-branch emission for arbitrary label depth, including
zero-arity and identity-copy elision. Loop targets are already resolved and
construct a source branch certificate without a forward-fixup assumption. -/
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096 in
@[step] theorem branch_transfer_loop {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (kind : frame.kind = .Loop) (nonempty : frame.params ≠ 0#u32)
    (different : source ≠ frame.height)
    (sourcePosition : source.val + frame.params.val = compiler.height.val)
    (codeFits : compiler.function.code.val.length + 2 ≤ Usize.max)
    (offsetsFit : compiler.function.source_offsets.val.length + 2 ≤ Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.control.FunctionCompiler.branch ops compiler depth 0#u32 false ⦃ out =>
      out.1 = .Ok () →
        out.2.function.code.val = compiler.function.code.val ++
          [transferInstruction frame.height source frame.params, .Jump frame.start_pc] ∧
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
    have sumEq : sum = frame.params := by
      apply UScalar.eq_of_val_eq
      simpa only [Nat.zero_add] using hsum.2.1
    rw [sumEq]
    simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step as ⟨operand, hoperand⟩
    cases operand with
    | none => simp at hoperand; scalar_tac
    | some operand =>
      have sourceEq : operand = source := by apply UScalar.eq_of_val_eq; simp at hoperand; omega
      rw [sourceEq]
      simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        Bool.false_eq_true, ite_false, bne_iff_ne, nonempty, different, ite_true]
      rw [if_pos nonempty]
      simp only [bind_ok, bne_iff_ne, if_pos different]
      step with compiler_copy ops law compiler frame.height source frame.params nonempty different
        (by omega) (by omega) coordinateFits as ⟨copied, afterCopy, emitted⟩
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
        simp only [kind, bind_ok, uncurry_apply_pair, Bool.false_eq_true, ite_false, ite_true]
        have copyCodeFits : copyCode.val.length < Usize.max := by simp [copiedCode]; omega
        have copyOffsetsFits : copyOffsets.val.length < Usize.max := by
          have lengths := congrArg List.length copiedOffsets
          simp only [List.length_map, List.length_append, List.length_singleton] at lengths
          omega
        step with compiler_emit ops law
          { compiler with budget := copyBudget, function := { compiler.function with code := copyCode, source_offsets := copyOffsets }, frames := back { frame with kind := .Loop } }
          (.Jump frame.start_pc) copyCodeFits copyOffsetsFits coordinateFits
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
          · simpa [exactState, copiedCode, List.append_assoc] using finalCode
          · simp [exactState, hback, alloc.vec.Vec.set_val_eq, kind]
            apply alloc.vec.Vec.ext
            simp only [alloc.vec.Vec.set_val_eq]
            have atIndex := (List.getElem?_eq_some_iff.mp lookup).2
            simpa only [← kind, ← atIndex] using List.set_getElem_self inBounds
set_option maxRecDepth 4096 in
@[step] theorem branch_elided_loop {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (kind : frame.kind = .Loop) (elided : frame.params = 0#u32 ∨ source = frame.height)
    (sourcePosition : source.val + frame.params.val = compiler.height.val)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (offsetsFit : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.control.FunctionCompiler.branch ops compiler depth 0#u32 false ⦃ out =>
      out.1 = .Ok () →
        out.2.function.code.val = compiler.function.code.val ++
          [.Jump frame.start_pc] ∧
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
    have sumEq : sum = frame.params := by
      apply UScalar.eq_of_val_eq
      simpa only [Nat.zero_add] using hsum.2.1
    rw [sumEq]
    simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step as ⟨operand, hoperand⟩
    cases operand with
    | none => simp at hoperand; scalar_tac
    | some operand =>
      have sourceEq : operand = source := by apply UScalar.eq_of_val_eq; simp at hoperand; omega
      rw [sourceEq]
      simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        Bool.false_eq_true, ite_false]
      have copyFalse : (if frame.params != 0#u32 then (Result.ok (source != frame.height) : Result Bool)
          else Result.ok false) = Result.ok false := by rcases elided with h | h <;> simp [h]
      rw [copyFalse]
      simp only [bind_ok, Bool.false_eq_true, ite_false]
      step as ⟨current, back, hcurrent, hback⟩
      have currentEq : current = frame := by simpa [List.getElem?_eq_getElem inBounds, hcurrent] using lookup
      rw [currentEq]
      simp only [kind, bind_ok, uncurry_apply_pair, Bool.false_eq_true, ite_false, ite_true]
      step with compiler_emit ops law
        { compiler with frames := back { frame with kind := .Loop } }
        (.Jump frame.start_pc) codeFits offsetsFit coordinateFits
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

@[step] theorem compiler_branch_loop {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (kind : frame.kind = .Loop)
    (sourcePosition : source.val + frame.params.val = compiler.height.val)
    (codeFits : compiler.function.code.val.length + 2 ≤ Usize.max)
    (offsetsFit : compiler.function.source_offsets.val.length + 2 ≤ Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.control.FunctionCompiler.branch ops compiler depth 0#u32 false ⦃ out =>
      out.1 = .Ok () →
        out.2.function.code.val = compiler.function.code.val ++
          branchInstructions frame.height source frame.params frame.start_pc ∧
        out.2.frames = compiler.frames ⦄ := by
  by_cases elided : frame.params = 0#u32 ∨ source = frame.height
  · apply WP.spec_mono (branch_elided_loop ops law compiler frame index depth source lookup
      position kind elided sourcePosition (by omega) (by omega) coordinateFits)
    intro out effect accepted
    simpa [branchInstructions, elided] using effect accepted
  · have nonempty : frame.params ≠ 0#u32 := fun eq => elided (Or.inl eq)
    have different : source ≠ frame.height := fun eq => elided (Or.inr eq)
    apply WP.spec_mono (branch_transfer_loop ops law compiler frame index depth source lookup
      position kind nonempty different sourcePosition codeFits offsetsFit coordinateFits)
    intro out effect accepted
    simpa [branchInstructions, elided] using effect accepted

end Itasca.Runtime.Compiler
