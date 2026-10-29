import Itasca.Runtime.Compiler.Local.Lowering.Emission.Copy
import Itasca.Runtime.Compiler.Local.Relations.Control.BranchCertificates
import Itasca.Runtime.Compiler.Local.Initializer.InitializerExpression
import Itasca.Runtime.Compiler.Local.Callbacks.Observation.Observe
/-! Actual forward BR emission for every non-loop label kind and arbitrary
label depth. Covers all transfer widths and both copy-elision cases, retaining
typed branch holes and exact fixup-list extensions for the closing callback. -/
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
@[step] theorem branch_transfer_forward {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (forward : frame.kind ≠ .Loop) (nonempty : frame.results ≠ 0#u32)
    (different : source ≠ frame.height)
    (sourcePosition : source.val + frame.results.val = compiler.height.val)
    (fixupsFit : frame.fixups.val.length < Usize.max)
    (codeFits : compiler.function.code.val.length + 2 ≤ Usize.max)
    (offsetsFit : compiler.function.source_offsets.val.length + 2 ≤ Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.control.FunctionCompiler.branch ops compiler depth 0#u32 false ⦃ out =>
      out.1 = .Ok () →
        out.2.function.code.val = compiler.function.code.val ++
          [transferInstruction frame.height source frame.results, .Jump core.num.U32.MAX] ∧
        ∃ fixups site, site.val = compiler.function.code.val.length + 1 ∧
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
      have sumEq : sum = frame.results := by
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
        step with compiler_copy ops law compiler frame.height source frame.results nonempty different
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
          simp only [kindEq, bind_ok, uncurry_apply_pair, Bool.false_eq_true, ite_false]
          step with budget_push ops law copyBudget frame.fixups (alloc.vec.Vec.len copyCode) fixupsFit
            as ⟨result, budget, fixups, pushed⟩
          rcases pushed with ⟨rfl, rfl, appended⟩ | ⟨rfl, rfl, rejected⟩
          · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, uncurry_apply_pair,
              Bool.false_eq_true, ite_false]
            have copyCodeFits : copyCode.val.length < Usize.max := by simp [copiedCode]; omega
            have copyOffsetsFits : copyOffsets.val.length < Usize.max := by
              have lengths := congrArg List.length copiedOffsets
              simp only [List.length_map, List.length_append, List.length_singleton] at lengths
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
              simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, WP.spec_ok]
              intro accepted
              obtain ⟨budget, code, offsets, exactState, finalCode, finalOffsets⟩ := emitted rfl
              refine ⟨?_, fixups, alloc.vec.Vec.len copyCode, ?_, ?_, appended⟩
              · simpa [exactState, copiedCode, List.append_assoc] using finalCode
              · simp [alloc.vec.Vec.len, copiedCode]
              · simp [exactState, hback, alloc.vec.Vec.set_val_eq, kindEq]
          · simp [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
@[step] theorem branch_elided_forward {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (forward : frame.kind ≠ .Loop) (elided : frame.results = 0#u32 ∨ source = frame.height)
    (sourcePosition : source.val + frame.results.val = compiler.height.val)
    (fixupsFit : frame.fixups.val.length < Usize.max)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (offsetsFit : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.control.FunctionCompiler.branch ops compiler depth 0#u32 false ⦃ out =>
      out.1 = .Ok () →
        out.2.function.code.val = compiler.function.code.val ++
          [.Jump core.num.U32.MAX] ∧
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
    simp only [kindEq, bind_ok, Bool.false_eq_true, ite_false]
    step as ⟨sum, hsum⟩
    cases sum with
    | none => simp at hsum; scalar_tac
    | some sum =>
      have sumEq : sum = frame.results := by
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
        have copyFalse : (if frame.results != 0#u32 then (Result.ok (source != frame.height) : Result Bool)
            else Result.ok false) = Result.ok false := by rcases elided with h | h <;> simp [h]
        rw [copyFalse]
        simp only [bind_ok, Bool.false_eq_true, ite_false]
        step as ⟨current, back, hcurrent, hback⟩
        have currentEq : current = frame := by simpa [List.getElem?_eq_getElem inBounds, hcurrent] using lookup
        rw [currentEq]
        simp only [kindEq, bind_ok, uncurry_apply_pair, Bool.false_eq_true, ite_false]
        step with budget_push ops law compiler.budget frame.fixups (alloc.vec.Vec.len compiler.function.code) fixupsFit
          as ⟨result, budget, fixups, pushed⟩
        rcases pushed with ⟨rfl, rfl, appended⟩ | ⟨rfl, rfl, rejected⟩
        · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, uncurry_apply_pair,
            Bool.false_eq_true, ite_false]
          have emit := compiler_emit ops law
            { compiler with frames := back { frame with end_reachable := true, fixups } }
            (.Jump core.num.U32.MAX) codeFits offsetsFit coordinateFits
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

@[step] theorem compiler_branch_forward {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (forward : frame.kind ≠ .Loop)
    (sourcePosition : source.val + frame.results.val = compiler.height.val)
    (fixupsFit : frame.fixups.val.length < Usize.max)
    (codeFits : compiler.function.code.val.length + 2 ≤ Usize.max)
    (offsetsFit : compiler.function.source_offsets.val.length + 2 ≤ Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.control.FunctionCompiler.branch ops compiler depth 0#u32 false ⦃ out =>
      out.1 = .Ok () → ∃ fixups,
        out.2.frames.val = compiler.frames.val.set index.val { frame with end_reachable := true, fixups } ∧
        BranchHole out.2.function.code.val fixups.val compiler.function.code.val.length
          frame.height source frame.results ∧
        out.2.function.code.val = compiler.function.code.val ++
          branchInstructions frame.height source frame.results core.num.U32.MAX ∧
        ∃ site, site.val = compiler.function.code.val.length +
          (if frame.results = 0#u32 ∨ source = frame.height then 0 else 1) ∧
          fixups.val = frame.fixups.val ++ [site] ⦄ := by
  by_cases elided : frame.results = 0#u32 ∨ source = frame.height
  · apply WP.spec_mono (branch_elided_forward ops law compiler frame index depth source lookup
      position forward elided sourcePosition fixupsFit (by omega) (by omega) coordinateFits)
    intro out effect accepted
    obtain ⟨code, fixups, site, position, frames, appended⟩ := effect accepted
    refine ⟨fixups, frames, ?_, ?_, ?_⟩
    · simp only [BranchHole, if_pos elided]
      exact ⟨site, by simp [appended], position, by simp [code, core.num.U32.MAX, U32.rMax]⟩
    · simpa [branchInstructions, elided] using code
    · exact ⟨site, by simpa [elided] using position, appended⟩
  · have nonempty : frame.results ≠ 0#u32 := fun eq => elided (Or.inl eq)
    have different : source ≠ frame.height := fun eq => elided (Or.inr eq)
    apply WP.spec_mono (branch_transfer_forward ops law compiler frame index depth source lookup
      position forward nonempty different sourcePosition fixupsFit codeFits offsetsFit coordinateFits)
    intro out effect accepted
    obtain ⟨code, fixups, site, position, frames, appended⟩ := effect accepted
    refine ⟨fixups, frames, ?_, ?_, ?_⟩
    · simp only [BranchHole, if_neg elided]
      exact ⟨by simp [code], site, by simp [appended], position, by simp [code, core.num.U32.MAX, U32.rMax]⟩
    · simpa [branchInstructions, elided] using code
    · exact ⟨site, by simpa [elided] using position, appended⟩

end Itasca.Runtime.Code
