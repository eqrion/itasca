import Itasca.Runtime.Compiler.Local.Lowering.Emission.Copy
import Itasca.Runtime.Compiler.Local.Relations.Control.BranchCertificates
import Itasca.Runtime.Compiler.Local.Initializer.InitializerElementAppend
import Itasca.Runtime.Compiler.Local.Callbacks.Observation.Frame
import Itasca.Runtime.Compiler.Local.Callbacks.Control.EnterIf
import Itasca.Runtime.Compiler.Local.Lowering.Emission.LoweringEmpty
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredLabels

/-!
Sections, each formerly its own module: LoweringForwardBranch, LoweringLoopBranch, LoweringBranchIf, LoweringConditionalTransfer, LoweringReturn, LoweringTrap.
-/

/-! ## LoweringForwardBranch -/

section

/-! Actual forward BR emission for every non-loop label kind and arbitrary
label depth. Covers all transfer widths and both copy-elision cases, retaining
typed branch holes and exact fixup-list extensions for the closing callback. -/
namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end

/-! ## LoweringLoopBranch -/

section

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

end

/-! ## LoweringBranchIf -/

section

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end

/-! ## LoweringConditionalTransfer -/

section

/-! Exact conditional branches with nonempty slot transfers. The guard skips
the copy and jump on false; the final patch fixes its exact resume address. -/
namespace Itasca.Runtime.Compiler
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
end Itasca.Runtime.Compiler

end

/-! ## LoweringReturn -/

section

/-! Actual RETURN callback emission and terminal structured source certificate. -/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

@[step] theorem callback_return {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (body : runtime.compiler.Frame) (source : U32)
    (reachable : compiler.reachable = true)
    (bodyFrame : compiler.frames.val[0]? = some body)
    (height : compiler.height.val = source.val + body.results.val)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return ops compiler state ⦃ out =>
      out.1 = .Ok () → out.2.reachable = false ∧
        out.2.function.code.val = compiler.function.code.val ++ [.Return source body.results] ∧
        out.2.frames = compiler.frames ∧ compilerLocals out.2 = compilerLocals compiler ⦄ := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return
  rw [if_pos reachable]
  have bound : 0 < compiler.frames.length := List.getElem?_eq_some_iff.mp bodyFrame |>.1
  step as ⟨frame, hframe⟩
  have same : frame = body := hframe.trans (List.getElem?_eq_some_iff.mp bodyFrame).2
  rw [same]
  step as ⟨value, hvalue⟩
  cases value with
  | none => simp only at hvalue; omega
  | some word =>
    have valueEq : word = source := by apply UScalar.eq_of_val_eq; simp only at hvalue; omega
    rw [valueEq]
    simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with compiler_emit ops law compiler (.Return source body.results) codeFits sourceFits coordinateFits
      as ⟨result, emitted, emission⟩
    cases result with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok value =>
      cases value
      obtain ⟨budget, code, sources, exactState, codeAppended, sourceAppended⟩ := emission rfl
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step with compiler_observe ops law { emitted with reachable := false } state as ⟨out, observed, accepted⟩
      obtain ⟨hoff, hh, hl, hls, hlo, hr, hcode, hsources, hnext, hcap, hmono, hframes, hcontrols⟩ := observed accepted
      refine ⟨hr, ?_, ?_, ?_⟩
      · simpa [hcode, exactState] using codeAppended
      · simpa [exactState] using hframes
      · simp [compilerLocals, hl, exactState]

end Itasca.Runtime.Compiler

end

/-! ## LoweringTrap -/

section

/-!
Compilation of an unreachable instruction.

Main declarations: `callback_unreachable`. A direct consumer is `Compiler.Local.Checking.TerminalInstructionPrefix`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

@[step] theorem callback_unreachable {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (reachable : compiler.reachable = true)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable ops compiler state ⦃ out =>
      out.1 = .Ok () → out.2.reachable = false ∧
        out.2.function.code.val = compiler.function.code.val ++ [.Unreachable] ∧
        out.2.frames = compiler.frames ∧ out.2.function.locals = compiler.function.locals ⦄ := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable
  rw [if_pos reachable]
  step with compiler_emit ops law compiler .Unreachable codeFits sourceFits coordinateFits
    as ⟨result, changed, emitted⟩
  cases result with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok value =>
    cases value
    obtain ⟨budget, code, sources, exactState, appended, sourceAppended⟩ := emitted rfl
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with compiler_observe ops law { changed with reachable := false } state
      as ⟨out, observed, accepted⟩
    obtain ⟨hoff, hh, hl, hls, hlo, hr, hcode, hsources, hnext, hcap, hmono, hframes, hcontrols⟩ := observed accepted
    refine ⟨hr, ?_, ?_, ?_⟩
    · simpa [exactState, hcode] using appended
    · simpa [exactState] using hframes
    · simpa [exactState] using hl

end Itasca.Runtime.Compiler

end
