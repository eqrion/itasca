import Exec.Code.Local.Lowering.Common.Copy
import Exec.Code.Local.Lowering.Control.LoweringBranch
/-! Actual nonempty forward BR emission at arbitrary label depth. Successful
callbacks retain the exact transfer/jump pair and fixup hole consumed by END. -/
namespace Exec.Code
open Aeneas Aeneas.Std

set_option maxRecDepth 4096 in
@[step] theorem branch_transfer_block {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (kind : frame.kind = .Block) (nonempty : frame.results ≠ 0#u32)
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
  simp only [kind, bind_ok, Bool.false_eq_true, ite_false]
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
        simp only [kind, bind_ok, uncurry_apply_pair, Bool.false_eq_true, ite_false]
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
          step with compiler_emit ops law
            { compiler with budget := budget, function := { compiler.function with code := copyCode, source_offsets := copyOffsets }, frames := back { frame with kind := .Block, end_reachable := true, fixups } }
            (.Jump core.num.U32.MAX) copyCodeFits copyOffsetsFits coordinateFits
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
            · simp [exactState, hback, alloc.vec.Vec.set_val_eq, kind]
        · simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
@[step] theorem callback_branch_transfer_block {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (resultType : Itasca.signature.ResultType)
    (reachable : compiler.reachable = true)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (kind : frame.kind = .Block) (nonempty : frame.results ≠ 0#u32)
    (different : source ≠ frame.height)
    (sourcePosition : source.val + frame.results.val = compiler.height.val)
    (fixupsFit : frame.fixups.val.length < Usize.max)
    (codeFits : compiler.function.code.val.length + 2 ≤ Usize.max)
    (offsetsFit : compiler.function.source_offsets.val.length + 2 ≤ Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br ops compiler state depth resultType ⦃ out =>
      out.1 = .Ok () → out.2.reachable = false ∧
        out.2.function.code.val = compiler.function.code.val ++
          [transferInstruction frame.height source frame.results, .Jump core.num.U32.MAX] ∧
        ∃ fixups site, site.val = compiler.function.code.val.length + 1 ∧
          out.2.frames.val = compiler.frames.val.set index.val { frame with end_reachable := true, fixups } ∧
          fixups.val = frame.fixups.val ++ [site] ⦄ := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br
  rw [if_pos reachable]
  step with branch_transfer_block ops law compiler frame index depth source lookup position kind
    nonempty different sourcePosition fixupsFit codeFits offsetsFit coordinateFits
    as ⟨result, changed, effect⟩
  cases result with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok value =>
    cases value
    obtain ⟨code, fixups, site, siteAt, frames, appended⟩ := effect rfl
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with compiler_observe ops law { changed with reachable := false } state
      as ⟨out, observed, accepted⟩
    obtain ⟨hoff, hh, hl, hls, hlo, hr, hcode, hsources, hnext, hcap, hmono, hframes, hcontrols⟩ := observed accepted
    exact ⟨hr, by simpa [hcode] using code, fixups, site, siteAt, by simpa [hframes] using frames, appended⟩
@[step] theorem callback_branch_transfer_hole {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (resultType : Itasca.signature.ResultType)
    (reachable : compiler.reachable = true)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (kind : frame.kind = .Block) (nonempty : frame.results ≠ 0#u32)
    (different : source ≠ frame.height)
    (sourcePosition : source.val + frame.results.val = compiler.height.val)
    (fixupsFit : frame.fixups.val.length < Usize.max)
    (codeFits : compiler.function.code.val.length + 2 ≤ Usize.max)
    (offsetsFit : compiler.function.source_offsets.val.length + 2 ≤ Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br ops compiler state depth resultType ⦃ out =>
      out.1 = .Ok () → out.2.reachable = false ∧
        ∃ fixups,
          out.2.frames.val = compiler.frames.val.set index.val { frame with end_reachable := true, fixups } ∧
          BranchHole out.2.function.code.val fixups.val compiler.function.code.val.length
            frame.height source frame.results ⦄ := by
  apply WP.spec_mono (callback_branch_transfer_block ops law compiler state resultType reachable
    frame index depth source lookup position kind nonempty different sourcePosition fixupsFit
    codeFits offsetsFit coordinateFits)
  intro out post accepted
  obtain ⟨dead, code, fixups, site, position, frames, appended⟩ := post accepted
  refine ⟨dead, fixups, frames, ?_⟩
  simp only [BranchHole, nonempty, different, false_or, if_false]
  refine ⟨?_, site, ?_, position, ?_⟩
  · simp [code]
  · simp [appended]
  · simp [code, core.num.U32.MAX, U32.rMax]
end Exec.Code
