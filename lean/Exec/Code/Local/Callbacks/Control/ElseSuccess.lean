import Exec.Code.Local.Relations.Control.BranchSuccessEmit
import Exec.Code.Local.Callbacks.Control.EnterElse
import Exec.Code.Local.Initializer.InitializerMappings
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

/-- Successful ELSE emission records its skip without an external fixup-vector
capacity assumption; each append is recovered from the actual normal return. -/
theorem compiler_else_live_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (frame : runtime.compiler.Frame) (prior : List runtime.compiler.Frame)
    (guard : Usize) (condition target : U32)
    (frames : compiler.frames.val = prior ++ [frame])
    (reachable : compiler.reachable = true) (guardPc : frame.if_pc = some guard)
    (guardCode : compiler.function.code.val[guard.val]? = some (.JumpIfZero condition core.num.U32.MAX))
    (position : target.val = compiler.function.code.val.length + 1)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else ops compiler state bt = .ok (.Ok (), after)) :
    after.reachable = frame.entry_reachable ∧
    after.function.code.val = (compiler.function.code.val ++ [runtime.bytecode.Instr.Jump core.num.U32.MAX]).set guard.val
      (.JumpIfZero condition target) ∧
    ∃ fixups, fixups.val = frame.fixups.val ++ [alloc.vec.Vec.len compiler.function.code] ∧
      after.frames.val = prior ++ [{ frame with kind := .Else, if_pc := none, end_reachable := true, fixups }] := by
  have nonempty : compiler.frames.val.isEmpty = false := by simp [frames]
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else at accepted
  simp only [alloc.vec.Vec.is_empty, bind_ok, nonempty, Bool.false_eq_true, ite_false] at accepted
  obtain ⟨index, indexCall, rest⟩ := bind_ok_inv _ _ _ accepted
  have indexSpec : alloc.vec.Vec.len compiler.frames - 1#usize ⦃ out => out.val = prior.length ⦄ := by
    step as ⟨index, indexEq⟩
    simp [frames, alloc.vec.Vec.len] at indexEq
    omega
  rw [indexCall, WP.spec_ok] at indexSpec
  obtain ⟨⟨found, back⟩, foundCall, rest⟩ := bind_ok_inv _ _ _ rest
  have readSpec : alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice runtime.compiler.Frame)
      compiler.frames index ⦃ out => out.1 = frame ∧ ∀ replacement, (out.2 replacement).val = prior ++ [replacement] ⦄ := by
    have inBounds : index.val < compiler.frames.val.length := by simp [frames, indexSpec]
    step as ⟨out, foundEq, backEq⟩
    have same : out.1 = frame := by simpa [indexSpec, frames] using foundEq
    exact ⟨same, by intro replacement; simp [backEq, alloc.vec.Vec.set_val_eq, indexSpec, frames]⟩
  rw [foundCall, WP.spec_ok] at readSpec
  dsimp only at readSpec
  obtain ⟨foundEq, backEq⟩ := readSpec
  subst found
  simp only [uncurry_apply_pair, core.option.Option.take, guardPc, reachable, ite_true, Bool.or_true] at rest
  obtain ⟨⟨result, budget, fixups⟩, pushed, rest⟩ := bind_ok_inv _ _ _ rest
  cases result with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok value =>
    cases value
    obtain ⟨budgetEq, appended⟩ := budget_push_success ops law compiler.budget budget frame.fixups fixups
      (alloc.vec.Vec.len compiler.function.code) pushed
    subst budget
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
    obtain ⟨⟨result, emitted⟩, emitCall, rest⟩ := bind_ok_inv _ _ _ rest
    cases result with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
    | Ok value =>
      cases value
      have effect := compiler_emit_success ops law _ emitted (.Jump core.num.U32.MAX) emitCall
      obtain ⟨budget, code, offsets, emittedEq, codeAppend, offsetAppend⟩ := effect
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
      rw [compiler_pc_eq ops emitted target (by simpa [emittedEq, codeAppend] using position)] at rest
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
      have guardBound := (List.getElem?_eq_some_iff.mp guardCode).1
      have retained : emitted.function.code.val[guard.val]? = some (.JumpIfZero condition core.num.U32.MAX) := by
        simp only [emittedEq, codeAppend]
        rw [List.getElem?_append_left guardBound]
        exact guardCode
      obtain ⟨⟨status, patched⟩, patchCall, rest⟩ := bind_ok_inv _ _ _ rest
      have patchedEffect := compiler_patch ops emitted guard (.zero condition) core.num.U32.MAX target retained
      rw [patchCall, WP.spec_ok] at patchedEffect
      dsimp only at patchedEffect
      obtain ⟨rfl, newCode, patchedEq, codeSet⟩ := patchedEffect
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
      have observed := compiler_observe ops law patched state
      rw [rest, WP.spec_ok] at observed
      dsimp only at observed
      obtain ⟨hoff, hh, hl, hls, hlo, hr, hcode, hsources, hnext, hcap, hmono, hframes, hcontrols⟩ := observed rfl
      refine ⟨?_, ?_, fixups, appended, ?_⟩
      · simpa [patchedEq, emittedEq] using hr
      · simpa [hcode, patchedEq, emittedEq, codeAppend, BranchKind.instruction] using codeSet
      · simp [hframes, patchedEq, emittedEq, backEq]
end Itasca.Runtime.Code
