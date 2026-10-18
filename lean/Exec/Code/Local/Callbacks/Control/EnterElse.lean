import Exec.Code.Local.Callbacks.Control.EnterIf
import Exec.Code.Local.Relations.Control.BranchCertificates
/-! The actual ELSE callback preserves source control metadata, records the
then-arm skip when needed, and retargets the original condition to the start
of the else arm. Unentered and non-fallthrough arms are handled explicitly. -/
namespace Exec.Code
open Aeneas Aeneas.Std

@[step] theorem compiler_else_live {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (frame : runtime.compiler.Frame) (prior : List runtime.compiler.Frame)
    (guard : Usize) (condition target : U32)
    (frames : compiler.frames.val = prior ++ [frame])
    (reachable : compiler.reachable = true) (guardPc : frame.if_pc = some guard)
    (guardCode : compiler.function.code.val[guard.val]? = some (.JumpIfZero condition core.num.U32.MAX))
    (position : target.val = compiler.function.code.val.length + 1)
    (fixupsFit : frame.fixups.val.length < Usize.max)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (offsetsFit : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else ops compiler state bt ⦃ out =>
      out.1 = .Ok () → out.2.reachable = frame.entry_reachable ∧
        out.2.function.code.val = (compiler.function.code.val ++ [runtime.bytecode.Instr.Jump core.num.U32.MAX]).set guard.val
          (.JumpIfZero condition target) ∧
        ∃ fixups, fixups.val = frame.fixups.val ++ [alloc.vec.Vec.len compiler.function.code] ∧
          out.2.frames.val = prior ++ [{ frame with kind := .Else, if_pc := none, end_reachable := true, fixups }] ⦄ := by
  have nonempty : compiler.frames.val.isEmpty = false := by simp [frames]
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else
  simp only [alloc.vec.Vec.is_empty, bind_ok, nonempty, Bool.false_eq_true, ite_false]
  step as ⟨index, indexEq⟩
  have atLast : index.val = prior.length := by simp [frames, alloc.vec.Vec.len] at indexEq; omega
  step as ⟨found, back, foundEq, backEq⟩
  have same : found = frame := by simpa [atLast, frames] using foundEq
  rw [same]
  simp only [core.option.Option.take, guardPc, reachable, ite_true, Bool.or_true]
  step with budget_push ops law compiler.budget frame.fixups (alloc.vec.Vec.len compiler.function.code)
    fixupsFit as ⟨result, budget, fixups, pushed⟩
  rcases pushed with ⟨rfl, rfl, appended⟩ | ⟨rfl, rfl, rejected⟩
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with compiler_emit ops law
      { compiler with frames := back { frame with kind := .Else, if_pc := none, end_reachable := true, fixups }, reachable := frame.entry_reachable }
      (.Jump core.num.U32.MAX) codeFits offsetsFit coordinateFits as ⟨result, emitted, effect⟩
    cases result with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok value =>
      cases value
      obtain ⟨budget, code, offsets, emittedEq, codeAppend, offsetAppend⟩ := effect rfl
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      rw [compiler_pc_eq ops emitted target (by simpa [emittedEq, codeAppend] using position)]
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      have guardBound := (List.getElem?_eq_some_iff.mp guardCode).1
      have retained : emitted.function.code.val[guard.val]? = some (.JumpIfZero condition core.num.U32.MAX) := by
        simp only [emittedEq, codeAppend]
        rw [List.getElem?_append_left guardBound]
        exact guardCode
      step with compiler_patch ops emitted guard (.zero condition) core.num.U32.MAX target retained
        as ⟨status, patched, statusEq, patchedEffect⟩
      subst status
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      obtain ⟨newCode, patchedEq, codeSet⟩ := patchedEffect
      step with compiler_observe ops law patched state as ⟨out, observed, accepted⟩
      obtain ⟨hoff, hh, hl, hls, hlo, hr, hcode, hsources, hnext, hcap, hmono, hframes, hcontrols⟩ := observed accepted
      refine ⟨?_, ?_, fixups, appended, ?_⟩
      · simpa [patchedEq, emittedEq] using hr
      · simpa [hcode, patchedEq, emittedEq, codeAppend, BranchKind.instruction] using codeSet
      · simp [hframes, patchedEq, emittedEq, backEq, alloc.vec.Vec.set_val_eq, atLast, frames]
  · simp [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- When the then arm does not fall through, ELSE emits no skip instruction;
it still retargets the initial conditional guard and restores entry reachability. -/
@[step] theorem compiler_else_dead {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (frame : runtime.compiler.Frame) (prior : List runtime.compiler.Frame)
    (guard : Usize) (condition target : U32)
    (frames : compiler.frames.val = prior ++ [frame])
    (reachable : compiler.reachable = false) (guardPc : frame.if_pc = some guard)
    (guardCode : compiler.function.code.val[guard.val]? = some (.JumpIfZero condition core.num.U32.MAX))
    (position : target.val = compiler.function.code.val.length) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else ops compiler state bt ⦃ out =>
      out.1 = .Ok () → out.2.reachable = frame.entry_reachable ∧
        out.2.function.code.val = compiler.function.code.val.set guard.val (.JumpIfZero condition target) ∧
        out.2.frames.val = prior ++ [{ frame with kind := .Else, if_pc := none }] ⦄ := by
  have nonempty : compiler.frames.val.isEmpty = false := by simp [frames]
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else
  simp only [alloc.vec.Vec.is_empty, bind_ok, nonempty, Bool.false_eq_true, ite_false]
  step as ⟨index, indexEq⟩
  have atLast : index.val = prior.length := by simp [frames, alloc.vec.Vec.len] at indexEq; omega
  step as ⟨found, back, foundEq, backEq⟩
  have same : found = frame := by simpa [atLast, frames] using foundEq
  rw [same]
  simp only [core.option.Option.take, guardPc, reachable, Bool.false_eq_true, ite_false, Bool.or_false]
  let updated := { compiler with frames := back { frame with kind := .Else, if_pc := none }, reachable := frame.entry_reachable }
  rw [compiler_pc_eq ops updated target position]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  step with compiler_patch ops updated guard (.zero condition) core.num.U32.MAX target guardCode
    as ⟨status, patched, statusEq, patchedEffect⟩
  subst status
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  obtain ⟨newCode, patchedEq, codeSet⟩ := patchedEffect
  step with compiler_observe ops law patched state as ⟨out, observed, accepted⟩
  obtain ⟨hoff, hh, hl, hls, hlo, hr, hcode, hsources, hnext, hcap, hmono, hframes, hcontrols⟩ := observed accepted
  refine ⟨?_, ?_, ?_⟩
  · simpa [patchedEq, updated] using hr
  · simpa [hcode, patchedEq, updated, BranchKind.instruction] using codeSet
  · simp [hframes, patchedEq, updated, backEq, alloc.vec.Vec.set_val_eq, atLast, frames]

@[step] theorem compiler_else_unentered {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (frame : runtime.compiler.Frame) (prior : List runtime.compiler.Frame)
    (frames : compiler.frames.val = prior ++ [frame])
    (reachable : compiler.reachable = false) (guardPc : frame.if_pc = none) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else ops compiler state bt ⦃ out =>
      out.1 = .Ok () → out.2.reachable = frame.entry_reachable ∧
        out.2.function.code = compiler.function.code ∧
        out.2.frames.val = prior ++ [{ frame with kind := .Else, if_pc := none }] ⦄ := by
  have nonempty : compiler.frames.val.isEmpty = false := by simp [frames]
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else
  simp only [alloc.vec.Vec.is_empty, bind_ok, nonempty, Bool.false_eq_true, ite_false]
  step as ⟨index, indexEq⟩
  have atLast : index.val = prior.length := by simp [frames, alloc.vec.Vec.len] at indexEq; omega
  step as ⟨found, back, foundEq, backEq⟩
  have same : found = frame := by simpa [atLast, frames] using foundEq
  rw [same]
  simp only [core.option.Option.take, guardPc, reachable, Bool.false_eq_true, ite_false, Bool.or_false]
  step with compiler_observe ops law _ state as ⟨out, observed, accepted⟩
  obtain ⟨hoff, hh, hl, hls, hlo, hr, hcode, hsources, hnext, hcap, hmono, hframes, hcontrols⟩ := observed accepted
  refine ⟨hr, hcode, ?_⟩
  simp [hframes, backEq, alloc.vec.Vec.set_val_eq, atLast, frames]
end Exec.Code
