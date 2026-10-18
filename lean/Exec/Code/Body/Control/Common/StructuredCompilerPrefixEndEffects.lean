import Exec.Code.Body.Control.Control.StructuredCompilerPrefixCloseBlock
import Exec.Code.Local.Callbacks.Control.CloseGuardedScope
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Successful END exposes its actual frame removal and fixup effects from
retained scope geometry, without an assumed code transformation. -/
theorem StructuredCompilerPrefix.end_unguarded {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position}
    (invariant : StructuredCompilerPrefix emit initial before types functions returns locals parents current raw position)
    (nonBody : current.form.kind ≠ .Body) (noGuard : current.guardPosition = none)
    (state : code.OpIterState) (kind : code.LabelKind) (bt : signature.BlockType)
    (coordinate : before.function.body_start.val + state.pos.val ≤ Usize.max)
    (bound : position ≤ limits.MAX_MODULE_BYTES.val)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state kind bt = .ok (.Ok (), after)) :
    ∃ frame target, before.frames.val = after.frames.val ++ [frame] ∧
      FrameScope locals before current frame ∧ target.val = before.function.code.val.length ∧
      after.reachable = scopeExitLive before.reachable frame ∧
      after.function.code.val = patchCode before.function.code.val frame.fixups.val target := by
  obtain ⟨prior, frame, frames, paired, shape⟩ := invariant.frames.split
  have priorBound : prior.length ≤ Usize.max := by have := before.frames.property; simp only [frames, List.length_append, List.length_singleton] at this; omega
  let rest := alloc.vec.Vec.from prior priorBound
  have restVal : rest.val = prior := by simp [rest]
  have noIf : frame.if_pc = none := by
    have same := shape.guard.trans noGuard
    simpa using same
  have nonRoot : frame.kind ≠ .Body := by simpa [shape.kind] using nonBody
  have fetchBound := invariant.codeBudget.fetch_bound bound
  let target : U32 := UScalar.ofNatCore before.function.code.val.length (by scalar_tac)
  have positionEq : target.val = before.function.code.val.length := by simp [target]
  have sites := (invariant.mode.sites frame (by simp [frames])).branches.branches
  have effect := close_scope_effect ops law before state frame rest target (by simpa [restVal] using frames)
    nonRoot noIf positionEq sites shape.mapBound coordinate
  have call : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state .Block .Empty = .ok (.Ok (), after) := accepted
  rw [call, WP.spec_ok] at effect
  have result := effect rfl
  dsimp only at result
  obtain ⟨popped, live, codeEq, closed⟩ := result
  exact ⟨frame, target, by simpa [popped, restVal] using frames, shape, positionEq, live, codeEq⟩

/-- The entered THEN frame supplies its exact unresolved guard; END resolves
it and the selected frame's forward branches at the same actual endpoint. -/
theorem StructuredCompilerPrefix.end_guarded {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position}
    (invariant : StructuredCompilerPrefix emit initial before types functions returns locals parents current raw position)
    (type : blocktype) (condition : U32) (form : current.form = .then_ type condition)
    (entered : current.entered = true)
    (state : code.OpIterState) (kind : code.LabelKind) (bt : signature.BlockType)
    (coordinate : before.function.body_start.val + state.pos.val ≤ Usize.max)
    (bound : position ≤ limits.MAX_MODULE_BYTES.val)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state kind bt = .ok (.Ok (), after)) :
    ∃ frame target guard, before.frames.val = after.frames.val ++ [frame] ∧
      FrameScope locals before current frame ∧ target.val = before.function.code.val.length ∧
      frame.if_pc = some guard ∧ before.function.code.val[guard.val]? = some (.JumpIfZero condition core.num.U32.MAX) ∧
      after.reachable = true ∧
      after.function.code.val = patchCode
        (before.function.code.val.set guard.val (.JumpIfZero condition target)) frame.fixups.val target := by
  obtain ⟨prior, frame, frames, paired, shape⟩ := invariant.frames.split
  have priorBound : prior.length ≤ Usize.max := by have := before.frames.property; simp only [frames, List.length_append, List.length_singleton] at this; omega
  let rest := alloc.vec.Vec.from prior priorBound
  have restVal : rest.val = prior := by simp [rest]
  have thenKind : frame.kind = .Then := by simpa [form, ScopeForm.kind] using shape.kind
  have guardPosition : frame.if_pc.map UScalar.val = some current.entry := by
    simpa [SourceScope.guardPosition, form, entered] using shape.guard
  cases hasGuard : frame.if_pc with
  | none => simp [hasGuard] at guardPosition
  | some guard =>
    have guardAt : guard.val = current.entry := by simpa [hasGuard] using guardPosition
    have hook : before.function.code.val[guard.val]? = some (.JumpIfZero condition core.num.U32.MAX) := by
      have retained : current.entered = true → before.function.code.val[current.entry]? = some (.JumpIfZero condition core.num.U32.MAX) := by
        simpa [ScopeEntryCode, form] using shape.entryCode
      simpa [guardAt] using retained entered
    have fetchBound := invariant.codeBudget.fetch_bound bound
    let target : U32 := UScalar.ofNatCore before.function.code.val.length (by scalar_tac)
    have positionEq : target.val = before.function.code.val.length := by simp [target]
    have sites := (invariant.mode.sites frame (by simp [frames])).branches.branches
    have effect := close_guarded_scope_effect ops law before state frame rest target (by simpa [restVal] using frames)
      guard condition core.num.U32.MAX (by simp [thenKind]) hasGuard hook positionEq sites shape.mapBound coordinate
    have call : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state .Block .Empty = .ok (.Ok (), after) := accepted
    rw [call, WP.spec_ok] at effect
    have result := effect rfl
    dsimp only at result
    obtain ⟨popped, live, codeEq, closed⟩ := result
    have entryReachable := shape.entered.trans entered
    exact ⟨frame, target, guard, by simpa [popped, restVal] using frames, shape, positionEq, hasGuard, hook,
      by simpa [scopeExitLive, thenKind, entryReachable] using live, codeEq⟩
end Exec.Code
