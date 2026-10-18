import Exec.Code.Local.Callbacks.Control.ScopeFramePatch
namespace Exec.Code
open Aeneas Aeneas.Std

/-- Resolving another frame's IF guard preserves this scope's entry instruction. -/
theorem ScopeEntryCode.set_guard {code scope} (entry : ScopeEntryCode code scope)
    (guard : Usize) (condition old target : U32)
    (found : code[guard.val]? = some (.JumpIfZero condition old))
    (distinct : scope.guardPosition ≠ some guard.val) :
    ScopeEntryCode (code.set guard.val (.JumpIfZero condition target)) scope := by
  unfold ScopeEntryCode at *
  split at entry <;> try simp_all only
  · intro live
    have atEntry := entry live
    have away : guard.val ≠ scope.entry := by
      intro equal
      rw [equal, atEntry] at found
      cases found
    rw [List.getElem?_set_ne away]
    exact atEntry
  · intro live
    have away : guard.val ≠ scope.entry := by
      intro equal
      apply distinct
      simp_all [SourceScope.guardPosition]
    rw [List.getElem?_set_ne away]
    exact entry live

theorem FrameScope.set_guard {A : Type} {locals} {before after : runtime.compiler.FunctionCompiler A}
    {scope frame} (shape : FrameScope locals before scope frame)
    (guard : Usize) (condition old target : U32)
    (found : before.function.code.val[guard.val]? = some (.JumpIfZero condition old))
    (distinct : frame.if_pc ≠ some guard)
    (code : after.function.code.val = before.function.code.val.set guard.val (.JumpIfZero condition target))
    (maps : before.function.controls.val.length ≤ after.function.controls.val.length) :
    FrameScope locals after scope frame := by
  apply shape.transport maps
  · simp [code]
  · rw [code]
    apply shape.entryCode.set_guard guard condition old target found
    intro equal
    apply distinct
    have mapped := shape.guard.trans equal
    cases atGuard : frame.if_pc with
    | none => simp [atGuard] at mapped
    | some other =>
      simp only [atGuard, Option.map_some, Option.some.injEq] at mapped
      have same : other = guard := by scalar_tac
      simp [same]
end Exec.Code
