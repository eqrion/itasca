import Itasca.Runtime.Code.Local.Callbacks.Control.ScopeFrameGuard
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std
theorem ScopeFrameShape.guard_distinct {locals scope frame}
    (shape : ScopeFrameShape locals scope frame) (guard : Usize)
    (distinct : frame.if_pc ≠ some guard) : scope.guardPosition ≠ some guard.val := by
  intro equal
  apply distinct
  have mapped := shape.guard.trans equal
  cases atGuard : frame.if_pc with
  | none => simp [atGuard] at mapped
  | some other =>
    simp only [atGuard, Option.map_some, Option.some.injEq] at mapped
    have same : other = guard := by scalar_tac
    simp [same]

/-- ELSE may first append a skip before resolving its guard. -/
theorem FrameScope.set_guard_append {A : Type} {locals} {before after : runtime.compiler.FunctionCompiler A}
    {scope frame} (shape : FrameScope locals before scope frame) (suffix : List Bytecode)
    (guard : Usize) (condition old target : U32)
    (found : before.function.code.val[guard.val]? = some (.JumpIfZero condition old))
    (distinct : frame.if_pc ≠ some guard)
    (code : after.function.code.val = (before.function.code.val ++ suffix).set guard.val (.JumpIfZero condition target))
    (maps : before.function.controls.val.length ≤ after.function.controls.val.length) :
    FrameScope locals after scope frame := by
  apply shape.transport maps
  · simp [code]
  · rw [code]
    exact (shape.entryCode.extend suffix).set_guard guard condition old target
      (fetch_extend found suffix) (shape.toScopeFrameShape.guard_distinct guard distinct)
end Itasca.Runtime.Code
