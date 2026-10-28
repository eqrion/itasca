import Exec.Code.Local.Callbacks.Control.ScopeFramePatch
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- ELSE keeps the original frame signature and stack base, consumes its guard,
and starts the second arm at the resolved destination. -/
theorem ScopeFrameShape.begin_else {locals scope frame}
    (shape : ScopeFrameShape locals scope frame) (bt : blocktype) (condition : U32)
    (form : scope.form = .then_ bt condition) (yesExit : Nat) (noEntry : U32)
    (normal : Bool) (fixups : alloc.vec.Vec Usize) :
    ScopeFrameShape locals (scope.begin_else bt condition yesExit noEntry normal)
      {frame with kind := .Else, if_pc := none, end_reachable := frame.end_reachable || normal, fixups} := by
  refine ⟨rfl, shape.entered, shape.params, shape.results, shape.height, ?_, rfl, rfl, ?_, ?_, ?_⟩
  · change frame.start_pc.val = scope.entry + (if scope.entered then 1 else 0)
    have start := shape.start
    unfold SourceScope.frameStart at start
    rw [form] at start
    exact start
  · simp [SourceScope.begin_else]
  · simp [SourceScope.begin_else]
  · cases normal <;> simp [SourceScope.begin_else]

theorem FrameScope.begin_else {A : Type} {locals} {before after : runtime.compiler.FunctionCompiler A}
    {scope frame} (shape : FrameScope locals before scope frame) (bt : blocktype) (condition : U32)
    (form : scope.form = .then_ bt condition) (yesExit : Nat) (noEntry : U32)
    (normal : Bool) (fixups : alloc.vec.Vec Usize)
    (maps : before.function.controls.val.length ≤ after.function.controls.val.length)
    (code : before.function.code.val.length ≤ after.function.code.val.length)
    (bodyBound : noEntry.val ≤ after.function.code.val.length) :
    FrameScope locals after (scope.begin_else bt condition yesExit noEntry normal)
      {frame with kind := .Else, if_pc := none, end_reachable := frame.end_reachable || normal, fixups} := by
  exact ⟨shape.toScopeFrameShape.begin_else bt condition form yesExit noEntry normal fixups,
    shape.mapBound.trans_le maps, shape.entryBound.trans code, bodyBound, trivial⟩

/-- Recording a forward branch changes only its target frame's fixup list and
exit liveness. Loop targets are handled separately and never record fixups. -/
theorem ScopeFrameShape.record_branch {locals scope frame}
    (shape : ScopeFrameShape locals scope frame) (fixups : alloc.vec.Vec Usize)
    (forward : frame.kind ≠ .Loop) :
    ScopeFrameShape locals scope {frame with fixups, end_reachable := true} := by
  refine ⟨shape.kind, shape.entered, shape.params, shape.results, shape.height,
    shape.start, shape.body, shape.guard, shape.root, ?_, by simp⟩
  intro bt form
  have kind := shape.kind
  simp only [form, ScopeForm.kind] at kind
  exact (forward kind).elim

theorem FrameScope.record_branch {A : Type} {locals} {compiler : runtime.compiler.FunctionCompiler A}
    {scope frame} (shape : FrameScope locals compiler scope frame) (fixups : alloc.vec.Vec Usize)
    (forward : frame.kind ≠ .Loop) :
    FrameScope locals compiler scope {frame with fixups, end_reachable := true} :=
  ⟨shape.toScopeFrameShape.record_branch fixups forward, shape.mapBound, shape.entryBound,
    shape.bodyBound, shape.entryCode⟩
end Itasca.Runtime.Code
