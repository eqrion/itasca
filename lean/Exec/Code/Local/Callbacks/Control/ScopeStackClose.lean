import Exec.Code.Local.Callbacks.Control.ScopeStackElse
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Ordinary END resolves forward branches and removes the inner physical
frame; all suspended scope entry instructions survive those fixups. -/
theorem ScopeFrameStack.close_branches {A : Type} {locals parents parent current}
    {before after : runtime.compiler.FunctionCompiler A}
    (stack : ScopeFrameStack locals before (parents ++ [parent]) current)
    (frame : runtime.compiler.Frame) (target : U32)
    (frames : before.frames.val = after.frames.val ++ [frame])
    (branches : ForwardSites before.function.code.val frame.fixups.val)
    (code : after.function.code.val = patchCode before.function.code.val frame.fixups.val target)
    (maps : before.function.controls.val.length ≤ after.function.controls.val.length) :
    ScopeFrameStack locals after parents parent := by
  apply stack.pop frame frames
  intro scope other _ shape
  exact shape.patch_branches branches target code maps

/-- END of an IF without ELSE first resolves its guard and then its branch
fixups. Nesting derives every outer-frame guard exclusion used here. -/
theorem ScopeFrameStack.close_guard {A : Type} {locals parents parent current}
    {before after : runtime.compiler.FunctionCompiler A}
    (stack : ScopeFrameStack locals before (parents ++ [parent]) current)
    (frame : runtime.compiler.Frame) (guard : Usize) (condition old target : U32)
    (frames : before.frames.val = after.frames.val ++ [frame]) (guardEq : frame.if_pc = some guard)
    (found : before.function.code.val[guard.val]? = some (.JumpIfZero condition old))
    (branches : ForwardSites before.function.code.val frame.fixups.val)
    (code : after.function.code.val = patchCode
      (before.function.code.val.set guard.val (.JumpIfZero condition target)) frame.fixups.val target)
    (maps : before.function.controls.val.length ≤ after.function.controls.val.length) :
    ScopeFrameStack locals after parents parent := by
  have distinct := stack.distinct_guard after.frames.val frame frames guard guardEq
  have patchedSites : ForwardSites
      (before.function.code.val.set guard.val (.JumpIfZero condition target)) frame.fixups.val := by
    simpa [patchCode, found, retarget] using branches.patch [guard] target
  apply stack.pop frame frames
  intro scope other member shape
  apply shape.transport maps
  · simp [code, patchCode_length]
  · rw [code]
    exact (shape.entryCode.set_guard guard condition old target found
      (shape.toScopeFrameShape.guard_distinct guard (distinct other member))).patch_branches patchedSites target

/-- A wholly dormant IF has no guard to resolve at ELSE. Its retained outer
frames are unchanged while the active source scope switches arms. -/
theorem ScopeFrameStack.begin_else_dormant {A : Type} {locals parents current}
    {before after : runtime.compiler.FunctionCompiler A} (stack : ScopeFrameStack locals before parents current)
    (prior : List runtime.compiler.Frame) (frame : runtime.compiler.Frame)
    (bt : blocktype) (condition : U32) (form : current.form = .then_ bt condition)
    (noEntry : U32) (position : noEntry.val = before.function.code.val.length)
    (beforeFrames : before.frames.val = prior ++ [frame])
    (afterFrames : after.frames.val = prior ++ [{frame with kind := .Else, if_pc := none}])
    (code : after.function.code.val = before.function.code.val)
    (maps : before.function.controls.val.length ≤ after.function.controls.val.length) :
    ScopeFrameStack locals after parents (current.begin_else bt condition noEntry.val noEntry false) := by
  obtain ⟨paired, shape⟩ := stack.parts prior frame beforeFrames
  have order : before.function.code.val.length ≤ after.function.code.val.length := by rw [code]
  have retained : List.Forall₂ (FrameScope locals after) parents prior :=
    paired.imp (fun _ _ shape => shape.transport maps order (by rw [code]; exact shape.entryCode))
  have fresh := shape.begin_else bt condition form noEntry.val noEntry false frame.fixups maps order
    (by rw [position, code])
  simp only [Bool.or_false] at fresh
  apply stack.replace_current _ prior _ afterFrames retained fresh rfl
  change current.entry ≤ noEntry.val
  rw [position]
  exact shape.entryBound
end Itasca.Runtime.Code
