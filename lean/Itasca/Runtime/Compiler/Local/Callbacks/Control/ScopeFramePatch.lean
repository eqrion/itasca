import Itasca.Runtime.Compiler.Local.Callbacks.Control.ScopeFrame
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Forward branch fixups cannot overwrite a LOOP hook or an open IF guard. -/
theorem ScopeEntryCode.patch_branches {code scope sites}
    (entry : ScopeEntryCode code scope) (branches : ForwardSites code sites) (target : U32) :
    ScopeEntryCode (patchCode code sites target) scope := by
  unfold ScopeEntryCode at *
  split at entry <;> try simp_all only
  · intro live
    have found := entry live
    rw [patchCode_get]
    split
    · simp [found, retarget]
    · exact found
  · intro live
    have found := entry live
    rw [patchCode_other code sites target scope.entry (fun site member => (branches.not_guard found site member).symm)]
    exact found

/-- Closing a child changes parent code targets while retaining parent entry geometry. -/
theorem FrameScope.patch_branches {A : Type} {locals} {before after : runtime.compiler.FunctionCompiler A}
    {scope frame sites} (shape : FrameScope locals before scope frame)
    (branches : ForwardSites before.function.code.val sites) (target : U32)
    (code : after.function.code.val = patchCode before.function.code.val sites target)
    (maps : before.function.controls.val.length ≤ after.function.controls.val.length) :
    FrameScope locals after scope frame := by
  apply shape.transport maps
  · simp [code, patchCode_length]
  · simpa only [code] using shape.entryCode.patch_branches branches target
end Itasca.Runtime.Code
