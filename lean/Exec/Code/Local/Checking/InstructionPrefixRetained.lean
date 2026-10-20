import Exec.Code.Local.Checking.NumericInstructionPrefix

namespace Exec.Code
open Aeneas Aeneas.Std

/-- Budget, scratch labels, reachability, and operand observations do not
change the checks or owners of stored instructions. -/
theorem CompilerInstructionPrefix.retained {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (held : CompilerInstructionPrefix before)
    (function : after.function = before.function) (frames : after.frames = before.frames) :
    CompilerInstructionPrefix after := by
  have owners : PendingInstructionSite after = PendingInstructionSite before := by
    funext index
    simp only [PendingInstructionSite,frames]
  simpa only [CompilerInstructionPrefix,function,owners] using held

end Exec.Code
