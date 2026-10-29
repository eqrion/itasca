import Itasca.Runtime.Compiler.Local.Publication.BranchMapOwners
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CompilerBranchMetadata
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CompilerCodeMonotoneControl
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlCursor

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Actual branch emission preserves every control-map publication bound;
frame fixups and end-reachability updates retain their owning map indices. -/
theorem compiler_branch_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (depth skip : U32) (conditional : Bool) (held : ControlMapPublication before)
    (called : runtime.compiler.control.FunctionCompiler.branch ops before depth skip conditional = .ok (.Ok (),after)) :
    ControlMapPublication after := by
  apply held.retained (compiler_branch_stable_result ops law before after depth skip conditional (.Ok ()) called)
    (compiler_branch_controls_result ops law before after depth skip conditional (.Ok ()) called)
    (compiler_branch_map_owners ops law before after depth skip conditional (.Ok ()) called)
    (compiler_branch_code_mono ops law before after depth skip conditional (.Ok ()) called)
  rw [compiler_branch_cursor ops law before after depth skip conditional called]

end Itasca.Runtime.Code
