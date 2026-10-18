import Exec.Code.Local.Callbacks.Control.ElseSource
namespace Exec.Code

/-- Closing source syntax depends only on the retained form and completed arm lists. -/
inductive ScopeClosed : ScopeForm → List instr → instr → Prop where
  | block (type source) : ScopeClosed (.block type) source (.BLOCK type source)
  | loop (type source) : ScopeClosed (.loop type) source (.LOOP type source)
  | then_ (type condition source) : ScopeClosed (.then_ type condition) source (.IFELSE type source [])
  | else_ (type condition yes yesExit noEntry yesNormal source) :
      ScopeClosed (.else_ type condition yes yesExit noEntry yesNormal) source (.IFELSE type yes source)

end Exec.Code
