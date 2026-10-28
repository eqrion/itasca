import Itasca.Runtime.Code.Local.Callbacks.Control.ElseSource
import Itasca.Runtime.Code.Local.Callbacks.Common.FramePlanPop
import Itasca.Runtime.Code.Local.Relations.Common.ResolvedGuards
namespace Itasca.Runtime.Code
open Aeneas.Std

def ScopeForm.isElse : ScopeForm → Bool
  | .else_ _ _ _ _ _ _ => true
  | _ => false

theorem ElseEvidence.fresh {types functions returns locals code labels child label}
    (fresh : child.form.isElse = false) :
    ElseEvidence types functions returns locals code labels child label := by
  unfold ElseEvidence
  split
  · cases form : child.form <;> simp_all [ScopeForm.isElse]
  · trivial

end Itasca.Runtime.Code
