import Exec.Spec.Depth
import Itasca.Generated.Types
namespace Itasca.Runtime.Theorems
open Aeneas Aeneas.Std SpecExt
/-- Call-stack exhaustion is bounded by decoded frame nesting; termination
retains a concrete interrupt decision. -/
def InvocationBoundaryCause {M P : Type} (hooks : runtime.platform.Platform P M)
    (initial : config) (maxFrames : Nat) : runtime.ExecError → Prop
  | .Exhausted .CallStack => maxFrames ≤ Spec.frameDepth initial ∨
      ∃ final, StepsH initial [] final ∧ maxFrames ≤ Spec.frameDepth final
  | .Terminated => ∃ before after, hooks.interrupt before = .ok (.Terminate, after)
  | _ => True

end Itasca.Runtime.Theorems
