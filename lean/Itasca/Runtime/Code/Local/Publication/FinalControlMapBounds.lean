import Itasca.Runtime.Code.Local.Publication.ControlMapPublication

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Exact control-map ranges required by the final publication checker. Unlike
intermediate closed-map bounds, every target is strictly inside final code. -/
def FinalControlMapBounds (function : runtime.bytecode.CompiledFunction) : Prop :=
  ∀ entry ∈ function.controls.val,
    entry.start_pc.val ≤ entry.end_pc.val ∧ entry.end_pc.val < function.code.length ∧
    function.body_start.val ≤ entry.source_start.val ∧ entry.source_end.val ≤ function.body_end.val ∧
    entry.source_start.val < entry.source_end.val

end Itasca.Runtime.Code
