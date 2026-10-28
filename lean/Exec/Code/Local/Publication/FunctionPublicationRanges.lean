import Exec.Code.Local.Publication.FinalControlMapBounds
import Exec.Code.Local.Relations.Common.SourcedWellFormedAcceptance

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Source-coordinate and control-target obligations of the actual final
checker, separated from instruction validity and function slot metadata. -/
structure FunctionPublicationRanges (function : runtime.bytecode.CompiledFunction) : Prop where
  sourceLength : function.source_offsets.length = function.code.length
  sources : ∀ (index : Nat) (bound : index < function.source_offsets.length),
    function.body_start.val ≤ function.source_offsets.val[index].val ∧
    function.source_offsets.val[index].val < function.body_end.val ∧
    (0 < index → (function.source_offsets.val[index-1]'(by
      have bounded : index < function.source_offsets.val.length := bound; omega)).val ≤
      function.source_offsets.val[index].val)
  controls : FinalControlMapBounds function
  targets : ∀ target ∈ function.jump_tables.val, target.val < function.code.length

/-- Once local instruction and slot obligations are established, the retained
ranges discharge all remaining source and control checks in the real checker. -/
theorem FunctionPublicationRanges.well_formed {function : runtime.bytecode.CompiledFunction}
    (held : FunctionPublicationRanges function)
    (nonsynthetic : ¬ (function.body_start = 0#usize ∧ function.body_end = 0#usize))
    (nonempty : 0 < function.code.length)
    (locals : function.local_slots.val ≤ function.slot_count.val)
    (params : function.param_slots.val ≤ function.local_slots.val)
    (returnStart returnCount : U32)
    (last : function.code.val[function.code.length-1]? = some (.Return returnStart returnCount))
    (instructions : ∀ (index : Nat) (bound : index < function.code.length),
      runtime.bytecode.CompiledFunction.instruction_valid function function.code.val[index] = .ok true) :
    runtime.bytecode.CompiledFunction.well_formed function ⦃ result => result = true ⦄ :=
  well_formed_sourced_accepts function nonsynthetic nonempty held.sourceLength locals params returnStart returnCount
    last instructions held.sources held.targets held.controls

end Itasca.Runtime.Code
