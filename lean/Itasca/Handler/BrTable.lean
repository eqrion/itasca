import Itasca.Handler.StackSemantics
import Itasca.Handler.ResumePrefix
import Itasca.Visitor.Total
import Itasca.Binary.Wasm1.BrTableLabels

/-!
# Branch table handlers

Lemmas about the extracted `br_table` reader. `BrTable.Targets` says every decoded label exists
and has a common target type. `code.read_table_labels.spec` shows label iteration terminates,
`code.read_br_table.prefix` shows a successful `br_table` decodes its labels, has a common target
type and extends a `Sequence.TypedPrefix` by the generated rule (`BrTable.instruction_typed`), and
`code.step_br_table.of_read` lifts reader facts to `code.step`.
-/

open Aeneas Aeneas.Std

namespace Itasca.BrTable

end Itasca.BrTable

namespace Itasca

end Itasca

namespace Itasca.BrTable

end Itasca.BrTable

namespace Itasca

end Itasca

namespace Itasca.BrTable

/-- The SpecTec `br_table` instruction with the given label depths and default. -/
def instruction (depths : List U32) (default : U32) : instr :=
  .BR_TABLE (depths.map (fun d => .mk_uN d.val)) (.mk_uN default.val)

/-- The `br_table` instruction is well-formed. -/
theorem instruction_wf (depths : List U32) (default : U32) :
    wf_instr (instruction depths default) := by
  apply wf_instr.instr_case_9
  · simp only [Forall, List.mem_map]
    rintro _ ⟨d, hd, rfl⟩
    exact Spec.label_wf d
  · exact Spec.label_wf default

end Itasca.BrTable

namespace Itasca

end Itasca

namespace Itasca

end Itasca
