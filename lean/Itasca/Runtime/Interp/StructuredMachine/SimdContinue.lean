import Itasca.Runtime.Interp.StructuredMachine.Point
import Itasca.Runtime.Code.Local.Relations.Common.ScalarEmission
import Itasca.Runtime.Code.Local.Control.Common.Structured
import Itasca.Runtime.Code.Local.Control.Common.StructuredComposition
import Itasca.Runtime.Code.Local.Control.Common.StructuredLabels
import Itasca.Runtime.Interp.Control.StructuredPoint
import Itasca.Runtime.Abs.ModuleBindingsExtension

namespace Itasca.Runtime.Interp.StructuredMachine.Simd
open Aeneas.Std

/-- Reuse the retained SIMD continuation after the exact operand suffix has
been replaced. The store may change only through a checked source extension. -/
theorem framePoint_continue
    {before afterStore raw f compiled C targets next output}
    (point : FramePoint before raw f compiled C targets next output)
    (extension : Extend_store before afterStore)
    (front operands results : List val) (after : List instr)
    (values : f.vals = front ++ operands)
    (heights : ∀ label ∈ f.labels, label.height ≤ front.length)
    (tail : Code.StructuredCode.Point (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS
      compiled.code.val compiled.jump_tables.val targets (front.map Code.valueType ++ results.map Code.valueType)
      after (raw.pc.val+1) next output)
    (pc : U32) (pcNext : pc.val = raw.pc.val+1) :
    FramePoint afterStore {raw with pc := pc} {f with code := after,vals := front ++ results}
      compiled C targets next output := by
  refine ⟨point.bindings.extend extension,point.locals,?_,?_⟩
  · have labels := point.labels
    rw [values] at labels
    exact labels.replace_suffix heights
  · simpa only [List.map_append,pcNext] using tail

end Itasca.Runtime.Interp.StructuredMachine.Simd
