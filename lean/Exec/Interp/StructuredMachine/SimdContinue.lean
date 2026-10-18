import Exec.Interp.StructuredMachine.Point
import Exec.Interp.Core.Point

namespace Exec.Interp.StructuredMachine.Simd
open Aeneas.Std

/-- Reuse the retained SIMD continuation after the exact operand suffix has
been replaced. The store may change only through a checked source extension. -/
theorem framePoint_continue {emission : FunctionEmission}
    {before afterStore raw f compiled C targets next output}
    (point : FramePoint emission before raw f compiled C targets next output)
    (extension : Extend_store before afterStore)
    (front operands results : List val) (after : List instr)
    (values : f.vals = front ++ operands)
    (heights : ∀ label ∈ f.labels, label.height ≤ front.length)
    (tail : Code.StructuredCodeWithTables.Point (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS
      compiled.code.val compiled.jump_tables.val targets (front.map Code.valueType ++ results.map Code.valueType)
      after (raw.pc.val+1) next output)
    (pc : U32) (pcNext : pc.val = raw.pc.val+1) :
    FramePoint emission afterStore {raw with pc := pc} {f with code := after,vals := front ++ results}
      compiled C targets next output := by
  refine ⟨point.bindings.extend extension,point.locals,?_,?_⟩
  · have labels := point.labels
    rw [values] at labels
    exact labels.replace_suffix heights
  · simpa only [List.map_append,pcNext] using tail

end Exec.Interp.StructuredMachine.Simd
