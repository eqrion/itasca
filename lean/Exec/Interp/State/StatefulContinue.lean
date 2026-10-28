import Exec.Interp.StructuredMachine.OrdinaryHeads
namespace Itasca.Runtime.Interp.StructuredMachine
open Aeneas.Std

/-- An ordinary source suffix may consume and produce values above every live
label. The exact static continuation and source extension retain its point. -/
theorem FramePoint.continue {before afterStore raw f compiled C targets next output}
    (point : FramePoint before raw f compiled C targets next output)
    (extension : Extend_store before afterStore)
    (front operands results : List val) (after : List instr)
    (values : f.vals=front++operands)
    (heights : ∀ label ∈ f.labels, label.height≤front.length)
    (tail : Code.StructuredCode.Point (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS
      compiled.code.val compiled.jump_tables.val targets (front.map Code.valueType++results.map Code.valueType) after (raw.pc.val+1) next output)
    (pc : U32) (pcNext : pc.val=raw.pc.val+1) :
    FramePoint afterStore {raw with pc:=pc} {f with code:=after,vals:=front++results}
      compiled C targets next output := by
  refine ⟨point.bindings.extend extension,point.locals,?_,?_⟩
  · have labels := point.labels
    rw [values] at labels
    exact labels.replace_suffix heights
  · simpa only [List.map_append,pcNext] using tail
end Itasca.Runtime.Interp.StructuredMachine
