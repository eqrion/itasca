import Exec.Interp.Numeric.Float.FloatPoint
import Exec.Code.Local.Lowering.Float.FloatCoreProjection
import Exec.Interp.Numeric.Float.FloatMemoryPoint
import Exec.Interp.Core.Point
namespace Exec.Interp.FloatMemoryDescriptor
open Exec.Interp.MemoryDescriptor
open Aeneas Aeneas.Std SpecExt

theorem corePoint_load_continue {sourceStore raw f compiled C targets next output}
    (point : FloatFramePoint sourceStore raw f compiled C targets next output)
    (front : List val) (bits : Nat) (value : val) (ty : numtype) (after : List instr)
    (values : f.vals = front ++ [Abs.integerVal .I32 bits])
    (heights : ∀ label ∈ f.labels, label.height ≤ front.length)
    (valueType : Code.valueType value = valtype_numtype ty)
    (tail : Code.StructuredCode.Point (Code.FloatCoreEmission C) C.TYPES C.FUNCS f.resultTypes C.LOCALS
      compiled.code.val targets (front.map Code.valueType ++ [valtype_numtype ty]) after (raw.pc.val+1) next output)
    (pc : U32) (pcNext : pc.val = raw.pc.val+1) :
    FloatFramePoint sourceStore {raw with pc := pc} {f with code := after,vals := front ++ [value]}
      compiled C targets next output := by
  refine ⟨point.bindings,point.locals,?_,?_⟩
  · have labels := point.labels
    rw [values] at labels
    exact labels.replace_suffix heights
  · simpa only [List.map_append,List.map_cons,List.map_nil,valueType,pcNext] using tail

theorem corePoint_store_continue {before afterStore raw f compiled C targets next output}
    (point : FloatFramePoint before raw f compiled C targets next output)
    (extension : Extend_store before afterStore)
    (front operands : List val) (after : List instr)
    (values : f.vals = front ++ operands)
    (heights : ∀ label ∈ f.labels, label.height ≤ front.length)
    (tail : Code.StructuredCode.Point (Code.FloatCoreEmission C) C.TYPES C.FUNCS f.resultTypes C.LOCALS
      compiled.code.val targets (front.map Code.valueType) after (raw.pc.val+1) next output)
    (pc : U32) (pcNext : pc.val = raw.pc.val+1) :
    FloatFramePoint afterStore {raw with pc := pc} {f with code := after,vals := front}
      compiled C targets next output := by
  refine ⟨point.bindings.extend extension,point.locals,?_,?_⟩
  · have labels := point.labels
    rw [values] at labels
    simpa only [List.append_nil] using labels.replace_suffix (after := []) heights
  · simpa only [pcNext] using tail
end Exec.Interp.FloatMemoryDescriptor
