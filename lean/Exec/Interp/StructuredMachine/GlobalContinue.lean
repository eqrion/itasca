import Exec.Code.Local.Lowering.Float.FloatEmissionInversion
import Exec.Interp.StructuredMachine.GlobalPrepare
namespace Exec.Interp.StructuredMachine.Global
open Aeneas Aeneas.Std SpecExt

theorem decode_words_valueType (ty : Itasca.types.ValueType) (lo hi : U64) :
    Code.valueType (Store.decodeWords ty lo hi) = sourceType ty := by
  cases ty <;> simp only [Store.decodeWords,Store.decodeRef,Store.decodeElemType,sourceType]
  all_goals first | rfl | (split <;> rfl)

theorem corePoint_globalGet_continue {sourceStore raw f compiled C targets next output}
    (point : FramePoint sourceStore raw f compiled C targets next output)
    (value : val) (ty : valtype) (after : List instr)
    (heights : ∀ label ∈ f.labels, label.height ≤ f.vals.length)
    (valueType : Code.valueType value = ty)
    (tail : Code.StructuredCode.Point (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS
      compiled.code.val compiled.jump_tables.val targets (f.vals.map Code.valueType ++ [ty]) after (raw.pc.val+1) next output)
    (pc : U32) (pcNext : pc.val = raw.pc.val+1) :
    FramePoint sourceStore {raw with pc := pc} {f with code := after,vals := f.vals ++ [value]}
      compiled C targets next output := by
  refine ⟨point.bindings,point.locals,?_,?_⟩
  · have labels : LabelsMatch (f.vals ++ []) f.labels targets := by simpa only [List.append_nil] using point.labels
    exact labels.replace_suffix heights
  · simpa only [List.map_append,List.map_cons,List.map_nil,valueType,pcNext] using tail

theorem corePoint_globalSet_continue {before afterStore raw f compiled C targets next output}
    (point : FramePoint before raw f compiled C targets next output)
    (extension : Extend_store before afterStore)
    (front : List val) (value : val) (after : List instr)
    (values : f.vals = front ++ [value])
    (heights : ∀ label ∈ f.labels, label.height ≤ front.length)
    (tail : Code.StructuredCode.Point (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS
      compiled.code.val compiled.jump_tables.val targets (front.map Code.valueType) after (raw.pc.val+1) next output)
    (pc : U32) (pcNext : pc.val = raw.pc.val+1) :
    FramePoint afterStore {raw with pc := pc} {f with code := after,vals := front}
      compiled C targets next output := by
  refine ⟨point.bindings.extend extension,point.locals,?_,?_⟩
  · have labels := point.labels
    rw [values] at labels
    simpa only [List.append_nil] using labels.replace_suffix (after := []) heights
  · simpa only [pcNext] using tail
end Exec.Interp.StructuredMachine.Global
