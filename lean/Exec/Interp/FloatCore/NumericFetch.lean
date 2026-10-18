import Exec.Interp.FloatCore.Numeric
import Exec.Interp.FloatCore.OrdinaryExecution
import Exec.Spec.Extend
namespace Exec.Interp
open Aeneas Aeneas.Std Abs.Numeric

theorem float_core_numeric_fetched {raw compiled C targets next output s} {f : Abs.AFrame}
    (op : Instruction) (after : List instr)
    (point : FloatFramePoint s raw {f with code := op.source :: after} compiled C targets next output) :
    ∃ instruction, compiled.code.val[raw.pc.val]? = some instruction := by
  have linear : linearSource op.source = true := by cases op <;> (try casesm* Conversion) <;> rfl
  rcases structuredCode_linear_inv linear point.code.current with ⟨target,forward,fetch,tail⟩ | ⟨middle,emitted,tail,head,fragment,rest⟩
  · exact ⟨_,fetch⟩
  · obtain ⟨stack,left,right,shape,emittedEq,middleEq,leftPos,rightPos⟩ := linearEmission_numeric_inv op (floatCoreEmission_numeric_pure op head)
    refine ⟨Code.integerInstruction op left left right,?_⟩
    simpa only [Nat.add_zero] using fragment.fetch (index := 0) (by simp only [emittedEq,List.getElem?_cons_zero])

end Exec.Interp
