import Exec.Interp.StructuredMachine.IndexedLinear
import Exec.Interp.StructuredMachine.Numeric
import Exec.Interp.StructuredMachine.OrdinaryExecution
import Exec.Spec.Extend
namespace Exec.Interp.StructuredMachine
open Aeneas Aeneas.Std Abs.Numeric
variable {emission : FunctionEmission} [∀ compiled, FloatHeads (emission compiled)]

theorem numeric_fetched {raw compiled C targets next output s} {f : Abs.AFrame}
    (op : Instruction) (after : List instr)
    (point : FramePoint emission s raw {f with code := op.source :: after} compiled C targets next output) :
    ∃ instruction, compiled.code.val[raw.pc.val]? = some instruction := by
  have linear : linearSource op.source = true := by cases op <;> (try casesm* Conversion) <;> rfl
  rcases structuredCodeWithTables_linear_inv linear point.code.current with ⟨target,forward,fetch,tail⟩ | ⟨middle,emitted,tail,head,fragment,rest⟩
  · exact ⟨_,fetch⟩
  · obtain ⟨stack,left,right,shape,emittedEq,middleEq,leftPos,rightPos⟩ := linearEmission_numeric_inv op (emission_numeric_pure op head)
    refine ⟨Code.integerInstruction op left left right,?_⟩
    simpa only [Nat.add_zero] using fragment.fetch (index := 0) (by simp only [emittedEq,List.getElem?_cons_zero])

end Exec.Interp.StructuredMachine
