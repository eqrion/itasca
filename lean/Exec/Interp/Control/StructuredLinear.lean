import Exec.Interp.Control.StructuredPoint
import Exec.Interp.Relations.Rel
import Exec.Abs.Sim.Typed

namespace Exec.Interp

def linearSource : instr → Bool
  | .NOP | .DROP | .CONST .. | .BINOP .. | .TESTOP .. | .RELOP ..
  | .UNOP .. | .CVTOP .. | .LOCAL_GET .. | .LOCAL_SET .. | .LOCAL_TEE .. => true
  | _ => false

def linearInputs : instr → Nat
  | .DROP | .TESTOP .. | .UNOP .. | .CVTOP .. | .LOCAL_SET .. | .LOCAL_TEE .. => 1
  | .BINOP .. | .RELOP .. => 2
  | _ => 0

theorem linearSource_inputs {C : context} {op : instr} {inputs outputs : List valtype}
    (linear : linearSource op = true)
    (typed : Instr_ok C op ⟨.mk_list inputs, .mk_list outputs⟩) : inputs.length = linearInputs op := by
  cases typed <;> simp_all [linearSource, linearInputs]

/-- Generated operand typing places every saved label prefix below the values
consumed by a linear instruction, even when its replacement changes a value. -/
theorem frame_linear_heights {s : store} {f : Abs.AFrame} {op : instr} {code : List instr}
    (typed : Abs.FrameTyped s { f with code := op :: code } [])
    (linear : linearSource op = true) (front : List val)
    (shape : f.vals.length = front.length + linearInputs op) :
    ∀ label ∈ f.labels, label.height ≤ front.length := by
  obtain ⟨C, first, operands, ins, outs, bindings, localTypes, operation, split, values, wf, heights⟩ :=
    Abs.frame_typed_operands_bounds typed
  have count := linearSource_inputs linear operation
  have operandsLength := Spec.resultsTyped_length values
  have firstLength : first.length = front.length := by
    have splitLength := congrArg List.length split
    simp only [List.length_append] at splitLength
    omega
  simpa only [firstLength] using heights

end Exec.Interp
