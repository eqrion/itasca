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

theorem codeRel_linear_inv {types functions returns locals code labels stack pc next output op after}
    (linear : linearSource op = true)
    (relation : Code.CodeRel types functions returns locals code labels stack (op :: after) pc next output) :
    (∃ target, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Code.CodeRel types functions returns locals code labels stack (op :: after) target.val next output) ∨
    (∃ middle emitted tail,
      Code.LinearEmission locals stack op emitted middle ∧ Code.Segment code pc emitted tail ∧
      Code.CodeRel types functions returns locals code labels middle after tail next output) := by
  cases relation with
  | linear head fragment rest => exact Or.inr ⟨_, _, _, head, fragment, rest⟩
  | skip forward instruction rest => exact Or.inl ⟨_, forward, instruction, rest⟩
  | _ => simp_all [linearSource]

/-- The emitted head can be inspected by existing exact linear opcode lemmas
without asserting that the following source continuation is also linear. -/
theorem linear_head_certificate {locals before after op emitted code pc tail}
    (head : Code.LinearEmission locals before op emitted after)
    (fragment : Code.Segment code pc emitted tail) :
    Code.LinearCodeRel locals before [op] code pc tail after := by
  obtain ⟨pre, suffix, hc, hp, ht⟩ := fragment
  refine ⟨pre, emitted, suffix, hc, hp, ht, ?_⟩
  simpa only [List.append_nil] using Code.LinearRel.cons head (Code.LinearRel.nil after)

/-- Replacing the active operand suffix retains every static label when the
saved prefixes lie below it. Local updates are permitted exactly when their
type list is preserved, keeping all retained slot coordinates unchanged. -/
theorem structured_linear_continuation {raw f compiled functions targets next output}
    (point : StructuredFramePoint raw f compiled functions targets next output)
    (pc : Aeneas.Std.U32) (locals values : List val) (source : List instr) (middle : List valtype)
    (rest : Code.CodeRel f.module.TYPES functions f.resultTypes (f.locals.map Code.valueType)
      compiled.code.val targets middle source pc.val next output)
    (localTypes : locals.map Code.valueType = f.locals.map Code.valueType)
    (valueTypes : values.map Code.valueType = middle)
    (labels : LabelsMatch values f.labels targets) :
    StructuredFramePoint { raw with pc := pc }
      { f with locals := locals, vals := values, code := source } compiled functions targets next output := by
  refine ⟨labels, ?_⟩
  simpa only [localTypes, valueTypes] using
    (show Code.StructuredPoint f.module.TYPES functions f.resultTypes (f.locals.map Code.valueType)
      compiled.code.val targets middle source pc.val next output from
      ⟨rest, point.code.targets, point.code.normal, point.code.exit, point.code.root⟩)

end Exec.Interp
