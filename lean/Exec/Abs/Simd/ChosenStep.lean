import Exec.Abs.Simd.Step
import Exec.Abs.Simd.ChosenSimulation
import Exec.Abs.Simd.ChosenMemory
import Exec.Abs.Sim.ChosenBasic
namespace Exec.Abs.Simd
open SpecExt Exec.Spec

/-- The choosing pure primitive is specified independently; memory operations
retain their generated deterministic effects. -/
inductive ChosenStep (choices : SourceChoices) (occurrence : Nat) : AState → AResult → Prop where
  | pure {s : store} {ambient : frame} {f : AFrame} {rest : List AFrame}
      {after : List instr} {source inputs output} {front operands : List val} {value : val}
      (signature : PureSignature source inputs output)
      (values : f.vals=front++operands) (types : operands.map valueType=inputs)
      (effect : PureResult source output operands value)
      (selected : ChosenPure choices occurrence (vals operands++[admininstr_instr source]) [admininstr_val value]) :
      ChosenStep choices occurrence ⟨s,ambient,{f with code:=source::after}::rest,[]⟩
        (.next ⟨s,ambient,{f with code:=after,vals:=front++[value]}::rest,[]⟩)
  | constant {s : store} {ambient : frame} {f : AFrame} {rest : List AFrame}
      {after : List instr} {value : vec_} :
      ChosenStep choices occurrence ⟨s,ambient,{f with code:=.VCONST .V128 value::after}::rest,[]⟩
        (.next (constant ⟨s,ambient,{f with code:=.VCONST .V128 value::after}::rest,[]⟩ f rest after value))
  | memory {s : store} {ambient : frame} {f : AFrame} {rest : List AFrame}
      {after : List instr} {source inputs outputs result}
      (signature : MemorySignature source inputs outputs)
      (transition : MemoryTransition ⟨s,ambient,{f with code:=source::after}::rest,[]⟩
        {f with code:=source::after} rest after source inputs outputs result) :
      ChosenStep choices occurrence ⟨s,ambient,{f with code:=source::after}::rest,[]⟩ result

theorem ChosenStep.erases {choices occurrence before result}
    (step : ChosenStep choices occurrence before result) : Step before result := by
  cases step with
  | pure signature values types effect selected => exact .pure signature (.next _ _ _ values types effect)
  | constant => exact .constant
  | memory signature transition => exact .memory signature transition

theorem ChosenStep.next_simulation {choices : SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=firstVectorChoice) {occurrence before next}
    (step : ChosenStep choices occurrence before (.next next)) (typed : CoreTyped before) :
    ChosenNextSim choices occurrence before next := by
  cases step with
  | pure signature values types effect selected =>
    exact ChosenNextSim.single admissible (signature.chosen_simulation admissible typed.typed values types selected)
  | @constant s ambient f rest after value =>
    have hf : FrameTyped s {f with code := .VCONST .V128 value :: after} [] := by
      cases typed.typed.frames with | cons h _ => exact h
    have heights : ∀ l ∈ f.labels, l.height ≤ f.vals.length := by simpa only [FrameHeights] using frameTyped_heights hf
    apply Or.inl
    constructor
    · simp only [Simd.constant,decode,decodeFrames,vals,List.map_nil,List.nil_append,
        AFrame.toFrame,List.map_cons,admininstr_instr]
      rw [decodeLabels_move_values _ _ _ _ heights]
      rfl
    · simp [Simd.constant,administrativeMeasure]
  | memory signature transition =>
    exact memory_transition_chosen_simulation admissible vector _ signature typed.typed transition

theorem ChosenStep.trap_simulation {choices : SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=firstVectorChoice) {occurrence before}
    (step : ChosenStep choices occurrence before .trap) (typed : CoreTyped before) :
    ∃ count,0<count ∧ ChosenStepsN choices occurrence count (decode before) [] ⟨⟨before.store,before.ambient⟩,[.TRAP]⟩ := by
  cases step with
  | memory signature transition => exact memory_transition_chosen_trap_simulation admissible vector _ signature typed.typed transition
end Exec.Abs.Simd
