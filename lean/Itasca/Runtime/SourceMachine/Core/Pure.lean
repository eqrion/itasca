import Itasca.Runtime.SourceMachine.Core.Step
import Itasca.Runtime.SourceMachine.Sim.Instruction

namespace Itasca.Runtime.Abs.Core
open SpecExt Itasca.Runtime.Spec

theorem instruction_slice (s : _root_.store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (op : instr) (after : List instr)
    (covered : PureHead op)
    (typed : FrameTyped s {f with code := op :: after} []) :
    instruction s ambient f rest op after =
      astep ⟨s,ambient,{f with code := op :: after} :: rest,[]⟩ := by
  cases covered with
  | numeric descriptor =>
    cases descriptor with
    | conversion conversion => cases conversion <;> rfl
    | _ => rfl
  | const ty value =>
    have progress := const_progress s ambient f rest after ty value typed
    simp only [instruction,astep] at progress ⊢
    split <;> simp_all [advance]
  | local_get index => cases index; rfl
  | local_set index => cases index; rfl
  | local_tee index => cases index; rfl
  | br index => cases index; rfl
  | br_if index => cases index; rfl
  | call index => cases index; rfl
  | _ => rfl

/-- All numeric constants, including floating encodings, are administrative
moves with identical source decoding and a strictly decreasing potential. -/
theorem constant_progress (s : _root_.store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (after : List instr) (ty : numtype) (value : num_)
    (typed : CoreTyped ⟨s,ambient,{f with code := .CONST ty value :: after} :: rest,[]⟩) :
    ∃ next, instruction s ambient f rest (.CONST ty value) after = .next next ∧ CoreTyped next ∧
      NextSim ⟨s,ambient,{f with code := .CONST ty value :: after} :: rest,[]⟩ next := by
  let next : AState := ⟨s,ambient,{f with code := after, vals := f.vals ++ [.CONST ty value]} :: rest,[]⟩
  have fresh := const_preservation s ambient f rest after ty value [] typed.typed
  have frameTyped : FrameTyped s {f with code := .CONST ty value :: after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  refine ⟨next,rfl,⟨fresh,typed.contents⟩,Or.inl ⟨?_,?_⟩⟩
  · exact decode_const s ambient f rest ty value after (by simpa only [FrameHeights] using frameTyped_heights frameTyped)
  · exact const_measure_decreases s ambient f rest ty value after

end Itasca.Runtime.Abs.Core

