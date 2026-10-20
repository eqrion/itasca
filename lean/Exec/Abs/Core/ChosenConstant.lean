import Exec.Abs.Core.Pure
import Exec.Abs.Sim.ChosenTyped
namespace Exec.Abs.Core
open SpecExt Exec.Spec

theorem constant_chosen_progress {choices : SourceChoices} (occurrence : Nat) (s : _root_.store) (ambient : frame) (f : AFrame) (rest : List AFrame)
    (after : List instr) (ty : numtype) (value : num_)
    (typed : CoreTyped ⟨s,ambient,{f with code := .CONST ty value :: after} :: rest,[]⟩) :
    ∃ next, instruction s ambient f rest (.CONST ty value) after = .next next ∧ CoreTyped next ∧
      ChosenNextSim choices occurrence ⟨s,ambient,{f with code := .CONST ty value :: after} :: rest,[]⟩ next := by
  let next : AState := ⟨s,ambient,{f with code := after, vals := f.vals ++ [.CONST ty value]} :: rest,[]⟩
  have fresh := const_preservation s ambient f rest after ty value [] typed.typed
  have frameTyped : FrameTyped s {f with code := .CONST ty value :: after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  refine ⟨next,rfl,⟨fresh,typed.contents⟩,Or.inl ⟨?_,?_⟩⟩
  · exact decode_const s ambient f rest ty value after (by simpa only [FrameHeights] using frameTyped_heights frameTyped)
  · exact const_measure_decreases s ambient f rest ty value after

end Exec.Abs.Core
