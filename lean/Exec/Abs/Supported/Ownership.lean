import Exec.Abs.Ownership.Core
import Exec.Abs.Supported.CoreStuck
namespace Itasca.Runtime.Abs.Supported
open Itasca.Runtime.Abs.Ownership

theorem step_owned {bounds : Bounds} {s next : AState}
    (typed : CoreTyped s) (covered : SupportedState s) (owned : CoreOwned bounds s)
    (step : Core.step s = .next next) : CoreOwned bounds next := by
  rcases s with ⟨store,ambient,frames,results⟩
  cases frames with
  | nil => simp [Core.step] at step
  | cons frame rest =>
    have first := owned.values.2 frame (by simp)
    have remaining : ∀ item ∈ rest, FrameOwned bounds item := fun item member => owned.values.2 item (by simp [member])
    have supported := (covered.active frame (by simp)).1
    have frameTyped : FrameTyped store frame [] := by cases typed.typed.frames with | cons head _ => exact head
    cases frame with
    | mk address types locals module labels code values =>
      cases code with
      | nil =>
        have pureStep : astep ⟨store,ambient,⟨address,types,locals,module,labels,[],values⟩ :: rest,results⟩ = .next next := step
        refine ⟨?_,by rw [astep_store pureStep]; exact owned.globals⟩
        cases labels with
        | nil => exact ownership_return first remaining owned.values.1 pureStep
        | cons label labels =>
          simp only [astep] at pureStep
          split at pureStep
          · apply ownership_advance (step := pureStep) owned.values.1
            · exact first
            · exact remaining
          · contradiction
      | cons op after =>
        rcases BinaryInstr.core_head (supported op (by simp)) with head | stuck
        · exact Ownership.instruction_owned bounds store ambient ⟨address,types,locals,module,labels,[],values⟩ rest op after next head frameTyped owned.globals first remaining step
        · exact nomatch (stuck _ _ _ _ _).symm.trans step
end Itasca.Runtime.Abs.Supported
