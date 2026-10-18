import Exec.Abs.Cumulative.Ownership
import Exec.Abs.Supported.Language
namespace Exec.Abs.Supported
open Exec.Abs.Ownership

theorem instruction_owned (bounds : Bounds) (s : _root_.store) (ambient : frame)
    (f : AFrame) (rest : List AFrame) (op : instr) (after : List instr) (next : AState)
    (covered : CoreHead op) (typed : FrameTyped s {f with code := op :: after} [])
    (globals : GlobalsOwned bounds s) (frame : FrameOwned bounds f)
    (frames : ∀ item ∈ rest, FrameOwned bounds item)
    (step : Core.instruction s ambient f rest op after = .next next) : CoreOwned bounds next := by
  cases covered with
  | cumulative allowed => exact Cumulative.instruction_owned bounds s ambient f rest op after next allowed typed globals frame frames step
  | external impossible => rw [impossible] at step; contradiction
  | block ty body =>
    have pureStep : astep ⟨s,ambient,{f with code := .BLOCK ty body :: after} :: rest,[]⟩ = .next next := step
    exact ⟨ownership_enter (step := step) frame frames (valuesOwned_nil _), by rw [astep_store pureStep]; exact globals⟩
  | loop ty body =>
    have pureStep : astep ⟨s,ambient,{f with code := .LOOP ty body :: after} :: rest,[]⟩ = .next next := step
    exact ⟨ownership_enter (step := step) frame frames (valuesOwned_nil _), by rw [astep_store pureStep]; exact globals⟩
  | ifelse ty yes no =>
    have pureStep : astep ⟨s,ambient,{f with code := .IFELSE ty yes no :: after} :: rest,[]⟩ = .next next := step
    refine ⟨?_, by rw [astep_store pureStep]; exact globals⟩
    simp only [Core.instruction,astep] at step
    repeat' first | split at step | contradiction
    all_goals
      apply ownership_advance (step := step) (valuesOwned_nil _) ?_ frames
      have values := frame.2
      exact ⟨frame.1, by aesop (add safe forward ValuesOwned.pop)⟩


theorem step_owned {bounds : Bounds} {s next : AState}
    (typed : CoreTyped s) (covered : SupportedState allowed s)
    (heads : ∀ {op}, allowed op → CoreHead op) (owned : CoreOwned bounds s)
    (step : Core.step s = .next next) : CoreOwned bounds next := by
  rcases s with ⟨store,ambient,frames,results⟩
  cases frames with
  | nil => simp [Core.step] at step
  | cons frame rest =>
    have first := owned.values.2 frame (by simp)
    have remaining : ∀ item ∈ rest, FrameOwned bounds item := fun item member => owned.values.2 item (by simp [member])
    have allowed := (covered.active frame (by simp)).1
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
        exact instruction_owned bounds store ambient ⟨address,types,locals,module,labels,[],values⟩ rest op after next
          (heads (allowed op (by simp))) frameTyped owned.globals first remaining step
end Exec.Abs.Supported
