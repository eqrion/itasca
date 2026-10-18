import Exec.Abs.Sim.Instruction

namespace Exec.Abs
open SpecExt Exec.Spec

theorem typed_label_end_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (label : Label) (labels : List Label) (next : AState)
    (typed : ATyped ⟨s, ambient, { f with code := [], labels := label :: labels } :: rest, []⟩)
    (step : astep ⟨s, ambient, { f with code := [], labels := label :: labels } :: rest, []⟩ = .next next) :
    NextSim ⟨s, ambient, { f with code := [], labels := label :: labels } :: rest, []⟩ next := by
  have frames := typed.frames
  cases frames with
  | cons hf hr =>
    obtain ⟨hw, hl, hv, _⟩ := frameTyped_wf hf
    have nested : ∀ outer ∈ labels, outer.height ≤ label.height := by
      cases hf with
      | mk C _ _ _ _ _ code _ => exact (codeStack_labels_nested code).1
    have heights := frameTyped_heights hf
    have result := label_exit_simulation s ambient f rest label labels typed.store typed.ambient hw hl hv
      (framesTyped_wf hr) (heights label (by simp)) nested
    simp only [astep] at step
    split at step
    · simp only [advance, AResult.next.injEq] at step
      rw [← step]
      exact .single result
    · contradiction

/-- Complete counted simulation for every successful step of the initial
integer slice, including label completion, direct calls, and returns. -/
theorem astep_simulation (s next : AState) (typed : ATyped s) (slice : SliceState s)
    (step : astep s = .next next) : NextSim s next := by
  rcases s with ⟨store, ambient, frames, results⟩
  cases frames with
  | nil => simp [astep] at step
  | cons frame rest =>
    have hresults := typed.activeResults (by simp)
    change results = [] at hresults
    subst results
    have hslice := (slice.active frame (by simp)).1
    cases frame with
    | mk addr rts locals m labels code values =>
      let f : AFrame := ⟨addr, rts, locals, m, labels, code, values⟩
      cases code with
      | cons op after =>
        exact instruction_simulation store ambient f rest op after next (hslice op (by simp)) typed step
      | nil =>
        cases labels with
        | nil => exact .single (typed_frame_end_simulation store ambient f rest next typed step)
        | cons label labels => exact typed_label_end_simulation store ambient f rest label labels next typed step

/-- Expose the counted form used by the quantitative iteration theorem. -/
theorem astep_counted (s next : AState) (typed : ATyped s) (slice : SliceState s)
    (step : astep s = .next next) :
    ∃ n, StepsHN n (decode s) [] (decode next) ∧
      (n = 0 → administrativeMeasure next < administrativeMeasure s) := by
  rcases astep_simulation s next typed slice step with ⟨same, decreases⟩ | ⟨n, positive, simulation⟩
  · refine ⟨0, ?_, fun _ => decreases⟩
    rw [same]
    exact .refl ((astep_preservation s next typed slice step).decode_wf)
  · exact ⟨n, simulation, by omega⟩

end Exec.Abs
