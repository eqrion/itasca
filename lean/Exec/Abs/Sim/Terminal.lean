import Exec.Abs.Sim.Step

namespace Exec.Abs
open SpecExt Exec.Spec

/-- Scalar integer traps arise from an explicit unreachable instruction or a numeric operation. -/
theorem instruction_trap_eq (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (op : instr) (after : List instr) (allowed : SliceInstr op)
    (step : astep ⟨s, ambient, { f with code := op :: after } :: rest, []⟩ = .trap) :
    op = .UNREACHABLE ∨ ∃ descriptor : Numeric.Instruction, op = descriptor.source := by
  cases allowed
  case numeric descriptor => exact .inr ⟨descriptor, rfl⟩
  case unreachable => exact .inl rfl
  all_goals
    simp only [astep, advance, integerBinary, branch, enterLabel, call, returnFrame] at step
    repeat' first | contradiction | split at step

theorem typed_trap_simulation (s : AState) (typed : ATyped s) (slice : SliceState s)
    (step : astep s = .trap) :
    ∃ n, 0 < n ∧ StepsHN n (decode s) [] ⟨⟨s.store, s.ambient⟩, [.TRAP]⟩ := by
  rcases s with ⟨store, ambient, frames, results⟩
  cases frames with
  | nil => simp [astep] at step
  | cons frame rest =>
    have hresults := typed.activeResults (by simp)
    change results = [] at hresults
    subst results
    have hslice := (slice.active frame (by simp)).1
    have hf : FrameTyped store frame [] := by cases typed.frames with | cons h _ => exact h
    have hr : Forall FrameWf rest := by cases typed.frames with | cons _ h => exact framesTyped_wf h
    obtain ⟨hw, hl, hv, hc⟩ := frameTyped_wf hf
    cases frame with
    | mk addr rts locals m labels code values =>
      let f : AFrame := ⟨addr, rts, locals, m, labels, code, values⟩
      cases code with
      | nil =>
        simp only [astep, returnFrame, advance] at step
        repeat' first | contradiction | split at step
      | cons op after =>
        have hop := instruction_trap_eq store ambient f rest op after (hslice op (by simp)) step
        rcases hop with rfl | ⟨descriptor, rfl⟩
        · exact unreachable_simulation store ambient f rest after typed.store typed.ambient hw hl hv
            (fun i hm => hc i (by simp [hm])) hr
        · exact Numeric.astep_trap_simulation store ambient f rest after descriptor typed step

theorem instruction_not_done (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (op : instr) (after : List instr) (allowed : SliceInstr op)
    (values : List val) :
    astep ⟨s, ambient, { f with code := op :: after } :: rest, []⟩ ≠ .done values := by
  intro step
  cases allowed
  case numeric descriptor =>
    cases descriptor
    all_goals
      simp only [Numeric.Instruction.source, Numeric.Conversion.source, astep,
        Numeric.decodeInstruction, Numeric.transition, Numeric.finish, integerBinary, advance] at step
      repeat' first | contradiction | split at step
  all_goals
    simp only [astep, advance, integerBinary, branch, enterLabel, call, returnFrame] at step
    repeat' first | contradiction | split at step

/-- A done result exposes precisely the terminal specification values. -/
theorem done_simulation (s : AState) (typed : ATyped s) (slice : SliceState s)
    (values : List val) (step : astep s = .done values) :
    decode s = ⟨⟨s.store, s.ambient⟩, vals values⟩ := by
  rcases s with ⟨store, ambient, frames, results⟩
  cases frames with
  | nil =>
    simp only [astep, AResult.done.injEq] at step
    subst results
    rfl
  | cons frame rest =>
    have hresults := typed.activeResults (by simp)
    change results = [] at hresults
    subst results
    have hslice := (slice.active frame (by simp)).1
    cases frame with
    | mk addr rts locals m labels code operands =>
      let f : AFrame := ⟨addr, rts, locals, m, labels, code, operands⟩
      cases code with
      | nil =>
        simp only [astep, returnFrame, advance] at step
        repeat' first | contradiction | split at step
      | cons op after => exact False.elim (instruction_not_done store ambient f rest op after (hslice op (by simp)) values step)

end Exec.Abs
