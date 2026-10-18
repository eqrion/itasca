import Exec.Interp.Relations.ReferenceTransfers
import Exec.Interp.StructuredMachine.Normalization
import Exec.Interp.Core.Erased
import Exec.Interp.Relations.SourceClosure
import Exec.Interp.Control.NormalizeClosure

namespace Exec.Interp.StructuredMachine

theorem normalization_choice {emission : FunctionEmission} (exec : runtime.interp.Execution) (raw : runtime.interp.Frame)
    (compiled : runtime.bytecode.CompiledFunction) [OrdinaryHeads (emission compiled)] [ErasedHeads (emission compiled)] (C : context)
    (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (s : store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (typed : Abs.CoreTyped ⟨s, ambient, f :: rest, []⟩)
    (slots : FrameSlots exec raw f)
    (point : FramePoint emission s raw f compiled C targets next output) :
    ForwardSkip emission s raw f compiled C targets next output ∨
      NormalizedPoint emission s exec raw compiled C f ∨ ReadySource f := by
  by_cases ready : ReadySource f
  · exact Or.inr (Or.inr ready)
  have frameTyped : Abs.FrameTyped s f [] := by cases typed.typed.frames with | cons h _ => exact h
  cases code : f.code with
  | nil =>
    cases hlabels : f.labels with
    | nil => exact False.elim (ready (by simp [ReadySource, code, hlabels]))
    | cons label labels =>
      have same : { f with code := [], labels := label :: labels } = f := by rw [← code, ← hlabels]
      have choice := structured_label_normalizes exec raw compiled C targets next output
        s ambient f rest label labels (by simpa only [same] using typed.typed) slots (by simpa only [same] using point)
      simpa only [same] using choice.imp_right Or.inl
  | cons head after =>
    have same : { f with code := head :: after } = f := by rw [← code]
    cases head <;> try { solve | apply False.elim; apply ready; simp [ReadySource, code] }
    case NOP =>
      have choice := structured_nop_normalizes exec raw compiled C targets next output s f after
        slots (by simpa only [same] using point)
      simpa only [same] using choice.imp_right Or.inl
    case DROP =>
      have choice := structured_drop_normalizes exec raw compiled C targets next output s f after
        (by simpa only [same] using frameTyped) slots (by simpa only [same] using point)
      simpa only [same] using choice.imp_right Or.inl
    case BLOCK bt body =>
      have choice := structured_block_normalizes exec raw compiled C targets next output s ambient f rest bt body after
        (by simpa only [same] using typed.typed) slots (by simpa only [same] using point)
      simpa only [same] using choice.imp_right Or.inl

/-- Source-only normalization reaches either a retained forward jump or a
bytecode-bearing source position after a bounded finite number of reductions. -/
theorem normalize {emission : FunctionEmission} (exec : runtime.interp.Execution) (raw : runtime.interp.Frame)
    (compiled : runtime.bytecode.CompiledFunction) [OrdinaryHeads (emission compiled)] [ErasedHeads (emission compiled)] (C : context)
    (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (s : store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (typed : Abs.CoreTyped ⟨s, ambient, f :: rest, []⟩)
    (slots : FrameSlots exec raw f)
    (point : FramePoint emission s raw f compiled C targets next output) :
    ∃ count g targets' next' output', ErasedSteps count f g ∧
      count + normalizationMeasure g ≤ normalizationMeasure f ∧
      FrameSlots exec raw g ∧
      FramePoint emission s raw g compiled C targets' next' output' ∧
      Abs.CoreTyped ⟨s, ambient, g :: rest, []⟩ ∧ FrameMetadata f g ∧
      (ForwardSkip emission s raw g compiled C targets' next' output' ∨ ReadySource g) := by
  induction measure : normalizationMeasure f using Nat.strong_induction_on
      generalizing f targets next output with
  | h measure ih =>
    rcases normalization_choice exec raw compiled C targets next output s ambient f rest typed slots point with
      skip | ⟨g, targets', next', output', step, represented, continuation⟩ | ready
    · exact ⟨0, f, targets, next, output, .nil f, by omega, slots, point, typed,
        ⟨rfl, rfl, rfl, rfl⟩, Or.inl skip⟩
    · have nextTyped := (step.core_sound s ambient rest typed).1
      obtain ⟨count, final, labels, finish, results, steps, bound, represented, continuation, finalTyped, metadata, done⟩ :=
        ih (normalizationMeasure g) (by have := step.decreases; omega) targets' next' output' g nextTyped represented continuation rfl
      have chain := ErasedSteps.cons step steps
      exact ⟨count + 1, final, labels, finish, results, chain, by simpa only [measure] using chain.bound, represented, continuation,
        finalTyped, step.metadata.trans metadata, done⟩
    · exact ⟨0, f, targets, next, output, .nil f, by omega, slots, point, typed,
        ⟨rfl, rfl, rfl, rfl⟩, Or.inr ready⟩

end Exec.Interp.StructuredMachine
