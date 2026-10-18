import Exec.Interp.Relations.ReferenceTransfers
import Exec.Interp.Control.StructuredNormalization
import Exec.Interp.Relations.SourceClosure

namespace Exec.Interp

/-- A source position that requires bytecode execution or function return. -/
def ReadySource (f : Abs.AFrame) : Prop :=
  match f.code with
  | [] => f.labels = []
  | .NOP :: _ | .DROP :: _ | .BLOCK _ _ :: _ => False
  | _ => True

theorem structured_normalization_choice (exec : runtime.interp.Execution) (raw : runtime.interp.Frame)
    (compiled : runtime.bytecode.CompiledFunction) (functions : List functype)
    (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (s : store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (typed : Abs.ATyped ⟨s, ambient, f :: rest, []⟩)
    (slots : FrameSlots exec raw f)
    (point : StructuredFramePoint raw f compiled functions targets next output) :
    ForwardSkip raw f compiled functions targets next output ∨
      NormalizedPoint exec raw compiled functions f ∨ ReadySource f := by
  by_cases ready : ReadySource f
  · exact Or.inr (Or.inr ready)
  have frameTyped : Abs.FrameTyped s f [] := by cases typed.frames with | cons h _ => exact h
  cases code : f.code with
  | nil =>
    cases hlabels : f.labels with
    | nil => exact False.elim (ready (by simp [ReadySource, code, hlabels]))
    | cons label labels =>
      have same : { f with code := [], labels := label :: labels } = f := by rw [← code, ← hlabels]
      have choice := structured_label_normalizes exec raw compiled functions targets next output
        s ambient f rest label labels (by simpa only [same] using typed) slots (by simpa only [same] using point)
      simpa only [same] using choice.imp_right Or.inl
  | cons head after =>
    have same : { f with code := head :: after } = f := by rw [← code]
    cases head <;> try { solve | apply False.elim; apply ready; simp [ReadySource, code] }
    case NOP =>
      have choice := structured_nop_normalizes exec raw compiled functions targets next output f after
        slots (by simpa only [same] using point)
      simpa only [same] using choice.imp_right Or.inl
    case DROP =>
      have choice := structured_drop_normalizes exec raw compiled functions targets next output s f after
        (by simpa only [same] using frameTyped) slots (by simpa only [same] using point)
      simpa only [same] using choice.imp_right Or.inl
    case BLOCK bt body =>
      have choice := structured_block_normalizes exec raw compiled functions targets next output s ambient f rest bt body after
        (by simpa only [same] using typed) slots (by simpa only [same] using point)
      simpa only [same] using choice.imp_right Or.inl

theorem ErasedStep.metadata {before after} (step : ErasedStep before after) : FrameMetadata before after := by
  cases step <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem FrameMetadata.trans {before middle after}
    (first : FrameMetadata before middle) (second : FrameMetadata middle after) : FrameMetadata before after :=
  ⟨second.address.trans first.address, second.module.trans first.module,
    second.results.trans first.results, second.locals.trans first.locals⟩

theorem ErasedSteps.metadata {count before after} (steps : ErasedSteps count before after) : FrameMetadata before after := by
  induction steps with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | cons step tail ih => exact step.metadata.trans ih

/-- Source-only normalization reaches either a retained forward jump or a
bytecode-bearing source position after a bounded finite number of reductions. -/
theorem structured_normalize (exec : runtime.interp.Execution) (raw : runtime.interp.Frame)
    (compiled : runtime.bytecode.CompiledFunction) (functions : List functype)
    (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (s : store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (typed : Abs.ATyped ⟨s, ambient, f :: rest, []⟩)
    (slots : FrameSlots exec raw f)
    (point : StructuredFramePoint raw f compiled functions targets next output) :
    ∃ count g targets' next' output', ErasedSteps count f g ∧
      count + normalizationMeasure g ≤ normalizationMeasure f ∧
      FrameSlots exec raw g ∧
      StructuredFramePoint raw g compiled functions targets' next' output' ∧
      Abs.ATyped ⟨s, ambient, g :: rest, []⟩ ∧ FrameMetadata f g ∧
      (ForwardSkip raw g compiled functions targets' next' output' ∨ ReadySource g) := by
  induction measure : normalizationMeasure f using Nat.strong_induction_on
      generalizing f targets next output with
  | h measure ih =>
    rcases structured_normalization_choice exec raw compiled functions targets next output s ambient f rest typed slots point with
      skip | ⟨g, targets', next', output', step, represented, continuation⟩ | ready
    · exact ⟨0, f, targets, next, output, .nil f, by omega, slots, point, typed,
        ⟨rfl, rfl, rfl, rfl⟩, Or.inl skip⟩
    · have nextTyped := (step.sound s ambient rest typed).1
      obtain ⟨count, final, labels, finish, results, steps, bound, represented, continuation, finalTyped, metadata, done⟩ :=
        ih (normalizationMeasure g) (by have := step.decreases; omega) targets' next' output' g nextTyped represented continuation rfl
      have chain := ErasedSteps.cons step steps
      exact ⟨count + 1, final, labels, finish, results, chain, by simpa only [measure] using chain.bound, represented, continuation,
        finalTyped, step.metadata.trans metadata, done⟩
    · exact ⟨0, f, targets, next, output, .nil f, by omega, slots, point, typed,
        ⟨rfl, rfl, rfl, rfl⟩, Or.inr ready⟩

theorem ErasedStep.closure {before after} (step : ErasedStep before after) : SourceClosure before after := by
  cases step with
  | nop f after => exact .tail _ _ _ _ _ (fun _ h => h)
  | drop f after front value => exact .tail { f with vals := front ++ [value] } .DROP after f.locals front (fun bound h => ⟨h.1, (Abs.valuesBound_append.mp h.2).1⟩)
  | block f bt body after front params results signature shape => exact .block _ _ _ _ _ _
  | label f label labels => exact .label _ _ _

theorem ErasedSteps.closure {count before after} (steps : ErasedSteps count before after) : SourceClosure before after := by
  induction steps with
  | nil => exact .refl _
  | cons step tail ih => exact step.closure.trans ih

theorem structured_normalize_slice (exec : runtime.interp.Execution) (raw : runtime.interp.Frame)
    (compiled : runtime.bytecode.CompiledFunction) (functions : List functype)
    (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (s : store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (typed : Abs.ATyped ⟨s, ambient, f :: rest, []⟩)
    (slice : Abs.SliceState ⟨s, ambient, f :: rest, []⟩)
    (slots : FrameSlots exec raw f)
    (point : StructuredFramePoint raw f compiled functions targets next output) :
    ∃ count g targets' next' output', ErasedSteps count f g ∧
      count + normalizationMeasure g ≤ normalizationMeasure f ∧
      FrameSlots exec raw g ∧
      StructuredFramePoint raw g compiled functions targets' next' output' ∧
      Abs.ATyped ⟨s, ambient, g :: rest, []⟩ ∧ Abs.SliceState ⟨s, ambient, g :: rest, []⟩ ∧
      FrameMetadata f g ∧
      (ForwardSkip raw g compiled functions targets' next' output' ∨ ReadySource g) := by
  obtain ⟨count, g, targets', next', output', chain, bound, represented, continuation, nextTyped, metadata, done⟩ :=
    structured_normalize exec raw compiled functions targets next output s ambient f rest typed slots point
  exact ⟨count, g, targets', next', output', chain, bound, represented, continuation,
    nextTyped, chain.closure.slice slice, metadata, done⟩

end Exec.Interp
