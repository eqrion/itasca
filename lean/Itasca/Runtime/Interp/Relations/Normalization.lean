import Itasca.Runtime.Interp.Relations.ControlEntry
import Itasca.Runtime.Interp.Control.LabelCompletion
import Itasca.Runtime.Interp.Relations.Erased
import Itasca.Runtime.SourceMachine.Sim.Compose

namespace Itasca.Runtime.Interp

/-- The saved normal continuations are counted once, alongside the active
source code. Entering nested blocks and completing labels both decrease this
measure, even when block entry enlarges the active instruction list. -/
noncomputable def normalContinuationSize : List SourceMachine.Label → Nat
  | [] => 0
  | label :: labels => 1 + sizeOf label.after + normalContinuationSize labels

noncomputable def normalizationMeasure (f : SourceMachine.AFrame) : Nat :=
  sizeOf f.code + normalContinuationSize f.labels

/-- Source-only operations omitted by slot bytecode. The BLOCK constructor
retains its actual signature and operand type shape; label completion is
validated from generated typing when the relation is used. -/
inductive ErasedStep : SourceMachine.AFrame → SourceMachine.AFrame → Prop where
  | nop (f : SourceMachine.AFrame) (after : List instr) :
      ErasedStep { f with code := .NOP :: after } { f with code := after }
  | drop (f : SourceMachine.AFrame) (after : List instr) (front : List val) (value : val) :
      ErasedStep { f with code := .DROP :: after, vals := front ++ [value] }
        { f with code := after, vals := front }
  | block (f : SourceMachine.AFrame) (bt : blocktype) (body after : List instr) (front params results : List valtype)
      (signature : Compiler.BlockSignature f.module.TYPES bt params results)
      (shape : f.vals.map Compiler.valueType = front ++ params) :
      ErasedStep { f with code := .BLOCK bt body :: after }
        { f with code := body, labels := ⟨results, results, [], front.length, after⟩ :: f.labels }
  | label (f : SourceMachine.AFrame) (label : SourceMachine.Label) (labels : List SourceMachine.Label) :
      ErasedStep { f with code := [], labels := label :: labels }
        { f with code := label.after, labels := labels }

theorem ErasedStep.decreases {before after : SourceMachine.AFrame} (step : ErasedStep before after) :
    normalizationMeasure after < normalizationMeasure before := by
  cases step <;> simp [normalizationMeasure, normalContinuationSize] <;> omega

theorem ErasedStep.sound {before after : SourceMachine.AFrame} (step : ErasedStep before after)
    (s : store) (ambient : frame) (rest : List SourceMachine.AFrame)
    (typed : SourceMachine.ATyped ⟨s, ambient, before :: rest, []⟩) :
    SourceMachine.ATyped ⟨s, ambient, after :: rest, []⟩ ∧
    SourceMachine.NextSim ⟨s, ambient, before :: rest, []⟩ ⟨s, ambient, after :: rest, []⟩ := by
  cases step with
  | nop f after =>
    have source : SourceMachine.astep ⟨s, ambient, { f with code := .NOP :: after } :: rest, []⟩ =
        .next ⟨s, ambient, { f with code := after } :: rest, []⟩ := rfl
    exact ⟨SourceMachine.instruction_preservation s ambient f rest .NOP after _ .nop typed source,
      SourceMachine.instruction_simulation s ambient f rest .NOP after _ .nop typed source⟩
  | drop f after front value =>
    have source : SourceMachine.astep
        ⟨s, ambient, { f with code := .DROP :: after, vals := front ++ [value] } :: rest, []⟩ =
        .next ⟨s, ambient, { f with code := after, vals := front } :: rest, []⟩ := by
      simp only [SourceMachine.astep, SourceMachine.pop_append, SourceMachine.advance]
    exact ⟨SourceMachine.instruction_preservation s ambient { f with vals := front ++ [value] } rest .DROP after _ .drop typed source,
      SourceMachine.instruction_simulation s ambient { f with vals := front ++ [value] } rest .DROP after _ .drop typed source⟩
  | block f bt body after front params results signature shape =>
    have source := block_source_step s ambient f rest bt body after front params results signature shape
    exact ⟨SourceMachine.block_preservation s ambient f rest after bt body _ typed source,
      SourceMachine.typed_block_simulation s ambient f rest after bt body _ typed source⟩
  | label f label labels =>
    have hf : SourceMachine.FrameTyped s { f with code := [], labels := label :: labels } [] := by
      cases typed.frames with | cons h _ => exact h
    have source := (typed_label_completion s ambient f rest label labels hf).2.2
    exact ⟨SourceMachine.active_frame_preservation typed (SourceMachine.label_exit_frame_preservation hf) rfl,
      SourceMachine.typed_label_end_simulation s ambient f rest label labels _ typed source⟩

inductive ErasedSteps : Nat → SourceMachine.AFrame → SourceMachine.AFrame → Prop where
  | nil (f) : ErasedSteps 0 f f
  | cons {count before middle after} :
      ErasedStep before middle → ErasedSteps count middle after → ErasedSteps (count + 1) before after

theorem ErasedSteps.bound {count before after} (steps : ErasedSteps count before after) :
    count + normalizationMeasure after ≤ normalizationMeasure before := by
  induction steps with
  | nil => omega
  | cons step tail ih => have decrease := step.decreases; omega

/-- Typed normalization chains compose their checked source simulations. The
empty chain is represented explicitly rather than inventing a positive step. -/
theorem ErasedSteps.sound {count before after} (steps : ErasedSteps count before after)
    (s : store) (ambient : frame) (rest : List SourceMachine.AFrame)
    (typed : SourceMachine.ATyped ⟨s, ambient, before :: rest, []⟩) :
    SourceMachine.ATyped ⟨s, ambient, after :: rest, []⟩ ∧
      ((count = 0 ∧ before = after) ∨
       SourceMachine.NextSim ⟨s, ambient, before :: rest, []⟩ ⟨s, ambient, after :: rest, []⟩) := by
  induction steps with
  | nil => exact ⟨typed, Or.inl ⟨rfl, rfl⟩⟩
  | cons step tail ih =>
    obtain ⟨middleTyped, first⟩ := step.sound s ambient rest typed
    obtain ⟨afterTyped, zero | remaining⟩ := ih middleTyped
    · obtain ⟨_, same⟩ := zero
      subst same
      exact ⟨afterTyped, Or.inr first⟩
    · exact ⟨afterTyped, Or.inr (first.trans remaining)⟩

end Itasca.Runtime.Interp
