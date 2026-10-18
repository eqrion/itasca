import Exec.Interp.Relations.Normalization
import Exec.Interp.Relations.ControlInversion
import Exec.Interp.Relations.ValueLookup

namespace Exec.Interp
open Aeneas.Std

/-- A retained forward administrative instruction must execute before the
source operation at its target can be normalized. -/
def ForwardSkip (raw : runtime.interp.Frame) (f : Abs.AFrame)
    (compiled : runtime.bytecode.CompiledFunction) (functions : List functype)
    (targets : List Code.LabelTarget) (next : Nat) (output : List valtype) : Prop :=
  ∃ target, raw.pc.val < target.val ∧ compiled.code.val[raw.pc.val]? = some (.Jump target) ∧
    StructuredFramePoint { raw with pc := target } f compiled functions targets next output

/-- A source-only transition retains the actual PC and live slot relation.
Its semantic preservation and finite chaining follow from ErasedStep. -/
def NormalizedPoint (exec : runtime.interp.Execution) (raw : runtime.interp.Frame)
    (compiled : runtime.bytecode.CompiledFunction) (functions : List functype)
    (before : Abs.AFrame) : Prop :=
  ∃ after targets next output,
    ErasedStep before after ∧ FrameSlots exec raw after ∧
    StructuredFramePoint raw after compiled functions targets next output

theorem structured_nop_normalizes (exec : runtime.interp.Execution) (raw : runtime.interp.Frame)
    (compiled : runtime.bytecode.CompiledFunction) (functions : List functype)
    (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (f : Abs.AFrame) (after : List instr)
    (slots : FrameSlots exec raw f)
    (point : StructuredFramePoint raw { f with code := .NOP :: after } compiled functions targets next output) :
    ForwardSkip raw { f with code := .NOP :: after } compiled functions targets next output ∨
    NormalizedPoint exec raw compiled functions { f with code := .NOP :: after } := by
  rcases codeRel_linear_inv (by rfl) point.code.current with skip | linear
  · obtain ⟨target, forward, fetched, continuation⟩ := skip
    exact Or.inl ⟨target, forward, fetched, point.labels, continuation, point.code.targets, point.code.normal, point.code.exit, point.code.root⟩
  · obtain ⟨middle, emitted, tail, head, fragment, continuation⟩ := linear
    obtain ⟨rfl, rfl⟩ := linearEmission_nop_inv head
    have endpoint : tail = raw.pc.val := by obtain ⟨_, _, _, _, h⟩ := fragment; simpa using h
    exact Or.inr ⟨{ f with code := after }, targets, next, output, .nop f after, slots,
      point.labels, by simpa only [endpoint] using continuation, point.code.targets, point.code.normal, point.code.exit, point.code.root⟩

theorem structured_drop_normalizes (exec : runtime.interp.Execution) (raw : runtime.interp.Frame)
    (compiled : runtime.bytecode.CompiledFunction) (functions : List functype)
    (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (s : store) (f : Abs.AFrame) (after : List instr)
    (typed : Abs.FrameTyped s { f with code := .DROP :: after } [])
    (slots : FrameSlots exec raw f)
    (point : StructuredFramePoint raw { f with code := .DROP :: after } compiled functions targets next output) :
    ForwardSkip raw { f with code := .DROP :: after } compiled functions targets next output ∨
    NormalizedPoint exec raw compiled functions { f with code := .DROP :: after } := by
  rcases codeRel_linear_inv (by rfl) point.code.current with skip | linear
  · obtain ⟨target, forward, fetched, continuation⟩ := skip
    exact Or.inl ⟨target, forward, fetched, point.labels, continuation, point.code.targets, point.code.normal, point.code.exit, point.code.root⟩
  · obtain ⟨middle, emitted, tail, head, fragment, continuation⟩ := linear
    obtain ⟨stack, ty, shape, middleEq, emittedEq⟩ := linearEmission_drop_inv head
    obtain ⟨front, value, split, frontTypes, valueType⟩ := values_type_suffix f.vals stack ty shape
    have endpoint : tail = raw.pc.val := by
      obtain ⟨_, _, _, _, h⟩ := fragment
      simpa only [emittedEq, List.length_nil, Nat.add_zero] using h
    have heights := frame_linear_heights typed (by rfl) front (by simp only [split, List.length_append, List.length_singleton, linearInputs])
    have labels : LabelsMatch (front ++ [value]) f.labels targets := by simpa only [← split] using point.labels
    have labelsAfter : LabelsMatch front f.labels targets := by
      simpa only [List.append_nil] using labels.replace_suffix (after := []) heights
    have values : ValuesAt exec.slots.val raw.base.val ((f.locals ++ front) ++ [value]) := by
      simpa only [FrameSlots, split, List.append_assoc] using slots
    refine Or.inr ⟨{ f with code := after, vals := front }, targets, next, output,
      ?_, values.locals, labelsAfter, ?_, point.code.targets, point.code.normal, point.code.exit, point.code.root⟩
    · simpa only [← split] using ErasedStep.drop f after front value
    · simpa only [middleEq, endpoint, frontTypes] using continuation

theorem structured_block_normalizes (exec : runtime.interp.Execution) (raw : runtime.interp.Frame)
    (compiled : runtime.bytecode.CompiledFunction) (functions : List functype)
    (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (s : store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (bt : blocktype) (body after : List instr)
    (typed : Abs.ATyped ⟨s, ambient, { f with code := .BLOCK bt body :: after } :: rest, []⟩)
    (slots : FrameSlots exec raw f)
    (point : StructuredFramePoint raw { f with code := .BLOCK bt body :: after } compiled functions targets next output) :
    ForwardSkip raw { f with code := .BLOCK bt body :: after } compiled functions targets next output ∨
    NormalizedPoint exec raw compiled functions { f with code := .BLOCK bt body :: after } := by
  rcases codeRel_block_inv point.code.current with skip | block
  · obtain ⟨target, forward, fetched, continuation⟩ := skip
    exact Or.inl ⟨target, forward, fetched, point.labels, continuation, point.code.targets, point.code.normal, point.code.exit, point.code.root⟩
  · obtain ⟨front, params, results, normalExit, branchExit, normalLive, branchLive, shape, signature, bodyCode, normal, branch, bounds⟩ := block
    obtain ⟨represented, continuation, _, _⟩ := block_entry_point exec raw compiled functions targets next output
      s ambient f rest bt body after front params results normalExit branchExit normalLive branchLive typed slots point shape signature bodyCode normal branch
    exact Or.inr ⟨_, _, _, _, .block f bt body after front params results signature shape, represented, continuation⟩

theorem structured_label_normalizes (exec : runtime.interp.Execution) (raw : runtime.interp.Frame)
    (compiled : runtime.bytecode.CompiledFunction) (functions : List functype)
    (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (s : store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (label : Abs.Label) (labels : List Abs.Label)
    (typed : Abs.ATyped ⟨s, ambient, { f with code := [], labels := label :: labels } :: rest, []⟩)
    (slots : FrameSlots exec raw f)
    (point : StructuredFramePoint raw { f with code := [], labels := label :: labels } compiled functions targets next output) :
    ForwardSkip raw { f with code := [], labels := label :: labels } compiled functions targets next output ∨
    NormalizedPoint exec raw compiled functions { f with code := [], labels := label :: labels } := by
  rcases codeRel_empty_inv point.code.current with skip | empty
  · obtain ⟨target, forward, fetched, continuation⟩ := skip
    exact Or.inl ⟨target, forward, fetched, point.labels, continuation, point.code.targets, point.code.normal, point.code.exit, point.code.root⟩
  · obtain ⟨next', output', represented, continuation, _, _⟩ :=
      label_completion_point exec raw compiled functions targets next output s ambient f rest label labels typed slots point empty.1 empty.2.2
    exact Or.inr ⟨_, _, next', output', .label f label labels, represented, continuation⟩

end Exec.Interp
