import Itasca.Runtime.Interp.Control.LabelCompletion
import Itasca.Runtime.Interp.StructuredMachine.Point
namespace Itasca.Runtime.Interp.StructuredMachine
open Aeneas Aeneas.Std
/-- Normal completion removes a source label at its retained fallthrough PC.
The concrete words and PC are unchanged; the generated source semantics takes
one positive reduction and installs the retained enclosing continuation. -/
theorem label_completion_point (exec : runtime.interp.Execution) (raw : runtime.interp.Frame)
    (compiled : runtime.bytecode.CompiledFunction) (C : context)
    (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (s : store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (label : Abs.Label) (labels : List Abs.Label)
    (typed : Abs.ATyped ⟨s, ambient, { f with code := [], labels := label :: labels } :: rest, []⟩)
    (slots : FrameSlots exec raw f)
    (point : FramePoint s raw { f with code := [], labels := label :: labels }
      compiled C targets next output)
    (atExit : raw.pc.val = next) (live : Code.NormalLive targets) :
    ∃ next' output',
      FrameSlots exec raw { f with code := label.after, labels := labels } ∧
      FramePoint s raw { f with code := label.after, labels := labels }
        compiled C (targets.drop 1) next' output' ∧
      Abs.ATyped ⟨s, ambient, { f with code := label.after, labels := labels } :: rest, []⟩ ∧
      Abs.NextSim ⟨s, ambient, { f with code := [], labels := label :: labels } :: rest, []⟩
        ⟨s, ambient, { f with code := label.after, labels := labels } :: rest, []⟩ := by
  have frameTyped : Abs.FrameTyped s { f with code := [], labels := label :: labels } [] := by
    cases typed.frames with | cons h _ => exact h
  obtain ⟨size, results, step⟩ := typed_label_completion s ambient f rest label labels frameTyped
  obtain ⟨target, lookup, matching⟩ := point.labels.atIndex 0 label (by rfl)
  have head : targets.head? = some target := by cases targets <;> simpa using lookup
  have pc : raw.pc.val = target.normalExit := atExit.trans (point.code.exit target head)
  obtain ⟨next', output', relation, aligned, root⟩ := point.code.normal 0 target lookup (live target head)
  have valueTypes : f.vals.map Code.valueType = target.front ++ target.resultTypes := by
    rw [matching.front, matching.resultTypes]
    have resultTypes : (f.vals.drop label.height).map Code.valueType = label.resultTypes := by
      simpa only [show Code.valueType = Abs.valueType from funext valueType_eq_abs] using results
    rw [← resultTypes, ← List.map_append, List.take_append_drop]
  refine ⟨next', output', slots, ⟨point.bindings,point.locals,?_, ?_⟩, ?_, ?_⟩
  · simpa only [List.drop_succ_cons, List.drop_zero] using point.labels.drop 1
  · exact ⟨by simpa only [Nat.zero_add, matching.after, pc, valueTypes] using relation,
      point.code.targets.drop 1, point.code.normal.drop 1, by simpa only [Nat.zero_add] using aligned, by simpa only [Nat.zero_add] using root⟩
  · exact Abs.active_frame_preservation typed (Abs.label_exit_frame_preservation frameTyped) rfl
  · exact Abs.typed_label_end_simulation s ambient f rest label labels _ typed step

end Itasca.Runtime.Interp.StructuredMachine
