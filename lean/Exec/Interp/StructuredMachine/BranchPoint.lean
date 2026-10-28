import Exec.Interp.StructuredMachine.Point
namespace Itasca.Runtime.Interp.StructuredMachine
open Aeneas.Std
/-- Target lookup exposes the retained source continuation, with concrete
label fields obtained from the dynamic/static label correspondence. -/
theorem FramePoint.target {s raw frame compiled C targets next output}
    (point : FramePoint s raw frame compiled C targets next output)
    (depth : Nat) (label : Abs.Label) (lookup : frame.labels[depth]? = some label)
    (live : ∀ target, targets[depth]? = some target → target.branchLive = true) :
    ∃ target targetNext targetOutput,
      targets[depth]? = some target ∧ LabelMatch frame.vals label target ∧
      Code.StructuredCode.Point (emission compiled C) C.TYPES C.FUNCS frame.resultTypes
        C.LOCALS compiled.code.val compiled.jump_tables.val (targets.drop (depth + 1))
        (target.front ++ label.branchTypes) (label.cont ++ label.after)
        target.target.val targetNext targetOutput := by
  obtain ⟨target, found, matching⟩ := point.labels.atIndex depth label lookup
  obtain ⟨targetNext, targetOutput, continuation, aligned, root⟩ := point.code.targets depth target found (live target found)
  refine ⟨target, targetNext, targetOutput, found, matching, ?_⟩
  exact ⟨by simpa only [matching.branchTypes, matching.cont, matching.after] using continuation,
    point.code.targets.drop (depth + 1), point.code.normal.drop (depth + 1), aligned, root⟩

/-- A typed source branch preserves the surviving dynamic/static label
correspondence and installs the exact retained target continuation. -/
theorem FramePoint.branch {s : _root_.store} {raw : runtime.interp.Frame}
    {f : Abs.AFrame} {compiled : runtime.bytecode.CompiledFunction}
    {C : context} {targets : List Code.LabelTarget} {next : Nat} {output : List valtype}
    (front discarded results : List val)
    (point : FramePoint s raw { f with vals := front ++ discarded ++ results } compiled C targets next output)
    (typed : Abs.FrameTyped s { f with vals := front ++ discarded ++ results } [])
    (depth : Nat) (label : Abs.Label) (lookup : f.labels[depth]? = some label)
    (height : label.height = front.length) (types : results.map Abs.valueType = label.branchTypes)
    (live : ∀ target, targets[depth]? = some target → target.branchLive = true) :
    ∃ target targetNext targetOutput,
      targets[depth]? = some target ∧ LabelMatch (front ++ discarded ++ results) label target ∧
      FramePoint s { raw with pc := target.target }
        { f with code := label.cont ++ label.after, labels := f.labels.drop (depth + 1), vals := front ++ results }
        compiled C (targets.drop (depth + 1)) targetNext targetOutput := by
  obtain ⟨target, targetNext, targetOutput, found, matching, continuation⟩ := point.target depth label lookup live
  have frontTypes : target.front = front.map Code.valueType := by
    simpa only [height, List.append_assoc, List.take_left] using matching.front
  have resultTypes : results.map Code.valueType = label.branchTypes := by
    simpa only [show Code.valueType = Abs.valueType from funext valueType_eq_abs] using types
  have outer := typed.outer_heights depth label lookup
  have labels := point.labels.branch depth (by simpa only [height] using outer)
  refine ⟨target, targetNext, targetOutput, found, matching, ⟨point.bindings,point.locals,labels, ?_⟩⟩
  simpa only [List.map_append, resultTypes, frontTypes] using continuation

theorem branch_target_point {s : _root_.store} {raw : runtime.interp.Frame}
    {f : Abs.AFrame} {compiled : runtime.bytecode.CompiledFunction}
    {C : context} {targets : List Code.LabelTarget}
    (front discarded results : List val)
    (bindings : Abs.ModuleBindings s f.module C) (locals : C.LOCALS = f.locals.map Code.valueType)
    (matchingLabels : LabelsMatch (front ++ discarded ++ results) f.labels targets)
    (continuations : Code.StructuredCode.Targets (emission compiled C) C.TYPES C.FUNCS f.resultTypes
      C.LOCALS compiled.code.val compiled.jump_tables.val targets)
    (normal : Code.StructuredCode.Normals (emission compiled C) C.TYPES C.FUNCS f.resultTypes
      C.LOCALS compiled.code.val compiled.jump_tables.val targets)
    (typed : Abs.FrameTyped s { f with vals := front ++ discarded ++ results } [])
    (depth : Nat) (label : Abs.Label) (lookup : f.labels[depth]? = some label)
    (height : label.height = front.length) (types : results.map Abs.valueType = label.branchTypes)
    (live : ∀ target, targets[depth]? = some target → target.branchLive = true) :
    ∃ target targetNext targetOutput,
      targets[depth]? = some target ∧ LabelMatch (front ++ discarded ++ results) label target ∧
      FramePoint s { raw with pc := target.target }
        { f with code := label.cont ++ label.after, labels := f.labels.drop (depth + 1), vals := front ++ results }
        compiled C (targets.drop (depth + 1)) targetNext targetOutput := by
  obtain ⟨target, found, matching⟩ := matchingLabels.atIndex depth label lookup
  obtain ⟨targetNext, targetOutput, relation, aligned, root⟩ := continuations depth target found (live target found)
  have continuation : Code.StructuredCode.Point (emission compiled C) C.TYPES C.FUNCS f.resultTypes
      C.LOCALS compiled.code.val compiled.jump_tables.val (targets.drop (depth + 1))
      (target.front ++ label.branchTypes) (label.cont ++ label.after) target.target.val targetNext targetOutput :=
    ⟨by simpa only [matching.branchTypes, matching.cont, matching.after] using relation,
      continuations.drop (depth + 1), normal.drop (depth + 1), aligned, root⟩
  have frontTypes : target.front = front.map Code.valueType := by
    simpa only [height, List.append_assoc, List.take_left] using matching.front
  have resultTypes : results.map Code.valueType = label.branchTypes := by
    simpa only [show Code.valueType = Abs.valueType from funext valueType_eq_abs] using types
  have outer := typed.outer_heights depth label lookup
  have labels := matchingLabels.branch depth (by simpa only [height] using outer)
  refine ⟨target, targetNext, targetOutput, found, matching, ⟨bindings,locals,labels, ?_⟩⟩
  simpa only [List.map_append, resultTypes, frontTypes] using continuation

end Itasca.Runtime.Interp.StructuredMachine
