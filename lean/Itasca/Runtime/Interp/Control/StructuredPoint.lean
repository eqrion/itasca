import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredComposition
import Itasca.Runtime.Interp.Relations.Rel
import Itasca.Runtime.SourceMachine.LabelHeights

namespace Itasca.Runtime.Interp
open Aeneas.Std

/-- Function identity and local layout survive ordinary instruction steps. -/
structure FrameMetadata (before after : SourceMachine.AFrame) : Prop where
  address : after.fa = before.fa
  module : after.module = before.module
  results : after.resultTypes = before.resultTypes
  locals : after.locals.map Compiler.valueType = before.locals.map Compiler.valueType

theorem value_type_eq_abs (value : val) : Compiler.valueType value = SourceMachine.valueType value := by
  cases value with
  | REF_NULL rt => cases rt <;> rfl
  | _ => rfl

/-- Each compiler label records the actual saved operand prefix and source
continuation of its abstract-machine counterpart. -/
structure LabelMatch (values : List val) (label : SourceMachine.Label) (target : Compiler.LabelTarget) : Prop where
  front : target.front = (values.take label.height).map Compiler.valueType
  height : target.front.length = label.height
  branchTypes : target.branchTypes = label.branchTypes
  resultTypes : target.resultTypes = label.resultTypes
  cont : target.cont = label.cont
  after : target.after = label.after

/-- Labels use the same innermost-first indexing on both sides. -/
structure LabelsMatch (values : List val) (labels : List SourceMachine.Label) (targets : List Compiler.LabelTarget) : Prop where
  length : labels.length = targets.length
  atIndex : ∀ (depth : Nat) (label : SourceMachine.Label), labels[depth]? = some label →
    ∃ target, targets[depth]? = some target ∧ LabelMatch values label target

theorem LabelsMatch.static_lookup {values labels targets}
    (h : LabelsMatch values labels targets) (depth : Nat) (target : Compiler.LabelTarget)
    (lookup : targets[depth]? = some target) :
    ∃ label, labels[depth]? = some label ∧ LabelMatch values label target := by
  have bound : depth < labels.length := by
    rw [h.length]
    exact List.getElem?_eq_some_iff.mp lookup |>.1
  have found : labels[depth]? = some labels[depth] := List.getElem?_eq_getElem bound
  obtain ⟨actual, actualAt, matching⟩ := h.atIndex depth labels[depth] found
  have same : actual = target := Option.some.inj (actualAt.symm.trans lookup)
  subst actual
  exact ⟨labels[depth], found, matching⟩

/-- Static branch stack decomposition determines concrete value intervals and
all transfer slots; no dynamic result correspondence is inserted as a premise. -/
theorem LabelsMatch.branch_layout {values labels targets} (locals : List val)
    (h : LabelsMatch values labels targets) (depth : Nat) (target : Compiler.LabelTarget)
    (lookup : targets[depth]? = some target) (dst src count : U32)
    (layout : Compiler.BranchLayout (locals.map Compiler.valueType) (values.map Compiler.valueType) target dst src count) :
    ∃ label front discarded results,
      labels[depth]? = some label ∧ LabelMatch values label target ∧
      values = front ++ discarded ++ results ∧ label.height = front.length ∧
      label.arity = results.length ∧ results.map SourceMachine.valueType = label.branchTypes ∧
      dst.val = Compiler.slots ((locals ++ front).map Compiler.valueType) ∧
      src.val = Compiler.slots ((locals ++ front ++ discarded).map Compiler.valueType) ∧
      count.val = Compiler.slots (results.map Compiler.valueType) := by
  obtain ⟨label, found, matching⟩ := h.static_lookup depth target lookup
  obtain ⟨discardedTypes, stackTypes, destination, source, size⟩ := layout
  obtain ⟨initial, results, valuesSplit, initialTypes, resultTypes⟩ := List.map_eq_append_iff.mp stackTypes
  obtain ⟨front, discarded, initialSplit, frontTypes, discardedType⟩ := List.map_eq_append_iff.mp initialTypes
  have frontLength : front.length = label.height := by
    have equal := congrArg List.length frontTypes
    simpa only [List.length_map, matching.height] using equal
  have resultLength : results.length = label.arity := by
    have equal := congrArg List.length resultTypes
    simpa only [List.length_map, matching.branchTypes, SourceMachine.Label.arity] using equal
  have types : results.map SourceMachine.valueType = label.branchTypes := by
    simpa only [show Compiler.valueType = SourceMachine.valueType from funext value_type_eq_abs, matching.branchTypes] using resultTypes
  refine ⟨label, front, discarded, results, found, matching, ?_, frontLength.symm, resultLength.symm, types, ?_, ?_, ?_⟩
  · simpa only [initialSplit] using valuesSplit
  · simpa only [List.map_append, Compiler.slots_append, frontTypes] using destination
  · simpa only [List.map_append, Compiler.slots_append, frontTypes, discardedType, Nat.add_assoc] using source
  · simpa only [resultTypes] using size

theorem LabelsMatch.drop {values labels targets} (h : LabelsMatch values labels targets) (count : Nat) :
    LabelsMatch values (labels.drop count) (targets.drop count) := by
  constructor
  · simp only [List.length_drop, h.length]
  · intro depth label lookup
    have original : labels[count + depth]? = some label := by simpa using lookup
    obtain ⟨target, found, matching⟩ := h.atIndex (count + depth) label original
    exact ⟨target, by simpa using found, matching⟩

theorem LabelMatch.reprefix {before after : List val} {label target}
    (h : LabelMatch before label target)
    (same : before.take label.height = after.take label.height) : LabelMatch after label target :=
  { h with front := h.front.trans (congrArg (List.map Compiler.valueType) same) }

theorem LabelsMatch.reprefix {before after : List val} {labels targets}
    (h : LabelsMatch before labels targets)
    (same : ∀ label ∈ labels, before.take label.height = after.take label.height) :
    LabelsMatch after labels targets := by
  refine ⟨h.length, ?_⟩
  intro depth label lookup
  obtain ⟨target, found, matching⟩ := h.atIndex depth label lookup
  exact ⟨target, found, matching.reprefix (same label (List.mem_of_getElem? lookup))⟩

theorem LabelsMatch.replace_suffix {front before after : List val} {labels targets}
    (h : LabelsMatch (front ++ before) labels targets)
    (heights : ∀ label ∈ labels, label.height ≤ front.length) :
    LabelsMatch (front ++ after) labels targets := by
  apply h.reprefix
  intro label member
  simp only [List.take_append_of_le_length (heights label member)]

/-- A branch only changes operand words at or above its target height. The
source typing invariant supplies the nesting bound for all surviving labels. -/
theorem LabelsMatch.branch {front discarded results : List val} {labels targets}
    (h : LabelsMatch (front ++ discarded ++ results) labels targets) (depth : Nat)
    (heights : ∀ label ∈ labels.drop (depth + 1), label.height ≤ front.length) :
    LabelsMatch (front ++ results) (labels.drop (depth + 1)) (targets.drop (depth + 1)) := by
  apply (h.drop (depth + 1)).reprefix
  intro label member
  have bound := heights label member
  simp only [List.append_assoc, List.take_append_of_le_length bound]

end Itasca.Runtime.Interp
