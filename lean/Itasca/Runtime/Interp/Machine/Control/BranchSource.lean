import Itasca.Runtime.Interp.Machine.Control.UniformSource
import Itasca.Runtime.Interp.Control.BranchCondition

/-!
A fused conditional branch always performs the source test and, when selected, the positive branch transfer.

Main declarations: `branch_if_source_positive`. A direct consumer is `Interp.Machine.Control.BranchIfOwned`.
-/

namespace Itasca.Runtime.Interp
open Aeneas.Std SpecExt Itasca.Runtime.Spec

/-- A fused conditional branch always performs the source test and, when
selected, the positive branch transfer. -/
theorem branch_if_source_positive (s : _root_.store) (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (after : List instr) (depth : Nat) (label : SourceMachine.Label) (front discarded results : List val) (value : Nat)
    (bound : value < 2 ^ 32) (lookup : f.labels[depth]? = some label)
    (height : label.height = front.length) (arity : label.arity = results.length)
    (types : results.map SourceMachine.valueType = label.branchTypes)
    (typed : SourceMachine.ATyped ⟨s, ambient, { f with code := .BR_IF (.mk_uN depth) :: after, vals := front ++ discarded ++ results ++ [SourceMachine.integerVal .I32 value] } :: rest, []⟩) :
    ∃ count, 0 < count ∧ StepsHN count
      (SourceMachine.decode ⟨s, ambient, { f with code := .BR_IF (.mk_uN depth) :: after, vals := front ++ discarded ++ results ++ [SourceMachine.integerVal .I32 value] } :: rest, []⟩)
      [] (SourceMachine.decode ⟨s, ambient, branchIfFrame f after depth label front discarded results value :: rest, []⟩) := by
  have step := branch_if_source_step s ambient f rest after depth (front ++ discarded ++ results) value bound
  have typedNext := SourceMachine.instruction_preservation s ambient
    { f with vals := front ++ discarded ++ results ++ [SourceMachine.integerVal .I32 value] } rest
    (.BR_IF (.mk_uN depth)) after _ (.br_if _) typed step
  have first := SourceMachine.typed_br_if_positive s ambient
    { f with vals := front ++ discarded ++ results ++ [SourceMachine.integerVal .I32 value] } rest
    after depth _ typed step
  have counted := StepsHN.cons first (StepsHN.refl (step_h_wf first).2)
  by_cases zero : value = 0
  · refine ⟨1,by omega,?_⟩
    simpa only [branchIfFrame,if_pos zero,List.nil_append] using counted
  · simp only [if_neg zero] at typedNext counted
    have branch := branch_source_step s ambient f rest after depth label front discarded results lookup height arity types
    have branchCounted := SourceMachine.typed_branch_simulation s ambient { f with vals := front ++ discarded ++ results } rest
      after depth _ typedNext branch
    refine ⟨1+(depth+1),by omega,?_⟩
    simpa only [branchIfFrame,if_neg zero,List.nil_append] using counted.trans branchCounted
end Itasca.Runtime.Interp
