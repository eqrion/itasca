import Exec.Interp.Machines.Uniform.UniformSourceControl
import Exec.Interp.Control.BranchCondition
namespace Exec.Interp
open Aeneas.Std SpecExt Exec.Spec

/-- A fused conditional branch always performs the source test and, when
selected, the positive branch transfer. -/
theorem branchIf_source_positive (s : _root_.store) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (after : List instr) (depth : Nat) (label : Abs.Label) (front discarded results : List val) (value : Nat)
    (bound : value < 2 ^ 32) (lookup : f.labels[depth]? = some label)
    (height : label.height = front.length) (arity : label.arity = results.length)
    (types : results.map Abs.valueType = label.branchTypes)
    (typed : Abs.ATyped ⟨s, ambient, { f with code := .BR_IF (.mk_uN depth) :: after, vals := front ++ discarded ++ results ++ [Abs.integerVal .I32 value] } :: rest, []⟩) :
    ∃ count, 0 < count ∧ StepsHN count
      (Abs.decode ⟨s, ambient, { f with code := .BR_IF (.mk_uN depth) :: after, vals := front ++ discarded ++ results ++ [Abs.integerVal .I32 value] } :: rest, []⟩)
      [] (Abs.decode ⟨s, ambient, branchIfFrame f after depth label front discarded results value :: rest, []⟩) := by
  have step := branchIf_source_step s ambient f rest after depth (front ++ discarded ++ results) value bound
  have typedNext := Abs.instruction_preservation s ambient
    { f with vals := front ++ discarded ++ results ++ [Abs.integerVal .I32 value] } rest
    (.BR_IF (.mk_uN depth)) after _ (.br_if _) typed step
  have first := Abs.typed_br_if_positive s ambient
    { f with vals := front ++ discarded ++ results ++ [Abs.integerVal .I32 value] } rest
    after depth _ typed step
  have counted := StepsHN.cons first (StepsHN.refl (stepH_wf first).2)
  by_cases zero : value = 0
  · refine ⟨1,by omega,?_⟩
    simpa only [branchIfFrame,if_pos zero,List.nil_append] using counted
  · simp only [if_neg zero] at typedNext counted
    have branch := branch_source_step s ambient f rest after depth label front discarded results lookup height arity types
    have branchCounted := Abs.typed_branch_simulation s ambient { f with vals := front ++ discarded ++ results } rest
      after depth _ typedNext branch
    refine ⟨1+(depth+1),by omega,?_⟩
    simpa only [branchIfFrame,if_neg zero,List.nil_append] using counted.trans branchCounted
end Exec.Interp
