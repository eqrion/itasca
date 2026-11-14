import Itasca.Runtime.Interp.Machine.Retention.StatefulOwnership
import Itasca.Runtime.Interp.Machine.Simulation.CoreErasure
import Itasca.Runtime.Interp.Machine.Retention.ReturnedOwnership
import Itasca.Runtime.SourceMachine.Stateful.TableSet
import Itasca.Runtime.Interp.Machine.Coverage.SyntaxClosure
import Itasca.Runtime.SourceMachine.Supported.PureCoverage
import Itasca.Runtime.SourceMachine.Supported.CumulativeStep
import Itasca.Runtime.SourceMachine.BrTable
import Itasca.Runtime.Compiler.Body.Relations.Executable.RecordingEmission
import Itasca.Runtime.Interp.Machine.Coverage.OrdinaryHeads

/-!
Sections, each formerly its own module: SupportedControlSemantics, RecordingHeads.
-/

/-! ## SupportedControlSemantics -/

section

/-!
Source grammar, ownership and code-bound closure through control transitions.

Main declarations: `Machine.SyntaxClosure.supported` and `bound_transition`. A direct consumer is `Interp.Machine.Memory`.
-/

namespace Itasca.Runtime.Interp

theorem Machine.SyntaxClosure.supported {before after}
    (closure : Machine.SyntaxClosure before after)
    {s : store} {ambient : frame} {rest : List SourceMachine.AFrame}
    (covered : SourceMachine.SupportedState ⟨s,ambient,before::rest,[]⟩) :
    SourceMachine.SupportedState ⟨s,ambient,after::rest,[]⟩ :=
  SourceMachine.Supported.replace_frame covered (closure (covered.active _ (List.mem_cons_self ..)))

theorem ErasedStep.supported {before after : SourceMachine.AFrame} (step : ErasedStep before after)

    {s : store} {ambient : frame} {rest : List SourceMachine.AFrame}
    (covered : SourceMachine.SupportedState ⟨s,ambient,before::rest,[]⟩) :
    SourceMachine.SupportedState ⟨s,ambient,after::rest,[]⟩ := by
  cases step with
  | nop f after => exact (Machine.SyntaxClosure.tail f .NOP after f.locals f.vals).supported covered
  | drop f after front value =>
    exact (Machine.SyntaxClosure.tail {f with vals := front++[value]} .DROP after f.locals front).supported covered
  | block f bt body after front params results signature shape =>
    have current := covered.active _ (List.mem_cons_self ..)
    have bodyCovered := SourceMachine.BinaryInstr.block_body (current.1 _ (List.mem_cons_self ..))
    apply SourceMachine.Supported.replace_frame covered
    refine ⟨bodyCovered,?_⟩
    intro label member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨by intro i found; simp at found,fun i found => current.1 i (List.mem_cons_of_mem _ found)⟩
    · exact current.2 label member
  | label f label labels =>
    have current := covered.active _ (List.mem_cons_self ..)
    apply SourceMachine.Supported.replace_frame covered
    exact ⟨(current.2 label (List.mem_cons_self ..)).2,fun outer member => current.2 outer (List.mem_cons_of_mem _ member)⟩

end Itasca.Runtime.Interp

namespace Itasca.Runtime.Interp.Machine

/-- A non-erased core step of a typed supported state stays supported. -/
theorem core_step_supported {before next} (typed : SourceMachine.CoreTyped before) (covered : SourceMachine.SupportedState before)
    (step : SourceMachine.Core.step before = .next next) : SourceMachine.SupportedState next :=
  (SourceMachine.Cumulative.Step.core step (by intro h; cases h)).next_covered_supported typed covered

/-- A core step of a typed supported state preserves stateful reference ownership. -/
theorem core_step_owned {before next} (typed : SourceMachine.CoreTyped before) (covered : SourceMachine.SupportedState before)
    (step : SourceMachine.Core.step before = .next next) :
    ∀ bounds, SourceMachine.Ownership.StatefulOwned bounds before → SourceMachine.Ownership.StatefulOwned bounds next :=
  fun _ owned => (SourceMachine.Cumulative.Step.core step (by intro h; cases h)).next_owned_supported typed covered owned

/-- A core step of a typed supported state preserves source code bounds. -/
theorem core_step_bound {before next} (typed : SourceMachine.CoreTyped before) (covered : SourceMachine.SupportedState before)
    (step : SourceMachine.Core.step before = .next next) : ∀ bound, SourceMachine.CodeBound bound before → SourceMachine.CodeBound bound next :=
  fun _ bounded => (SourceMachine.Cumulative.Step.core step (by intro h; cases h)).next_bound_supported typed covered bounded

theorem erased_steps_supported {count before after s ambient rest} (steps : ErasedSteps count before after)
    (covered : SourceMachine.SupportedState ⟨s,ambient,before::rest,[]⟩) : SourceMachine.SupportedState ⟨s,ambient,after::rest,[]⟩ := by
  induction steps with
  | nil => exact covered
  | cons step tail ih => exact ih (step.supported covered)

theorem owned_transition {initial next} (typed : SourceMachine.CoreTyped initial) (covered : SourceMachine.SupportedState initial)
    (transition : initial = next ∨ SourceMachine.Core.step initial = .next next) :
    ∀ bounds, SourceMachine.Ownership.StatefulOwned bounds initial → SourceMachine.Ownership.StatefulOwned bounds next := by
  rcases transition with same | step
  · exact fun _ h => same ▸ h
  · exact core_step_owned typed covered step

theorem bound_transition {initial next} (typed : SourceMachine.CoreTyped initial) (covered : SourceMachine.SupportedState initial)
    (transition : initial = next ∨ SourceMachine.Core.step initial = .next next) :
    ∀ bound, SourceMachine.CodeBound bound initial → SourceMachine.CodeBound bound next := by
  rcases transition with same | step
  · exact fun _ h => same ▸ h
  · exact core_step_bound typed covered step
end Itasca.Runtime.Interp.Machine

end

/-! ## RecordingHeads -/

section

/-!
The source-event shape retained by recorded code heads.

Main declarations: `RecordingHeads`. A direct consumer is `Integration.Host.HostRecordingSite`.
-/

namespace Itasca.Runtime.Interp.Machine
open Aeneas.Std

class RecordingHeads (emission : ContextEmission) : Prop where
  shape : ∀{C before source emitted after}, emission C before source emitted after → Compiler.RecordingEmissionShape source emitted

instance (tables : Compiler.CompilerTables) : RecordingHeads (Compiler.ExecutableEmission tables) := ⟨Compiler.ExecutableEmission.recording_shape⟩

private theorem fragment_call_tag {code pc next emitted instruction}
    (segment : Compiler.Segment code pc emitted next)
    (fetched : code[pc]?=some instruction) (nonempty : emitted≠[]) :
    emitted.head?=some instruction := by
  cases emitted with
  | nil => contradiction
  | cons first rest =>
    have fetch := segment.fetch (index:=0) (instruction:=first) rfl
    simp only [Nat.add_zero,fetched,Option.some.injEq] at fetch
    simpa only [List.head?_cons] using congrArg some fetch.symm

/-- A ready source head can fetch a host-capable bytecode only at a direct or
indirect source call. This follows from exact emitted syntax, not a semantic
assumption about the host callback. -/
theorem code_recording_source {emission : ContextEmission} [RecordingHeads emission]
    {C returns locals code jumpTables labels stack op source pc next output instruction}
    (ready : ReadyInstruction op)
    (relation : Compiler.StructuredCode (emission C) C.TYPES C.FUNCS returns locals code jumpTables labels stack (op::source) pc next output)
    (fetched : code[pc]?=some instruction) (calls : Compiler.callTag instruction≠0) :
    (∃index : U32,op=.CALL (.mk_uN index.val)) ∨ (∃table type : U32,op=.CALL_INDIRECT (.mk_uN table.val) (.mk_uN type.val)) := by
  cases relation with
  | linear head ordinary fragment rest =>
    have shape := RecordingHeads.shape head
    have nonempty := fun empty => (show False from by
      rcases shape.1 empty with rfl | rfl <;> exact ready)
    have first := fragment_call_tag fragment fetched nonempty
    obtain ⟨direct,indirect⟩ := shape.2 _ first
    cases instruction <;> first
      | exact (calls rfl).elim
      | exact (direct _ _ rfl).elim
      | exact Or.inr (indirect _ _ _ rfl)
  | skip forward head rest => rw [head] at fetched; cases fetched; exact (calls rfl).elim
  | block => exact ready.elim
  | loop signature head bodyCode rest bounds => rw [head] at fetched; cases fetched; exact (calls rfl).elim
  | ifElse signature condition head yesCode skip noCode rest bounds => rw [head] at fetched; cases fetched; exact (calls rfl).elim
  | branch lookup live layout fragment remaining scope =>
    have first := fragment_call_tag fragment fetched (by unfold Compiler.branchInstructions; split <;> simp)
    unfold Compiler.branchInstructions Compiler.transferInstruction at first
    split at first
    · simp only [List.head?_cons,Option.some.injEq] at first
      subst instruction
      exact (calls rfl).elim
    · split at first <;> (try split at first) <;>
        simp only [List.head?_cons,Option.some.injEq] at first <;>
        subst instruction <;> exact (calls rfl).elim
  | branchIf lookup live layout condition fragment rest =>
    have first := fragment_call_tag fragment fetched (by unfold Compiler.branchIfInstructions; split <;> simp)
    unfold Compiler.branchIfInstructions at first
    split at first <;> simp only [List.head?_cons,Option.some.injEq] at first <;>
      subst instruction <;> exact (calls rfl).elim
  | call => exact Or.inl ⟨_,rfl⟩
  | unreachable head remaining scope => rw [head] at fetched; cases fetched; exact (calls rfl).elim
  | return_ source size head remaining scope => rw [head] at fetched; cases fetched; exact (calls rfl).elim
  | branchTable gate table bounds => rw [table.instruction] at fetched; cases fetched; exact (calls rfl).elim
end Itasca.Runtime.Interp.Machine

end
