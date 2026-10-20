import Exec.Spec.Open.WasmSegment
namespace Exec.Spec.OpenExecution
open SpecExt

/-- A completed selected run has a suffix starting at any matching completed
silent Wasm segment. Its own occurrence index is retained, so differing trap
cleanup lengths cannot shift later API choices. -/
theorem ChoiceTrace.after_quiet_boundary {H : Type} {model : HostModel H} {choices : Choices H}
    (allowed : choices.Admissible model) {occurrence total initial expected stack events last}
    (trace : ChoiceTrace model choices occurrence total
      ⟨initial.1.1,.wasm initial.1.2 initial.2 expected,stack⟩ events last)
    (held : (State.mk initial.1.1 (.wasm initial.1.2 initial.2 expected) stack).Typed)
    (completed : ∃result,last.mode=.completed result)
    {count endpoint} (actualPrefix : ChosenStepsN choices.wasm occurrence count initial [] endpoint)
    (boundary : OpenHost.QuietBoundary endpoint) :
    ∃sourceCount remaining tailEvents,
      ChoiceTrace model choices (occurrence+sourceCount) remaining
        ⟨endpoint.1.1,.wasm endpoint.1.2 endpoint.2 expected,stack⟩ tailEvents last ∧
      total=sourceCount+remaining ∧ events=List.replicate sourceCount .wasm++tailEvents := by
  obtain ⟨sourceCount,sourceEnd,remaining,tailEvents,sourcePrefix,sourceBoundary,rest,length,observed⟩:=
    trace.wasm_segment allowed held completed
  have same:=OpenHost.quiet_boundary_unique allowed.wasm sourcePrefix sourceBoundary actualPrefix boundary
  cases same
  exact ⟨sourceCount,remaining,tailEvents,rest,length,observed⟩
end Exec.Spec.OpenExecution
