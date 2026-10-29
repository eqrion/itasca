import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerMetadata

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Numerical bounds for a closed control map. Intermediate closing targets
may equal the current code length; the final root return makes them strict. -/
def ClosedControlMapBounds (function : runtime.bytecode.CompiledFunction)
    (entry : runtime.compiler.ControlMap) : Prop :=
  entry.start_pc.val ≤ entry.end_pc.val ∧ entry.end_pc.val ≤ function.code.length ∧
    function.body_start.val ≤ entry.source_start.val ∧ entry.source_end.val ≤ function.body_end.val ∧
    entry.source_start.val < entry.source_end.val

/-- A closed map survives later code emission with the same source interval. -/
theorem ClosedControlMapBounds.grow {before after : runtime.bytecode.CompiledFunction}
    {entry : runtime.compiler.ControlMap} (held : ClosedControlMapBounds before entry)
    (code : before.code.length ≤ after.code.length)
    (start : after.body_start = before.body_start) (finish : after.body_end = before.body_end) :
    ClosedControlMapBounds after entry := by
  obtain ⟨ordered,bounded,lower,upper,positive⟩ := held
  exact ⟨ordered,bounded.trans code,by simpa only [start] using lower,
    by simpa only [finish] using upper,positive⟩

/-- Strict code growth after closing establishes the exact numeric contract
used by the actual publication checker. -/
theorem ClosedControlMapBounds.publish {before after : runtime.bytecode.CompiledFunction}
    {entry : runtime.compiler.ControlMap} (held : ClosedControlMapBounds before entry)
    (code : before.code.length < after.code.length)
    (start : after.body_start = before.body_start) (finish : after.body_end = before.body_end) :
    entry.start_pc.val ≤ entry.end_pc.val ∧ entry.end_pc.val < after.code.length ∧
      after.body_start.val ≤ entry.source_start.val ∧ entry.source_end.val ≤ after.body_end.val ∧
      entry.source_start.val < entry.source_end.val := by
  obtain ⟨ordered,bounded,lower,upper,positive⟩ := held
  exact ⟨ordered,bounded.trans_lt code,by simpa only [start] using lower,
    by simpa only [finish] using upper,positive⟩

/-- A still-open control map has a bounded entry PC and source origin. Its
owner is retained separately until the corresponding frame is popped. -/
def OpenControlMapBounds (compiler : runtime.compiler.FunctionCompiler A)
    (entry : runtime.compiler.ControlMap) : Prop :=
  entry.start_pc.val ≤ compiler.function.code.length ∧
    compiler.function.body_start.val ≤ entry.source_start.val ∧
    entry.source_start.val ≤ compiler.function.body_start.val+compiler.next_source.val

/-- Closing bounds depend on the preserved entry fields and computed exit
coordinates, so callback effects need not expose a record representation. -/
theorem OpenControlMapBounds.close_fields {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    {entry closed : runtime.compiler.ControlMap} (held : OpenControlMapBounds compiler entry)
    (startPc : closed.start_pc = entry.start_pc) (startSource : closed.source_start = entry.source_start)
    (position : closed.end_pc.val = compiler.function.code.length)
    (endSource : closed.source_end.val = compiler.function.body_start.val+positionSource)
    (progress : compiler.next_source.val < positionSource)
    (endBound : compiler.function.body_start.val+positionSource ≤ compiler.function.body_end.val) :
    ClosedControlMapBounds compiler.function closed := by
  obtain ⟨pc,lower,prior⟩ := held
  unfold ClosedControlMapBounds
  rw [startPc,startSource,position,endSource]
  exact ⟨pc,le_rfl,lower,endBound,by omega⟩

end Itasca.Runtime.Compiler
