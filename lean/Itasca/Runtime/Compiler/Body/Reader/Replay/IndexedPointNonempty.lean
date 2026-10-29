import Itasca.Runtime.Compiler.Body.Reader.Replay.IndexedPoint

/-!
The complete-profile reached reader likewise has an active source control frame.

Main declarations: `IndexedTableReaderCompilerPointWasm2.ctrls_nonempty`. A direct consumer is `Compiler.Body.Reader.Publication.SourcePublicationAdvanceWasm2`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- The complete-profile reached reader likewise has an active source control frame. -/
theorem IndexedTableReaderCompilerPointWasm2.ctrls_nonempty {A : Type}
    {emit initial compiler types functions returns locals data env sourceLocals index ft st}
    (point : @IndexedTableReaderCompilerPointWasm2 emit A initial compiler types functions returns locals data env sourceLocals index ft st) :
    st.core.ctrls.val ≠ [] := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  obtain ⟨C,outer,spine,header,base,typed,controls,blocks,values⟩ := state.boundary.opened
  rw [controls]
  simp

end Itasca.Runtime.Compiler
