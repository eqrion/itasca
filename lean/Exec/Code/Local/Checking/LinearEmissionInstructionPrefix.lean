import Exec.Code.Local.Checking.CoreEmissionInstructionPrefix

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Literal, local, and integer lowering derives its instruction check from
source stack regions and retains every prior pending branch owner. -/
theorem Lowered.linearInstructionPrefix {A : Type}
    {before after : runtime.compiler.FunctionCompiler A} {instruction input output source}
    (lowered : Lowered before after instruction output) (layout : CompilerLayout before input)
    (live : before.reachable = true)
    (emission : LinearEmission (compilerLocals before) input source [instruction] output)
    (tables : CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function)
    (held : CompilerInstructionPrefix before) (frames : after.frames = before.frames) :
    CompilerInstructionPrefix after := by
  obtain ⟨inputs,outputs⟩ := lowered.source_capacities layout live
  have valid := emission.instructions_accept after.function inputs outputs
  apply lowered.openInstructionPrefix tables held (valid := valid instruction (by simp))
  intro index owned
  simpa only [PendingInstructionSite,frames] using owned

end Itasca.Runtime.Code
