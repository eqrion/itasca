import Itasca.Runtime.Compiler.Local.Checking.CoreEmissionInstructionPrefix

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Literal, local, and integer lowering derives its instruction check from
source stack regions and retains every prior pending branch owner. -/
theorem Lowered.linear_instruction_prefix {A : Type}
    {before after : runtime.compiler.FunctionCompiler A} {instruction input output source}
    (lowered : Lowered before after instruction output) (layout : CompilerLayout before input)
    (live : before.reachable = true)
    (emission : LinearEmission (compilerLocals before) input source [instruction] output)
    (tables : CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function)
    (held : CompilerInstructionPrefix before) (frames : after.frames = before.frames) :
    CompilerInstructionPrefix after := by
  obtain ⟨inputs,outputs⟩ := lowered.source_capacities layout live
  have valid := emission.instructions_accept after.function inputs outputs
  apply lowered.open_instruction_prefix tables held (valid := valid instruction (by simp))
  intro index owned
  simpa only [PendingInstructionSite,frames] using owned

end Itasca.Runtime.Compiler
