import Exec.Code.Body.Relations.Common.ExecutableInstructionAcceptance
import Exec.Code.Local.Checking.CoreEmissionInstructionPrefix

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Captured table appends increase every local checker index space. The
contents are separately related to source syntax by emission certificates. -/
theorem instruction_check_extends_of_tables_append (before after : runtime.bytecode.CompiledFunction)
    (extra : CompilerTables)
    (tables : CompilerTables.ofFunction after = (CompilerTables.ofFunction before).append extra)
    (slots : before.slot_count.val ≤ after.slot_count.val) (code : before.code.length ≤ after.code.length) :
    InstructionCheckExtends before after := by
  have lengths := congrArg (fun tables => (tables.indirect.length,tables.simd.length,tables.constants.length,tables.jumpTables.length)) tables
  simp only [CompilerTables.ofFunction,CompilerTables.append,List.length_append,Prod.mk.injEq] at lengths
  refine ⟨slots,code,?_,?_,?_,?_⟩
  · change before.indirect.val.length ≤ after.indirect.val.length
    omega
  · change before.simd.val.length ≤ after.simd.val.length
    omega
  · change before.v128_pool.val.length ≤ after.v128_pool.val.length
    omega
  · change before.jump_tables.val.length ≤ after.jump_tables.val.length
    omega

/-- All ordinary complete-profile source emissions preserve checking of every
stored instruction, including outstanding branches in older code. Appended
SIMD, constant, and indirect-call metadata are allowed. -/
theorem Lowered.executableInstructionPrefix {A : Type}
    {before after : runtime.compiler.FunctionCompiler A} {instruction input output source C}
    (lowered : Lowered before after instruction output) (layout : CompilerLayout before input)
    (live : before.reachable = true) (locals : C.LOCALS = compilerLocals before)
    (emission : ExecutableEmission (CompilerTables.ofFunction after.function) C input source [instruction] output)
    (ordinary : ∀ depths fallback, source ≠ .BR_TABLE depths fallback)
    (growth : InstructionCheckExtends before.function after.function)
    (held : CompilerInstructionPrefix before) (frames : after.frames = before.frames) :
    CompilerInstructionPrefix after := by
  obtain ⟨inputs,outputs⟩ := lowered.source_capacities layout live
  have valid := emission.ordinary_instructions_accept after.function ordinary
    (by simpa only [locals] using inputs) (by simpa only [locals] using outputs)
  refine held.append growth ?_ [instruction] lowered.1 (by simpa using valid instruction (by simp))
  intro index owned
  simpa only [PendingInstructionSite,frames] using owned

end Itasca.Runtime.Code
