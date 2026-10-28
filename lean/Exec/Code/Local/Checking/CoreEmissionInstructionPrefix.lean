import Exec.Code.Local.Checking.OpenInstructionCompiler
import Exec.Code.Local.Relations.Common.ScalarEmissionAcceptance

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Source layouts at the two ends of actual lowering bound both operand
regions in the resulting function. -/
theorem Lowered.source_capacities {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {instruction : runtime.bytecode.Instr} {input output : List valtype} (lowered : Lowered before after instruction output)
    (layout : CompilerLayout before input) (live : before.reachable = true) :
    slots (compilerLocals before)+slots input ≤ after.function.slot_count.val ∧
    slots (compilerLocals before)+slots output ≤ after.function.slot_count.val := by
  refine ⟨(layout.live_slots_fit live).trans lowered.2.2.2.2,?_⟩
  simpa only [lowered.2.2.1] using lowered.2.1.live_slots_fit (lowered.2.2.2.1.trans live)

/-- Actual ordinary lowering derives every new instruction check from its
source emission record and preserves the open prefix's earlier checks. -/
theorem Lowered.floatCoreInstructionPrefix {A : Type}
    {before after : runtime.compiler.FunctionCompiler A} {instruction input output source C}
    (lowered : Lowered before after instruction output) (layout : CompilerLayout before input)
    (live : before.reachable = true) (locals : C.LOCALS = compilerLocals before)
    (emission : ScalarEmission C input source [instruction] output)
    (tables : CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function)
    (held : CompilerInstructionPrefix before) (frames : after.frames = before.frames) :
    CompilerInstructionPrefix after := by
  obtain ⟨inputs,outputs⟩ := lowered.source_capacities layout live
  have valid := emission.instructions_accept after.function (by simpa only [locals] using inputs) (by simpa only [locals] using outputs)
  apply lowered.openInstructionPrefix tables held (valid := valid instruction (by simp))
  intro index owned
  simpa only [PendingInstructionSite,frames] using owned

end Itasca.Runtime.Code
