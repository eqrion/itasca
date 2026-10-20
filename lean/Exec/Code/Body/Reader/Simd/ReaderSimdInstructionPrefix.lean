import Exec.Code.Body.Reader.Simd.ReaderSimdEventTablesWithTables
import Exec.Code.Body.Relations.Common.ExecutableInstructionPrefix
import Exec.Code.Local.Checking.BranchCallbackInstructionPrefix
import Exec.Code.Local.Checking.BranchCallbackExitSlots

namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- The exhaustive actual SIMD event classifier supplies source widths and
exact metadata appends. Every live form checks its new instruction; dead forms
only observe. Both retain the slot regions of earlier forward exits. -/
theorem SimdReaderEvent.instruction_prefix {jumpTables : List U32} {A : Type} {ops : runtime.platform.Alloc A}
    {data env sourceLocals index st p initial before after out C}
    (event : @SimdReaderEvent A ops data env sourceLocals index st p before after out C)
    (law : Platform.AllocCorrect ops)
    {emit types functions returns locals parents current}
    (contextLocals : C.LOCALS = locals)
    (invariant : StructuredCompilerPrefixWithTables jumpTables emit initial before types functions returns locals
      parents current st.core.vals.val p.start.val)
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val+data.length ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  cases reachable : before.reachable with
  | false =>
    have checked := compiler_dead_op_open_instructions ops law before after out event.opcode event.a event.b event.bits
      reachable held event.callback
    have observed := event.callback
    unfold runtime.compiler.lower.FunctionCompiler.op at observed
    rw [if_neg (by simp [reachable])] at observed
    exact ⟨checked,compiler_observe_exit_slots ops law before after out exits observed⟩
  | true =>
    obtain ⟨entered,retained⟩ := invariant.live reachable
    have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
    obtain ⟨codeFits,sourceFits,_,_⟩ := invariant.capacities bound
    have coordinateFits : before.function.body_start.val+before.next_source.val ≤ Usize.max := by
      have cursor := invariant.cursor
      have position := p.inbounds
      omega
    obtain ⟨ordinary,sources,cursor,extra,front,emitted,tables,oldTypes,lowered,emission⟩ :=
      reader_simd_callback_emission p ops law before after out C event.opcode event.sub event.a event.b event.bits event.number
        event.meaning event.post event.effect event.read (invariant.known reachable) (monomorphic reachable) event.capacity
        (contextLocals.trans retained.localsEq.symm) retained.layout reachable codeFits sourceFits coordinateFits event.callback
    have growth := instruction_check_extends_of_tables_append before.function after.function extra tables
      ordinary.capacity (by change before.function.code.val.length ≤ after.function.code.val.length; rw [lowered.1.1,List.length_append,List.length_singleton]; omega)
    have layout := retained.layout
    rw [oldTypes] at layout
    exact ⟨lowered.1.executableInstructionPrefix layout reachable (contextLocals.trans retained.localsEq.symm)
      (.base (.right emission)) emission.not_branchTable growth held ordinary.frames,
      exits.retained (congrArg alloc.vec.Vec.val ordinary.frames) ordinary.capacity⟩

end Exec.Code
