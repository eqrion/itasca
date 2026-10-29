import Itasca.Runtime.Compiler.Body.Relations.Replay.ReachedCompilerLedger
import Itasca.Runtime.Compiler.Body.Reader.Control.ControlSafetyWasm2
import Itasca.Runtime.Compiler.Body.Reader.Safety.ProfileOrdinarySafety
import Itasca.Runtime.Compiler.Body.Reader.Control.BranchTableSafetyWasm2
import Itasca.Visitor.ReachedTableLabels

/-!
Normal return of a reader step at a reached compiler point.

Main declarations: `IndexedTableReaderCompilerPointWasm2.reader_total`. A direct consumer is `Compiler.Body.Relations.Replay.ReachedBodySafetyWasm2`.
-/

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

theorem IndexedTableReaderCompilerPointWasm2.reader_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env sourceLocals index ft st}
    (point : IndexedTableReaderCompilerPointWasm2 emit initial compiler types functions returns locals
      data env sourceLocals index ft st)
    (namespaces : OrdinaryNamespaces initial env ⟨sourceLocals,ft.results⟩)
    (signatures : SignatureSequence initial.signatures.val env.types.val)
    (ledger : ReachedCompilerLedger compiler st.core.vals.val)
    (bodyBound : initial.function.body_start.val+data.length ≤ Usize.max)
    (next : Usize) (advance : next.val=st.core.pos.val+1) (inbounds : st.core.pos.val<data.length)
    (opcode : U8) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      ⟨{st.core with pos:=next}⟩ data env ⟨sourceLocals,ft.results⟩ index .Wasm2 opcode compiler
      ⦃out => out.1 = .Ok () → ObservedStack out.2.2 out.2.1.core.vals.val⦄ := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  have pending := state.boundary.pending next advance inbounds
  have ready := point.ordinary_ready namespaces ledger.observed bodyBound ledger.indirect ledger.simd ledger.constants
  by_cases table : opcode = 14#u8
  · subst opcode
    rw [Wasm2.CallbackTrace.dispatch_br_table]
    apply compiler_table_reader_wasm2_total ops law compiler _ data env pending.opened.shape.core
      state.boundary.source_bound state.frames_length point.tables.depths _ state.compiled.sources ledger.fixups
      point.tables.targets ready.coordinateFits
    have budget := state.compiled.codeBudget
    unfold SourceCodeBudget at budget
    dsimp only
    omega
  by_cases control : opcode.val ∈ [2,3,4,5,11,12,13,15]
  · apply state.control_total ops law next advance inbounds _ opcode control _ ledger.observed ledger.fixups bodyBound
    obtain ⟨sigEq,_⟩ := state.compiled.metadata.fields
    simpa only [sigEq] using signatures
  · apply compiler_reader_profile_wasm2_ordinary_total ops law compiler ⟨{st.core with pos:=next}⟩ data env _ index opcode ready pending.opened.shape.core
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at control ⊢
    have tableNe : opcode.val ≠ 14 := fun h => table (UScalar.eq_of_val_eq h)
    tauto

end Itasca.Runtime.Code
