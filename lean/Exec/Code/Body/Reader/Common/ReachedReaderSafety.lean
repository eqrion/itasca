import Exec.Code.Body.Relations.Common.ReachedCompilerLedger
import Exec.Code.Body.Reader.Control.ReaderControlSafetyWasm1
import Exec.Code.Body.Reader.Control.ReaderControlSafetyWasm2
import Exec.Code.Body.Reader.Common.ReaderProfileOrdinarySafety
import Exec.Code.Body.Reader.Table.ReaderTableSafetyWasm1
import Exec.Code.Body.Reader.Table.ReaderTableSafetyWasm2
namespace Exec.Code
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

theorem IndexedTableReaderCompilerPointWasm1.reader_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx bt st}
    (point : IndexedTableReaderCompilerPointWasm1 emit initial compiler types functions returns locals data env ctx bt st)
    (namespaces : OrdinaryNamespaces initial env ctx)
    (ledger : ReachedCompilerLedger compiler st.vals.val)
    (bodyBound : initial.function.body_start.val+data.length ≤ Usize.max)
    (index : U32) (next : Usize) (advance : next.val=st.pos.val+1) (inbounds : st.pos.val<data.length)
    (opcode : U8) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      ⟨{st with pos:=next}⟩ data env ctx index .Wasm1 opcode compiler
      ⦃out => out.1 = .Ok () → ObservedStack out.2.2 out.2.1.core.vals.val⦄ := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  have pending := state.boundary.pending next advance inbounds
  have ready := point.ordinary_ready namespaces ledger.observed bodyBound ledger.indirect ledger.simd ledger.constants
  by_cases table : opcode = 14#u8
  · subst opcode
    apply reader_profile_wasm1_reached _ _ data env ctx index _ compiler (fun st after => ObservedStack after st.vals.val)
    have room : compiler.function.code.val.length+3 ≤ 3*next.val := by
      have budget := state.compiled.codeBudget
      unfold SourceCodeBudget at budget
      omega
    simpa only [code.OP_BR_TABLE] using compiler_table_reader_wasm1_total ops law compiler _ data env ctx pending.opened.shape
      state.boundary.source_bound state.frames_length point.tables.depths room state.compiled.sources ledger.fixups
      point.tables.targets ready.coordinateFits
  by_cases control : opcode.val ∈ [2,3,4,5,11,12,13,15]
  · apply reader_profile_wasm1_reached _ _ data env ctx index _ compiler (fun st after => ObservedStack after st.vals.val)
    exact state.control_total ops law next advance inbounds opcode control ledger.observed ledger.fixups bodyBound
  · have capacity : st.vals.val.length < Usize.max := by
      have bound := state.boundary.bounds.vals
      have size := state.boundary.bounds.size
      have words : 2^32-1 ≤ Usize.max := by scalar_tac
      norm_num [limits.MAX_FUNCTION_BYTES] at size
      omega
    apply compiler_reader_profile_wasm1_ordinary_total ops law compiler ⟨{st with pos:=next}⟩ data env ctx index opcode ready
      pending.opened.shape capacity
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at control ⊢
    have tableNe : opcode.val ≠ 14 := fun h => table (UScalar.eq_of_val_eq h)
    tauto
end Exec.Code
