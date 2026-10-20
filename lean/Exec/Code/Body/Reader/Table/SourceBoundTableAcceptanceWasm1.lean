import Exec.Code.Body.Reader.Table.ReachedTableAcceptanceWasm1
import Exec.Code.Body.Reader.Source.SourceReaderCapacityWasm1
import Exec.Code.Body.Relations.Common.ReachedCompilerLedger

namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace
set_option maxRecDepth 4096

/-- Consumed source bytes and independently recorded operand peaks pay all
Wasm 1 table labels, stubs, and allocations, including in unreachable code. -/
theorem IndexedTableReaderCompilerPointWasm1.table_available_from_source {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns localTypes data env ctx bodyBt st}
    (point : IndexedTableReaderCompilerPointWasm1 emit initial compiler types functions returns localTypes
      data env ctx bodyBt st)
    (ledger : ReachedCompilerLedger compiler st.vals.val)
    (before after final : List Observation) (out : code.BodyState)
    (room : BodyResourceRoom initial data.length (observationDemand final).operands bound)
    (budget : SourceCompilationBudget initial.budget compiler.budget bodyResourceRate st.pos.val)
    (index : U32) (nonempty : st.ctrls.val ≠ []) (next : Usize)
    (advance : next.val = st.pos.val+1) (inbounds : st.pos.val<data.length)
    (byte : data.val[st.pos.val] = code.OP_BR_TABLE)
    (reference : code.step_profile recorder {core := {st with pos := next}} data env ctx index .Wasm1
      data.val[st.pos.val] before = .ok (.Ok (),out,after))
    (suffix : code.body_loop_loop recorder data env ctx index .Wasm1 before {core := st} = .ok (.Ok (),final)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st with pos := next}} data env ctx index .Wasm1 data.val[st.pos.val] compiler
      ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => bodyResourceRate counter * (out.core.pos.val-st.pos.val)) ⦄ := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  let pending := state.boundary.pending next advance inbounds
  have tail := code.body_loop_loop.accepted_tail recorder data env ctx index .Wasm1 ⟨st⟩ out before after final
    nonempty inbounds next advance reference suffix
  have canonical := reference
  rw [byte] at canonical
  have raw := profile_raw_success_wasm1 recorder _ out data env ctx index code.OP_BR_TABLE before after canonical
  obtain ⟨fallback,common,middle,read,callback⟩ := reader_table_dispatch_wasm1 recorder _ out.core data env ctx before after raw
  obtain ⟨depths,encoded⟩ := reader_table_decoded_wasm1 recorder pending before middle out.core fallback common read
  have invoked : invoke recorder middle (.op out.core (.br_table fallback (Control.resultView common))) =
      .ok (.Ok (),after) := callback
  have operands := (source_callback_demand middle after final out.core (.br_table fallback (Control.resultView common))
    (.Ok ()) out data env ctx index .Wasm1 (.Ok ()) invoked tail).1
  obtain ⟨count,first,last,countDecoded,lengthSource,labelsDecoded,fallbackDecoded⟩ := encoded
  have allDecoded := labelsDecoded.snoc fallbackDecoded
  have countSpan := countDecoded.span
  change next.val < first.val ∧ first.val ≤ next.val+5 ∧ first.val ≤ data.length at countSpan
  have labelSpan := table_labels_length_span allDecoded
  have endBound := (allDecoded.span countSpan.2.2).2
  simp only [List.length_append,List.length_singleton] at labelSpan
  have remaining : st.pos.val+(out.core.pos.val-st.pos.val) ≤ data.length := by omega
  have instructionPaid : 2*(depths.length+1)+1 ≤ 3*(out.core.pos.val-st.pos.val) := by omega
  have branchPaid : depths.length+1 ≤ out.core.pos.val-st.pos.val := by omega
  have capacity := room.capacity budget state.compiled.metadata state.compiled.codeBudget state.compiled.sources
    state.compiled.cursor remaining instructionPaid out.core operands
  have branchRoom := budget.room .branches (room.counters .branches) remaining (amount := depths.length+1)
    (by simpa only [bodyResourceRate,Nat.one_mul] using branchPaid)
  change compiler.budget.branches.val+(depths.length+1) ≤ compiler.budget.limits.max_branch_table_entries.val at branchRoom
  have sourceSize := room.pc
  have reserve := room.temporary
  have words : U32.max ≤ Usize.max := by scalar_tac
  have accepted := reached_br_table_available_wasm1 pending ops law bound allocation initial compiler recorder before after
    out.core state.compiled state.sources state.fronts state.reach.current depths fallback
    ⟨count,first,last,countDecoded,lengthSource,labelsDecoded,fallbackDecoded⟩ capacity branchRoom
    (by omega) (by omega) (by omega) point.tables ledger.fixups raw
  rw [byte]
  apply profile_raw_available_wasm1 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) _ out data env ctx
    index code.OP_BR_TABLE compiler (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => bodyResourceRate counter*(out.core.pos.val-st.pos.val)))
  apply WP.spec_mono accepted
  intro result held
  refine ⟨held.1,held.2.1,held.2.2.weaken ?_⟩
  intro counter
  cases counter <;> simp only [bodyResourceRate] <;> omega

end Exec.Code
