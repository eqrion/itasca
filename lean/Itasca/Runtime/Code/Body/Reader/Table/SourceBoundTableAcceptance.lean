import Itasca.Runtime.Code.Body.Reader.Table.ReachedTableAcceptance
import Itasca.Runtime.Code.Body.Reader.Table.SourceTableDemand
import Itasca.Runtime.Code.Body.Reader.Table.IndexedTableReaderCompilerPoint
import Itasca.Runtime.Code.Body.Relations.Common.ReachedCompilerLedger
import Itasca.Runtime.Code.Local.Capacity.BodyResourceRoom
import Itasca.Runtime.Code.Local.Capacity.BodyReplay

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace
set_option maxRecDepth 4096

/-- A full reached Wasm 2 branch table accepts from source-only demand.
The source reference supplies decoding and stack peaks; consumed bytes pay
all label charges, stubs, reserves, and arithmetic bounds internally. -/
theorem IndexedTableReaderCompilerPointWasm2.table_available_from_source {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns localTypes data env sourceLocals index ft st}
    (point : IndexedTableReaderCompilerPointWasm2 emit initial compiler types functions returns localTypes
      data env sourceLocals index ft st)
    (ledger : ReachedCompilerLedger compiler st.core.vals.val)
    (before after final : List Observation) (out : code.BodyState)
    (room : BodyResourceRoom initial data.length (observationDemand final).operands bound)
    (budget : SourceCompilationBudget initial.budget compiler.budget bodyResourceRate st.core.pos.val)
    (nonempty : st.core.ctrls.val ≠ []) (next : Usize)
    (advance : next.val = st.core.pos.val+1) (inbounds : st.core.pos.val<data.length)
    (byte : data.val[st.core.pos.val] = 14#u8)
    (reference : code.step_profile recorder {core := {st.core with pos := next}} data env
      ⟨sourceLocals,ft.results⟩ index .Wasm2 data.val[st.core.pos.val] before = .ok (.Ok (),out,after))
    (suffix : code.body_loop_loop recorder data env ⟨sourceLocals,ft.results⟩ index .Wasm2 before st =
      .ok (.Ok (),final)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ⟨sourceLocals,ft.results⟩ index .Wasm2
      data.val[st.core.pos.val] compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => bodyResourceRate counter * (out.core.pos.val-st.core.pos.val)) ⦄ := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  let pending := state.boundary.pending next advance inbounds
  have tail := code.body_loop_loop.accepted_tail recorder data env ⟨sourceLocals,ft.results⟩ index .Wasm2 st out
    before after final nonempty inbounds next advance reference suffix
  have canonical := reference
  rw [byte] at canonical
  have raw := canonical
  rw [Wasm2.CallbackTrace.dispatch_br_table] at raw
  obtain ⟨C,outer,spine,header,base,typed,controls,blocks,values⟩ := pending.opened
  obtain ⟨count,first,selector,popped,all,arity,countDecoded,popCall,popControls,popPos,
    countEq,allDecoded,targets⟩ := reader_table_targets_wasm2 recorder before after _ out data env
      _ pending.current.ctrl controls pending.opened.shape.core raw
  obtain ⟨depths,fallback,last,allEq,labelsDecoded,fallbackDecoded⟩ := allDecoded.unsnoc (by
    intro empty
    simp only [empty,List.length_nil] at countEq
    omega)
  have lengthSource : depths.length = count.val := by
    rw [allEq,List.length_append,List.length_singleton] at countEq
    omega
  have encoded : BrTable.Decoded data next depths fallback out.core.pos :=
    ⟨count,first,last,countDecoded,lengthSource,labelsDecoded,fallbackDecoded⟩
  have poppedSpec := code.pop_with_type.total {st.core with pos := first} .I32
    (show Control.Shape {st.core with pos := first} from
      ⟨pending.opened.shape.core.ordered,pending.opened.shape.core.bounded⟩)
  rw [popCall,WP.spec_ok] at poppedSpec
  have readCount := reader.read_u32_leb.complete data next count first countDecoded
  have loopReference : code.branch_table_with_loop recorder popped data env .Wasm2 before count none .Empty 0#u32 =
      .ok (.Ok (),out,after) := by
    unfold code.branch_table_with at raw
    rw [readCount] at raw
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Std.uncurry] at raw
    rw [popCall] at raw
    simpa only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Std.uncurry] using raw
  have operands := (source_table_loop_demand before after final popped out data env ⟨sourceLocals,ft.results⟩
    index .Wasm2 poppedSpec.1 count loopReference tail).1
  have countSpan := countDecoded.span
  change next.val < first.val ∧ first.val ≤ next.val+5 ∧ first.val ≤ data.length at countSpan
  have labelSpan := table_labels_length_span allDecoded
  have endBound := (allDecoded.span countSpan.2.2).2
  have spanPositive : st.core.pos.val < out.core.pos.val := by omega
  have remaining : st.core.pos.val+(out.core.pos.val-st.core.pos.val) ≤ data.length := by omega
  have instructionPaid : 2*(depths.length+1)+1 ≤ 3*(out.core.pos.val-st.core.pos.val) := by omega
  have branchPaid : depths.length+1 ≤ out.core.pos.val-st.core.pos.val := by omega
  have capacity := room.capacity budget state.compiled.metadata state.compiled.codeBudget state.compiled.sources
    state.compiled.cursor remaining instructionPaid out.core operands
  have branchRoom := budget.room .branches (room.counters .branches) remaining (amount := depths.length+1)
    (by simpa only [bodyResourceRate,Nat.one_mul] using branchPaid)
  change compiler.budget.branches.val+(depths.length+1) ≤ compiler.budget.limits.max_branch_table_entries.val at branchRoom
  have sourceSize := room.pc
  have reserve := room.temporary
  have words : U32.max ≤ Usize.max := by scalar_tac
  have accepted := reached_profile_br_table_available_wasm2 pending ops law bound allocation initial compiler recorder
    before after out ⟨sourceLocals,ft.results⟩ state.compiled state.sources state.fronts state.reach.current
    depths fallback encoded capacity branchRoom (by omega) (by omega) (by omega) point.tables ledger.fixups canonical
  rw [byte]
  apply WP.spec_mono accepted
  intro result held
  refine ⟨held.1,held.2.1,held.2.2.weaken ?_⟩
  intro counter
  cases counter <;> simp only [bodyResourceRate] <;> omega

end Itasca.Runtime.Code
