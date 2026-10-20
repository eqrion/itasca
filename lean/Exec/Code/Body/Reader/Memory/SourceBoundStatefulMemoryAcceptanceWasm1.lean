import Exec.Code.Body.Reader.Memory.ReachedStatefulMemoryAcceptanceWasm1
import Exec.Code.Body.Reader.Acceptance.StatefulCallbackAcceptance
import Exec.Code.Body.Reader.Source.SourceReaderCapacityWasm1
import Exec.Code.Body.Relations.Common.ReachedCompilerLedger

namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Wasm 1 memory size/growth readers accept from independent source typing
and source-derived allocation demand, including polymorphic dead paths. -/
theorem IndexedTableReaderCompilerPointWasm1.stateful_memory_available_from_source {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns localTypes data env ctx bodyBt st}
    (point : IndexedTableReaderCompilerPointWasm1 emit initial compiler types functions returns localTypes
      data env ctx bodyBt st)
    (C : context) (matched : EnvTranslation.Matches env ctx C)
    (ledger : ReachedCompilerLedger compiler st.vals.val)
    (before after final : List Observation) (out : code.BodyState)
    (room : BodyResourceRoom initial data.length (observationDemand final).operands bound)
    (budget : SourceCompilationBudget initial.budget compiler.budget bodyResourceRate st.pos.val)
    (index : U32) (nonempty : st.ctrls.val ≠ []) (next : Usize)
    (advance : next.val = st.pos.val+1) (inbounds : st.pos.val<data.length)
    (opcode : U8) (member : opcode.val ∈ [63,64]) (byte : data.val[st.pos.val] = opcode)
    (reference : code.step_profile recorder {core := {st with pos := next}} data env ctx index .Wasm1
      data.val[st.pos.val] before = .ok (.Ok (),out,after))
    (suffix : code.body_loop_loop recorder data env ctx index .Wasm1 before {core := st} = .ok (.Ok (),final)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st with pos := next}} data env ctx index .Wasm1 data.val[st.pos.val] compiler
      ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧ CompilationBudgetEffect compiler.budget result.2.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  let pending := state.boundary.pending next advance inbounds
  have tail := code.body_loop_loop.accepted_tail recorder data env ctx index .Wasm1 ⟨st⟩ out before after final
    nonempty inbounds next advance reference suffix
  have canonical := reference
  rw [byte] at canonical
  have raw := profile_raw_success_wasm1 recorder _ out data env ctx index opcode before after canonical
  obtain ⟨op,_,_,callback,_⟩ := reader_stateful_memory_wasm1 pending recorder before after out.core opcode member byte raw
  rw [stateful_callback_invoke] at callback
  have operands := (source_callback_demand before after final out.core (statefulAction op 0#u32 0#u32) (.Ok ()) out
    data env ctx index .Wasm1 (.Ok ()) callback tail).1
  have demand := room.demand budget state.compiled.metadata state.compiled.codeBudget state.compiled.sources
    state.compiled.cursor inbounds out.core operands
  rw [byte]
  apply profile_raw_available_wasm1 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) _ out data env ctx index
    opcode compiler (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0))
  exact reached_reader_stateful_memory_available_wasm1 pending ops bound allocation recorder before after compiler out.core
    opcode member demand C matched state.compiled.known state.reach.current (fun live => (state.compiled.live live).2.layout)
    ledger.indirect byte raw

end Exec.Code
