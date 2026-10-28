import Itasca.Runtime.Code.Body.Reader.Simd.ReachedSimdAcceptance
import Itasca.Runtime.Code.Body.Reader.Simd.SourceSimdCallback
import Itasca.Runtime.Code.Body.Reader.Table.IndexedTableReaderCompilerPoint
import Itasca.Runtime.Code.Body.Relations.Common.ReachedCompilerLedger
import Itasca.Runtime.Code.Local.Capacity.BodyResourceRoom
import Itasca.Runtime.Code.Local.Capacity.BodyReplay
import Itasca.Runtime.Code.Local.Demand.RecordedDemand

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Source typing, source byte room, and the independent final reference
log construct all demands for actual complete SIMD reader acceptance. -/
theorem IndexedTableReaderCompilerPointWasm2.simd_available_from_source {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns localTypes data env sourceLocals index ft st}
    (point : IndexedTableReaderCompilerPointWasm2 emit initial compiler types functions returns localTypes
      data env sourceLocals index ft st)
    (C : context) (matched : EnvTranslation.Matches env ⟨sourceLocals,ft.results⟩ C)
    (ledger : ReachedCompilerLedger compiler st.core.vals.val)
    (before after final : List Observation) (out : code.BodyState)
    (room : BodyResourceRoom initial data.length (observationDemand final).operands bound)
    (budget : SourceCompilationBudget initial.budget compiler.budget bodyResourceRate st.core.pos.val)
    (nonempty : st.core.ctrls.val ≠ []) (next : Usize)
    (advance : next.val = st.core.pos.val+1) (inbounds : st.core.pos.val<data.length)
    (byte : data.val[st.core.pos.val] = 253#u8)
    (reference : code.step_profile recorder {core := {st.core with pos := next}} data env
      ⟨sourceLocals,ft.results⟩ index .Wasm2 data.val[st.core.pos.val] before = .ok (.Ok (),out,after))
    (suffix : code.body_loop_loop recorder data env ⟨sourceLocals,ft.results⟩ index .Wasm2 before st =
      .ok (.Ok (),final)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ⟨sourceLocals,ft.results⟩ index .Wasm2
      data.val[st.core.pos.val] compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  let pending := state.boundary.pending next advance inbounds
  have tail := code.body_loop_loop.accepted_tail recorder data env ⟨sourceLocals,ft.results⟩ index .Wasm2 st out
    before after final nonempty inbounds next advance reference suffix
  have canonical := reference
  rw [byte] at canonical
  obtain ⟨action,callback⟩ := source_simd_callback _ out data env ⟨sourceLocals,ft.results⟩ index before after canonical
  have operands := (source_callback_demand before after final out.core action (.Ok ()) out data env
    ⟨sourceLocals,ft.results⟩ index .Wasm2 (.Ok ()) callback tail).1
  have demand := room.demand budget state.compiled.metadata state.compiled.codeBudget state.compiled.sources
    state.compiled.cursor inbounds out.core operands
  rw [byte]
  exact reached_profile_simd_available_wasm2 pending ops bound allocation before after compiler out
    ⟨sourceLocals,ft.results⟩ C matched.mems demand state.compiled.known state.reach.current
    (fun live => (state.compiled.live live).2.layout) ledger.simd ledger.constants byte canonical

end Itasca.Runtime.Code
