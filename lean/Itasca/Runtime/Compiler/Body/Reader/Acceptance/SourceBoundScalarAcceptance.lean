import Itasca.Runtime.Compiler.Body.Reader.Acceptance.ScalarAcceptance
import Itasca.Runtime.Compiler.Body.Reader.Acceptance.SourceBoundBaseAcceptance
import Itasca.Runtime.Compiler.Body.Reader.Replay.IndexedPoint

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- All ordinary scalar readers accept at a reached source/compiler prefix
when the independent body demand fits. Layout, local declarations, and callback
capacity are derived internally from that prefix and source validation. -/
theorem IndexedTableReaderCompilerPointWasm2.scalar_available_from_source {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns localTypes data env sourceLocals index ft st}
    (point : IndexedTableReaderCompilerPointWasm2 emit initial compiler types functions returns localTypes
      data env sourceLocals index ft st)
    (localsMatch : initial.function.locals = sourceLocals)
    (before after final : List Observation) (out : code.BodyState)
    (room : BodyResourceRoom initial data.length (observationDemand final).operands bound)
    (budget : SourceCompilationBudget initial.budget compiler.budget bodyResourceRate st.core.pos.val)
    (nonempty : st.core.ctrls.val ≠ []) (next : Usize)
    (advance : next.val = st.core.pos.val+1) (inbounds : st.core.pos.val<data.length)
    (kind : ScalarReaderKind) (byte : data.val[st.core.pos.val] = kind.opcode)
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
  obtain ⟨C,outer,spine,header,base,typed,ctrls,blocks,values⟩ := state.boundary.opened
  obtain ⟨_,_,_,_,storedLocals,_⟩ := state.compiled.metadata.fields
  refine source_bound_base_available_wasm2 ops out before after final bound room budget state.compiled.metadata
    state.compiled.codeBudget state.compiled.sources state.compiled.cursor nonempty next advance inbounds
    kind.opcode byte kind.ordinary kind.plain kind.sign kind.misc
    (kind.read {st.core with pos := next} data env ⟨sourceLocals,ft.results⟩) kind.action
    (kind.dispatch recorder _ data env ⟨sourceLocals,ft.results⟩ before)
    (fun counter => if counter = .instructions then 1 else 0) ?_ reference suffix
  intro capacity raw demand
  exact kind.available ops bound allocation recorder before after compiler {st.core with pos := next} out.core
    data env ⟨sourceLocals,ft.results⟩ demand (storedLocals.trans localsMatch) capacity outer savedCurrent.vals values
    (by simpa [Control.base,ctrls] using base)
    (fun live => by simpa [Control.polymorphic,ctrls] using state.reach.current live)
    state.compiled.known (fun live => (state.compiled.live live).2.layout) raw

end Itasca.Runtime.Compiler
