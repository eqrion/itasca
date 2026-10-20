import Exec.Code.Body.Reader.Acceptance.ScalarReaderAcceptance
import Exec.Code.Body.Reader.Source.SourceReaderCapacityWasm1

namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Every ordinary Wasm 1 scalar reader accepts from independent source
validation and source-derived demand, for both live and polymorphic code. -/
theorem IndexedTableReaderCompilerPointWasm1.scalar_available_from_source {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns localTypes data env ctx bodyBt st}
    (point : IndexedTableReaderCompilerPointWasm1 emit initial compiler types functions returns localTypes
      data env ctx bodyBt st)
    (localsMatch : initial.function.locals = ctx.locals)
    (before after final : List Observation) (out : code.BodyState)
    (room : BodyResourceRoom initial data.length (observationDemand final).operands bound)
    (budget : SourceCompilationBudget initial.budget compiler.budget bodyResourceRate st.pos.val)
    (index : U32) (nonempty : st.ctrls.val ≠ []) (next : Usize)
    (advance : next.val = st.pos.val+1) (inbounds : st.pos.val<data.length)
    (kind : ScalarReaderKind) (byte : data.val[st.pos.val] = kind.opcode)
    (reference : code.step_profile recorder {core := {st with pos := next}} data env ctx index .Wasm1
      data.val[st.pos.val] before = .ok (.Ok (),out,after))
    (suffix : code.body_loop_loop recorder data env ctx index .Wasm1 before {core := st} = .ok (.Ok (),final)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st with pos := next}} data env ctx index .Wasm1 data.val[st.pos.val] compiler
      ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧ CompilationBudgetEffect compiler.budget result.2.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  let pending := state.boundary.pending next advance inbounds
  have canonical := reference
  rw [byte] at canonical
  obtain ⟨capacity,_,_,_⟩ := point.capacity_from_source_read before after final out bound room budget index nonempty next advance
    inbounds kind.opcode (kind.read {st with pos := next} data env ctx) kind.action
    (kind.dispatch recorder _ data env ctx before) canonical byte suffix
  have raw := profile_raw_success_wasm1 recorder _ out data env ctx index kind.opcode before after canonical
  obtain ⟨C,outer,spine,header,base,typed,ctrls,values⟩ := state.boundary.opened
  obtain ⟨_,_,_,_,storedLocals,_⟩ := state.compiled.metadata.fields
  rw [byte]
  apply profile_raw_available_wasm1 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) _ out data env ctx index
    kind.opcode compiler (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0))
  exact kind.available ops bound allocation recorder before after compiler {st with pos := next} out.core data env ctx
    (capacity.one (by decide)) (storedLocals.trans localsMatch) (by have room := pending.val_capacity; omega)
    outer savedCurrent.vals values (by simpa [Control.base,ctrls] using base)
    (fun live => by simpa [Control.polymorphic,ctrls] using state.reach.current live)
    state.compiled.known (fun live => (state.compiled.live live).2.layout) raw

end Exec.Code
