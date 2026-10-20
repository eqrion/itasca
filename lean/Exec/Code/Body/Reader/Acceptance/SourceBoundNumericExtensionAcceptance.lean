import Exec.Code.Body.Reader.Acceptance.ReachedNumericExtensionAcceptance
import Exec.Code.Body.Reader.Table.IndexedTableReaderCompilerPoint
import Exec.Code.Local.Capacity.BodyResourceRoom
import Exec.Code.Local.Capacity.BodyReplay
import Exec.Code.Local.Demand.RecordedDemand

namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Independent source sign validation and source-byte room construct
the actual numeric-extension callback demand internally. -/
theorem IndexedTableReaderCompilerPointWasm2.sign_available_from_source {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns localTypes data env sourceLocals index ft st}
    (point : IndexedTableReaderCompilerPointWasm2 emit initial compiler types functions returns localTypes
      data env sourceLocals index ft st)
    (before after final : List Observation) (out : code.BodyState)
    (room : BodyResourceRoom initial data.length (observationDemand final).operands bound)
    (budget : SourceCompilationBudget initial.budget compiler.budget bodyResourceRate st.core.pos.val)
    (nonempty : st.core.ctrls.val ≠ []) (next : Usize)
    (advance : next.val = st.core.pos.val+1) (inbounds : st.core.pos.val<data.length)
    (op : Abs.Numeric.Instruction) (extension : 192 ≤ (integerOpcode op).val)
    (byte : data.val[st.core.pos.val] = UScalar.cast .U8 (integerOpcode op))
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
  obtain ⟨operation,hook,meaning,_,_,_,encoding,_,ordinary,base⟩ :=
    integer_sign_reader_facts ops compiler out.core op extension
  obtain ⟨capacity,raw⟩ := profile_scalar_success recorder _ out data env ⟨sourceLocals,ft.results⟩ index _ before after
    ordinary canonical
  rw [code.step_wasm2.base _ _ _ _ _ _ _ base] at raw
  obtain ⟨callback,_⟩ := reader_sign_wasm2 pending recorder before after out.core ⟨sourceLocals,ft.results⟩ _ operation
    capacity byte meaning raw
  have dispatch := ExtendedNumericHook.dispatch recorder before out.core hook
  rw [encoding] at dispatch
  dsimp only at dispatch
  rw [dispatch] at callback
  have operands := (source_callback_demand before after final out.core (.extendedNumeric hook) (.Ok ()) out data env
    ⟨sourceLocals,ft.results⟩ index .Wasm2 (.Ok ()) callback tail).1
  have demand := room.demand budget state.compiled.metadata state.compiled.codeBudget state.compiled.sources
    state.compiled.cursor inbounds out.core operands
  rw [byte]
  exact reached_profile_sign_available_wasm2 pending ops bound allocation recorder before after compiler out
    ⟨sourceLocals,ft.results⟩ op extension demand state.compiled.known state.reach.current
    (fun live => (state.compiled.live live).2.layout) byte canonical

/-- Independent source saturating validation and source-byte room construct
the actual numeric-extension callback demand internally. -/
theorem IndexedTableReaderCompilerPointWasm2.saturating_available_from_source {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns localTypes data env sourceLocals index ft st}
    (point : IndexedTableReaderCompilerPointWasm2 emit initial compiler types functions returns localTypes
      data env sourceLocals index ft st)
    (before after final : List Observation) (out : code.BodyState)
    (room : BodyResourceRoom initial data.length (observationDemand final).operands bound)
    (budget : SourceCompilationBudget initial.budget compiler.budget bodyResourceRate st.core.pos.val)
    (nonempty : st.core.ctrls.val ≠ []) (next : Usize)
    (advance : next.val = st.core.pos.val+1) (inbounds : st.core.pos.val<data.length)
    (op : Abs.Float.Instruction) (extension : 256 ≤ (floatOpcode op).val)
    (subopcode : U32) (prefixEnd : Usize) (subopcodeEq : subopcode.val = (floatOpcode op).val-256)
    (decoded : Leb128.Decoded data next subopcode prefixEnd)
    (byte : data.val[st.core.pos.val] = 252#u8)
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
  obtain ⟨sub,operation,hook,subEq,small,meaning,_,_,_,encoding,_⟩ :=
    float_saturating_reader_facts ops compiler out.core op extension
  have same : sub = subopcode := UScalar.eq_of_val_eq (subEq.trans subopcodeEq.symm)
  subst sub
  obtain ⟨capacity,raw⟩ := profile_scalar_success recorder _ out data env ⟨sourceLocals,ft.results⟩ index 252#u8 before after
    (by decide) canonical
  rw [code.step_wasm2.saturating _ _ _ _ _ _ _ _ decoded small] at raw
  obtain ⟨callback,_⟩ := reader_saturating_wasm2 pending recorder before after out.core ⟨sourceLocals,ft.results⟩
    subopcode prefixEnd operation capacity byte decoded meaning raw
  have dispatch := ExtendedNumericHook.dispatch recorder before out.core hook
  rw [encoding] at dispatch
  dsimp only at dispatch
  rw [dispatch] at callback
  have operands := (source_callback_demand before after final out.core (.extendedNumeric hook) (.Ok ()) out data env
    ⟨sourceLocals,ft.results⟩ index .Wasm2 (.Ok ()) callback tail).1
  have demand := room.demand budget state.compiled.metadata state.compiled.codeBudget state.compiled.sources
    state.compiled.cursor inbounds out.core operands
  rw [byte]
  exact reached_profile_saturating_available_wasm2 pending ops bound allocation recorder before after compiler out
    ⟨sourceLocals,ft.results⟩ op extension subopcode prefixEnd subopcodeEq decoded demand state.compiled.known state.reach.current
    (fun live => (state.compiled.live live).2.layout) byte canonical

end Exec.Code
