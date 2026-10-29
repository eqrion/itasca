import Itasca.Runtime.Compiler.Body.Reader.References.TypedSelect
import Itasca.Runtime.Compiler.Body.Reader.Simd.SimdTypes
import Itasca.Runtime.Compiler.Body.Reader.Acceptance.RecordedAcceptance
import Itasca.Runtime.Compiler.Body.Reader.Acceptance.ProfileAcceptance
import Itasca.Runtime.Compiler.Local.Capacity.SelectAvailability
import Itasca.Runtime.Compiler.Body.Reader.Replay.IndexedPoint
import Itasca.Runtime.Compiler.Body.Relations.Replay.ReachedCompilerLedger
import Itasca.Runtime.Compiler.Local.Capacity.BodyResourceRoom
import Itasca.Visitor.BodyReplay
import Itasca.Runtime.Compiler.Local.Demand.RecordedDemand

/-!
Typed-select replay from reached source state and independently bounded demand.
-/

/-! ## Reached Typed Select Acceptance -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Explicit-select source typing supplies the full live operand layout.
The actual profile reader and callback accept with one instruction of room. -/
theorem reached_profile_typed_select_available_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (before after : List Observation) (compiler : runtime.compiler.FunctionCompiler A)
    (out : code.BodyState) (ctx : code.Context) (demand : CallbackDemand compiler out.core bound)
    (known : compiler.reachable = true → ConcreteStack st.core.vals.val)
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Sequence.stackTypes st.core.vals.val))
    (byte : data.val[p.start.val]'p.inbounds = 28#u8)
    (reference : code.step_profile recorder st data env ctx index .Wasm2 28#u8 before = .ok (.Ok (),out,after)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 28#u8 compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨capacity,raw⟩ := profile_scalar_success recorder st out data env ctx index 28#u8 before after (by decide) reference
  obtain ⟨ty,position,sourceCalled,read,controls,cursor,values,effect,post⟩ := reader_typed_select_wasm2 p
    recorder before after out ctx byte reference
  have callback : invoke (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) compiler
      (.op out.core (.select_typed ty)) ⦃ result => result.1 = .Ok () ∧
        CompilationBudgetEffect compiler.budget result.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
    change runtime.compiler.lower.FunctionCompiler.op ops compiler out.core 28#u16 0#u32 0#u32 0#u128 ⦃ _ ⦄
    by_cases live : compiler.reachable = true
    · obtain ⟨front,types,beforeTypes,_,_⟩ := reader_simd_fixed_types post effect read (known live) (monomorphic live) capacity
      simp only [Wasm2.Simd.inputTypes,Wasm2.Simd.outputTypes,List.reverse_cons,List.reverse_nil,
        List.map_append,List.map_cons,List.map_nil,List.nil_append,List.cons_append,Translate.valueType] at beforeTypes
      have layout := wholeLayout live
      rw [beforeTypes] at layout
      exact compiler_select_available ops bound allocation compiler out.core demand front (Translate.valueType ty) true
        (fun _ => layout)
    · exact compiler_select_available ops bound allocation compiler out.core demand [] .I32 true
        (fun impossible => False.elim (live impossible))
  apply profile_scalar_available_wasm2 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out.core data env
    ctx index 28#u8 compiler (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) capacity (by decide)
  rw [code.step_wasm2.typed_select] at raw ⊢
  exact recorded_reader_available (code.read_typed_select st.core data) .select_typed
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) compiler before after out.core (.select_typed ty)
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) raw sourceCalled callback

end Itasca.Runtime.Compiler

end

/-! ## Source Bound Typed Select Acceptance -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Source typing, source byte room, and the independent final reference
log construct all demands for actual explicit-select reader acceptance. -/
theorem IndexedTableReaderCompilerPointWasm2.typed_select_available_from_source {A : Type}
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
    (byte : data.val[st.core.pos.val] = 28#u8)
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
  obtain ⟨ty,position,callback,_⟩ := reader_typed_select_wasm2 pending recorder before after out
    ⟨sourceLocals,ft.results⟩ byte canonical
  have operands := (source_callback_demand before after final out.core (.select_typed ty) (.Ok ()) out data env
    ⟨sourceLocals,ft.results⟩ index .Wasm2 (.Ok ()) callback tail).1
  have demand := room.demand budget state.compiled.metadata state.compiled.codeBudget state.compiled.sources
    state.compiled.cursor inbounds out.core operands
  rw [byte]
  exact reached_profile_typed_select_available_wasm2 pending ops bound allocation before after compiler out
    ⟨sourceLocals,ft.results⟩ demand state.compiled.known state.reach.current
    (fun live => (state.compiled.live live).2.layout) byte canonical

end Itasca.Runtime.Compiler

end
