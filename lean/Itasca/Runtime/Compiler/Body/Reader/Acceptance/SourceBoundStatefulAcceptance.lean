import Itasca.Runtime.Compiler.Local.Capacity.ReaderAcceptance
import Itasca.Runtime.Compiler.Body.Reader.Acceptance.StatefulCallbackAcceptance
import Itasca.Runtime.Compiler.Body.Reader.Stateful.StatefulBase
import Itasca.Runtime.Compiler.Body.Reader.Acceptance.ProfileAcceptance
import Itasca.Runtime.Compiler.Body.Reader.Stateful.StatefulBulkDispatch
import Itasca.Runtime.Compiler.Body.Reader.Replay.IndexedPoint
import Itasca.Runtime.Compiler.Body.Relations.Replay.ReachedCompilerLedger
import Itasca.Runtime.Compiler.Local.Capacity.BodyResourceRoom
import Itasca.Runtime.Compiler.Local.Capacity.BodyReplay
import Itasca.Runtime.Compiler.Local.Demand.RecordedDemand

/-!
Base and bulk stateful reader replay from independent source bounds. The two dispatch families retain their distinct source and allocation obligations.
-/

/-! ## Reached Stateful Base Acceptance -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 4096

/-- Actual base reference, table, and memory-metadata readers accept when
independent source typing and the retained live layout discharge their hooks.
Only the current independently accepted source result is replayed. -/
theorem reached_profile_stateful_base_available_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A V : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (opcode : U8) (member : opcode.val ∈ [37,38,63,64,208,209,210])
    (demand : CallbackDemand compiler out.core bound)
    (C : context) (matched : EnvTranslation.Matches env ⟨locals,p.ft.results⟩ C)
    (known : compiler.reachable = true → ConcreteStack st.core.vals.val)
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Sequence.stackTypes st.core.vals.val))
    (pairs : compiler.function.indirect.length ≤ compiler.function.code.length)
    (byte : data.val[p.start.val]'p.inbounds = opcode)
    (reference : code.step_profile source st data env ctx index .Wasm2 opcode before = .ok (.Ok (),out,after)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 opcode compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  have ordinary : opcode.val ∉ Wasm2.controlOpcodes := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with h | h | h | h | h | h | h <;> simp only [h,Wasm2.controlOpcodes] <;> decide
  obtain ⟨capacity,raw⟩ := profile_scalar_success source st out data env ctx index opcode before after ordinary reference
  have callbacks {op : Abs.Stateful.Instruction} (post : StatefulReaderPost p out.core op)
      (a b : U32) (arguments : StatefulArguments op a b) :=
    post.callback_available ops bound allocation compiler demand C matched known monomorphic wholeLayout pairs a b arguments
  apply profile_scalar_available_wasm2 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out.core
    data env ctx index opcode compiler
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) capacity ordinary
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with member | member | member | member | member | member | member
  · have equal : opcode = 37#u8 := UScalar.eq_of_val_eq member
    rw [equal] at byte raw ⊢
    rw [code.step_wasm2.table_get] at raw ⊢
    refine CoreVisitor.run.accepted_lift_on (code.read_table_get st.core data env) source.on_table_get
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_table_get before after compiler out.core
      (fun after => CompilationBudgetEffect compiler.budget after.budget
        (fun counter => if counter = .instructions then 1 else 0)) raw ?_
    intro value read _
    have post := reader_table_get_post_wasm2 p byte capacity value out.core read
    exact callbacks post value 0#u32 ⟨rfl,rfl⟩
  · have equal : opcode = 38#u8 := UScalar.eq_of_val_eq member
    rw [equal] at byte raw ⊢
    rw [code.step_wasm2.table_set] at raw ⊢
    refine CoreVisitor.run.accepted_lift_on (code.read_table_set st.core data env) source.on_table_set
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_table_set before after compiler out.core
      (fun after => CompilationBudgetEffect compiler.budget after.budget
        (fun counter => if counter = .instructions then 1 else 0)) raw ?_
    intro value read _
    have post := reader_table_set_post_wasm2 p byte capacity value out.core read
    exact callbacks post value 0#u32 ⟨rfl,rfl⟩
  · have equal : opcode = 63#u8 := UScalar.eq_of_val_eq member
    rw [equal] at byte raw ⊢
    rw [code.step_wasm2.base _ _ _ _ _ _ _ (by decide),
      code.step_extended.base _ _ _ _ _ _ _ rfl (by simp [global_simps])] at raw ⊢
    have dispatchSource := code.step_memory_size.dispatch source st.core data env ctx before
    have dispatchTarget := code.step_memory_size.dispatch (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st.core data env ctx compiler
    simp only [global_simps] at dispatchSource dispatchTarget
    rw [dispatchSource] at raw
    rw [dispatchTarget]
    refine CoreVisitor.run.accepted_lift_on (code.read_memory_size st.core data env) (fun v state (_ : Unit) => source.on_memory_size v state)
      (fun v state (_ : Unit) => (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_memory_size v state) before after compiler out.core
      (fun after => CompilationBudgetEffect compiler.budget after.budget
        (fun counter => if counter = .instructions then 1 else 0)) raw ?_
    intro value read _
    cases value
    have post := reader_memory_size_post_wasm2 p byte capacity out.core read
    exact callbacks post 0#u32 0#u32 ⟨rfl,rfl⟩
  · have equal : opcode = 64#u8 := UScalar.eq_of_val_eq member
    rw [equal] at byte raw ⊢
    rw [code.step_wasm2.base _ _ _ _ _ _ _ (by decide),
      code.step_extended.base _ _ _ _ _ _ _ rfl (by simp [global_simps])] at raw ⊢
    have dispatchSource := code.step_memory_grow.dispatch source st.core data env ctx before
    have dispatchTarget := code.step_memory_grow.dispatch (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st.core data env ctx compiler
    simp only [global_simps] at dispatchSource dispatchTarget
    rw [dispatchSource] at raw
    rw [dispatchTarget]
    refine CoreVisitor.run.accepted_lift_on (code.read_memory_grow st.core data env) (fun v state (_ : Unit) => source.on_memory_grow v state)
      (fun v state (_ : Unit) => (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_memory_grow v state) before after compiler out.core
      (fun after => CompilationBudgetEffect compiler.budget after.budget
        (fun counter => if counter = .instructions then 1 else 0)) raw ?_
    intro value read _
    cases value
    have post := reader_memory_grow_post_wasm2 p byte capacity out.core read
    exact callbacks post 0#u32 0#u32 ⟨rfl,rfl⟩
  · have equal : opcode = 208#u8 := UScalar.eq_of_val_eq member
    rw [equal] at byte raw ⊢
    rw [code.step_wasm2.ref_null] at raw ⊢
    refine CoreVisitor.run.accepted_lift_on (code.read_ref_null st.core data) source.on_ref_null
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_ref_null before after compiler out.core
      (fun after => CompilationBudgetEffect compiler.budget after.budget
        (fun counter => if counter = .instructions then 1 else 0)) raw ?_
    intro value read _
    have post := reader_ref_null_post_wasm2 p byte capacity value out.core read
    have callback := callbacks post (match value with | .FuncRef => 0#u32 | .ExternRef => 1#u32) 0#u32 (by cases value <;> exact ⟨rfl,rfl⟩)
    cases value <;> exact callback
  · have equal : opcode = 209#u8 := UScalar.eq_of_val_eq member
    rw [equal] at byte raw ⊢
    rw [code.step_wasm2.ref_is_null] at raw ⊢
    refine CoreVisitor.run.accepted_lift_on (code.read_ref_is_null st.core) (fun v state (_ : Unit) => source.on_ref_is_null v state)
      (fun v state (_ : Unit) => (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_ref_is_null v state) before after compiler out.core
      (fun after => CompilationBudgetEffect compiler.budget after.budget
        (fun counter => if counter = .instructions then 1 else 0)) raw ?_
    intro value read _
    cases value
    have post := reader_ref_is_null_post_wasm2 p out.core byte capacity read
    exact callbacks post 0#u32 0#u32 ⟨rfl,rfl⟩
  · have equal : opcode = 210#u8 := UScalar.eq_of_val_eq member
    rw [equal] at byte raw ⊢
    rw [code.step_wasm2.ref_func] at raw ⊢
    refine CoreVisitor.run.accepted_lift_on (code.read_ref_func st.core data env) source.on_ref_func
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_ref_func before after compiler out.core
      (fun after => CompilationBudgetEffect compiler.budget after.budget
        (fun counter => if counter = .instructions then 1 else 0)) raw ?_
    intro value read _
    have post := reader_ref_func_post_wasm2 p value out.core byte capacity read
    exact callbacks post value 0#u32 ⟨rfl,rfl⟩

end Itasca.Runtime.Code

end

/-! ## Reached Stateful Bulk Acceptance -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 4096

/-- Actual miscellaneous-prefix table and bulk-memory readers accept when
independent source typing and the retained live layout discharge their hooks.
Only the current independently accepted source result is replayed. -/
theorem reached_profile_stateful_bulk_available_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A V : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (source : code.OpVisitor V) (before after : V)
    (compiler : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (subopcode : U32) (next : Usize) (member : subopcode.val ∈ [8,9,10,11,12,13,14,15,16,17])
    (decoded : Leb128.Decoded data st.core.pos subopcode next)
    (demand : CallbackDemand compiler out.core bound)
    (C : context) (matched : EnvTranslation.Matches env ⟨locals,p.ft.results⟩ C)
    (known : compiler.reachable = true → ConcreteStack st.core.vals.val)
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Sequence.stackTypes st.core.vals.val))
    (pairs : compiler.function.indirect.length ≤ compiler.function.code.length)
    (byte : data.val[p.start.val]'p.inbounds = 252#u8)
    (reference : code.step_profile source st data env ctx index .Wasm2 252#u8 before = .ok (.Ok (),out,after)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 252#u8 compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  have ordinary : (252#u8).val ∉ Wasm2.controlOpcodes := by simp only [Wasm2.controlOpcodes]; decide
  have extended : 8 ≤ subopcode.val := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    omega
  obtain ⟨capacity,raw⟩ := profile_scalar_success source st out data env ctx index 252#u8 before after ordinary reference
  have callbacks {op : Abs.Stateful.Instruction} (post : StatefulReaderPost p out.core op)
      (a b : U32) (arguments : StatefulArguments op a b) :=
    post.callback_available ops bound allocation compiler demand C matched known monomorphic wholeLayout pairs a b arguments
  apply profile_scalar_available_wasm2 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out.core
    data env ctx index 252#u8 compiler
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) capacity ordinary
  rw [code.step_wasm2.bulk _ _ _ _ _ subopcode next _ decoded extended,code.step_bulk.eq_runs] at raw ⊢
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with member | member | member | member | member | member | member | member | member | member
  · have equal : subopcode = 8#u32 := UScalar.eq_of_val_eq member
    rw [equal] at decoded raw ⊢
    simp only [Wasm2.bulkStep] at raw ⊢
    refine CoreVisitor.run.accepted_lift_on (code.read_memory_init {st.core with pos := next} data env) source.on_memory_init
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_memory_init before after compiler out.core
      (fun after => CompilationBudgetEffect compiler.budget after.budget
        (fun counter => if counter = .instructions then 1 else 0)) raw ?_
    intro value read _
    have post := reader_memory_init_post_wasm2 p byte next decoded capacity value out.core read
    exact callbacks post value 0#u32 ⟨rfl,rfl⟩
  · have equal : subopcode = 9#u32 := UScalar.eq_of_val_eq member
    rw [equal] at decoded raw ⊢
    simp only [Wasm2.bulkStep] at raw ⊢
    refine CoreVisitor.run.accepted_lift_on (code.take_data_index {st.core with pos := next} data env) source.on_data_drop
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_data_drop before after compiler out.core
      (fun after => CompilationBudgetEffect compiler.budget after.budget
        (fun counter => if counter = .instructions then 1 else 0)) raw ?_
    intro value read _
    have post := reader_data_drop_post_wasm2 p byte next decoded capacity value out.core read
    exact callbacks post value 0#u32 ⟨rfl,rfl⟩
  · have equal : subopcode = 10#u32 := UScalar.eq_of_val_eq member
    rw [equal] at decoded raw ⊢
    simp only [Wasm2.bulkStep] at raw ⊢
    refine CoreVisitor.run.accepted_lift_on (code.read_memory_copy {st.core with pos := next} data env) (fun v state (_ : Unit) => source.on_memory_copy v state)
      (fun v state (_ : Unit) => (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_memory_copy v state) before after compiler out.core
      (fun after => CompilationBudgetEffect compiler.budget after.budget
        (fun counter => if counter = .instructions then 1 else 0)) raw ?_
    intro value read _
    cases value
    have post := reader_memory_copy_post_wasm2 p byte next decoded capacity () out.core read
    exact callbacks post 0#u32 0#u32 ⟨rfl,rfl⟩
  · have equal : subopcode = 11#u32 := UScalar.eq_of_val_eq member
    rw [equal] at decoded raw ⊢
    simp only [Wasm2.bulkStep] at raw ⊢
    refine CoreVisitor.run.accepted_lift_on (code.read_memory_fill {st.core with pos := next} data env) (fun v state (_ : Unit) => source.on_memory_fill v state)
      (fun v state (_ : Unit) => (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_memory_fill v state) before after compiler out.core
      (fun after => CompilationBudgetEffect compiler.budget after.budget
        (fun counter => if counter = .instructions then 1 else 0)) raw ?_
    intro value read _
    cases value
    have post := reader_memory_fill_post_wasm2 p byte next decoded capacity () out.core read
    exact callbacks post 0#u32 0#u32 ⟨rfl,rfl⟩
  · have equal : subopcode = 12#u32 := UScalar.eq_of_val_eq member
    rw [equal] at decoded raw ⊢
    simp only [Wasm2.bulkStep] at raw ⊢
    refine CoreVisitor.run.accepted_lift_on (code.read_table_init {st.core with pos := next} data env) (fun v state (arg : U32 × U32) => source.on_table_init v state arg.1 arg.2)
      (fun v state (arg : U32 × U32) => (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_table_init v state arg.1 arg.2) before after compiler out.core
      (fun after => CompilationBudgetEffect compiler.budget after.budget
        (fun counter => if counter = .instructions then 1 else 0)) raw ?_
    intro value read _
    have post := reader_table_init_post_wasm2 p byte next decoded capacity value out.core read
    exact callbacks post value.1 value.2 ⟨rfl,rfl⟩
  · have equal : subopcode = 13#u32 := UScalar.eq_of_val_eq member
    rw [equal] at decoded raw ⊢
    simp only [Wasm2.bulkStep] at raw ⊢
    refine CoreVisitor.run.accepted_lift_on (code.take_element {st.core with pos := next} data env) (fun v state (arg : U32 × types.ValueType) => source.on_elem_drop v state arg.1)
      (fun v state (arg : U32 × types.ValueType) => (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_elem_drop v state arg.1) before after compiler out.core
      (fun after => CompilationBudgetEffect compiler.budget after.budget
        (fun counter => if counter = .instructions then 1 else 0)) raw ?_
    intro value read _
    have post := reader_elem_drop_post_wasm2 p byte next decoded capacity value out.core read
    exact callbacks post value.1 0#u32 ⟨rfl,rfl⟩
  · have equal : subopcode = 14#u32 := UScalar.eq_of_val_eq member
    rw [equal] at decoded raw ⊢
    simp only [Wasm2.bulkStep] at raw ⊢
    refine CoreVisitor.run.accepted_lift_on (code.read_table_copy {st.core with pos := next} data env) (fun v state (arg : U32 × U32) => source.on_table_copy v state arg.1 arg.2)
      (fun v state (arg : U32 × U32) => (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_table_copy v state arg.1 arg.2) before after compiler out.core
      (fun after => CompilationBudgetEffect compiler.budget after.budget
        (fun counter => if counter = .instructions then 1 else 0)) raw ?_
    intro value read _
    have post := reader_table_copy_post_wasm2 p byte next decoded capacity value out.core read
    exact callbacks post value.1 value.2 ⟨rfl,rfl⟩
  · have equal : subopcode = 15#u32 := UScalar.eq_of_val_eq member
    rw [equal] at decoded raw ⊢
    simp only [Wasm2.bulkStep] at raw ⊢
    refine CoreVisitor.run.accepted_lift_on (code.read_table_grow {st.core with pos := next} data env) source.on_table_grow
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_table_grow before after compiler out.core
      (fun after => CompilationBudgetEffect compiler.budget after.budget
        (fun counter => if counter = .instructions then 1 else 0)) raw ?_
    intro value read _
    have post := reader_table_grow_post_wasm2 p byte next decoded capacity value out.core read
    exact callbacks post value 0#u32 ⟨rfl,rfl⟩
  · have equal : subopcode = 16#u32 := UScalar.eq_of_val_eq member
    rw [equal] at decoded raw ⊢
    simp only [Wasm2.bulkStep] at raw ⊢
    refine CoreVisitor.run.accepted_lift_on (code.read_table_size {st.core with pos := next} data env) source.on_table_size
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_table_size before after compiler out.core
      (fun after => CompilationBudgetEffect compiler.budget after.budget
        (fun counter => if counter = .instructions then 1 else 0)) raw ?_
    intro value read _
    have post := reader_table_size_post_wasm2 p byte next decoded capacity value out.core read
    exact callbacks post value 0#u32 ⟨rfl,rfl⟩
  · have equal : subopcode = 17#u32 := UScalar.eq_of_val_eq member
    rw [equal] at decoded raw ⊢
    simp only [Wasm2.bulkStep] at raw ⊢
    refine CoreVisitor.run.accepted_lift_on (code.read_table_fill {st.core with pos := next} data env) source.on_table_fill
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_table_fill before after compiler out.core
      (fun after => CompilationBudgetEffect compiler.budget after.budget
        (fun counter => if counter = .instructions then 1 else 0)) raw ?_
    intro value read _
    have post := reader_table_fill_post_wasm2 p byte next decoded capacity value out.core read
    exact callbacks post value 0#u32 ⟨rfl,rfl⟩

end Itasca.Runtime.Code

end

/-! ## Source Bound Stateful Acceptance -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace
set_option maxRecDepth 4096

/-- Source typing, source byte room, and the independent final reference
log construct all demands for actual stateful base reader acceptance. -/
theorem IndexedTableReaderCompilerPointWasm2.stateful_base_available_from_source {A : Type}
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
    (opcode : U8) (member : opcode.val ∈ [37,38,63,64,208,209,210])
    (byte : data.val[st.core.pos.val] = opcode)
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
  obtain ⟨op,a,b,_,callback,_⟩ := reader_stateful_base_wasm2 pending recorder before after out
    ⟨sourceLocals,ft.results⟩ opcode member byte canonical
  rw [stateful_callback_invoke] at callback
  have operands := (source_callback_demand before after final out.core (statefulAction op a b) (.Ok ()) out data env
    ⟨sourceLocals,ft.results⟩ index .Wasm2 (.Ok ()) callback tail).1
  have demand := room.demand budget state.compiled.metadata state.compiled.codeBudget state.compiled.sources
    state.compiled.cursor inbounds out.core operands
  rw [byte]
  exact reached_profile_stateful_base_available_wasm2 pending ops bound allocation recorder before after compiler out
    ⟨sourceLocals,ft.results⟩ opcode member demand C matched state.compiled.known state.reach.current
    (fun live => (state.compiled.live live).2.layout) ledger.indirect byte canonical

/-- Source typing, source byte room, and the independent final reference
log construct all demands for actual stateful bulk reader acceptance. -/
theorem IndexedTableReaderCompilerPointWasm2.stateful_bulk_available_from_source {A : Type}
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
    (subopcode : U32) (prefixEnd : Usize) (member : subopcode.val ∈ [8,9,10,11,12,13,14,15,16,17])
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
  obtain ⟨op,a,b,_,callback,_⟩ := reader_stateful_bulk_wasm2 pending recorder before after out
    ⟨sourceLocals,ft.results⟩ subopcode prefixEnd member byte decoded canonical
  rw [stateful_callback_invoke] at callback
  have operands := (source_callback_demand before after final out.core (statefulAction op a b) (.Ok ()) out data env
    ⟨sourceLocals,ft.results⟩ index .Wasm2 (.Ok ()) callback tail).1
  have demand := room.demand budget state.compiled.metadata state.compiled.codeBudget state.compiled.sources
    state.compiled.cursor inbounds out.core operands
  rw [byte]
  exact reached_profile_stateful_bulk_available_wasm2 pending ops bound allocation recorder before after compiler out
    ⟨sourceLocals,ft.results⟩ subopcode prefixEnd member decoded demand C matched state.compiled.known state.reach.current
    (fun live => (state.compiled.live live).2.layout) ledger.indirect byte canonical

end Itasca.Runtime.Code

end
