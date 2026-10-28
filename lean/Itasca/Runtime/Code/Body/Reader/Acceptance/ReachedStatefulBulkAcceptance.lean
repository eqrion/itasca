import Itasca.Runtime.Code.Local.Capacity.ReaderAcceptance
import Itasca.Runtime.Code.Body.Reader.Acceptance.StatefulCallbackAcceptance
import Itasca.Runtime.Code.Body.Reader.Common.StatefulReaderBulkDispatch
import Itasca.Runtime.Code.Body.Reader.Acceptance.ReaderProfileAcceptance

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
