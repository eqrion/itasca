import Exec.Code.Local.Capacity.ReaderAcceptance
import Exec.Code.Body.Reader.Acceptance.StatefulCallbackAcceptance
import Exec.Code.Body.Reader.Common.StatefulReaderBase
import Exec.Code.Body.Reader.Acceptance.ReaderProfileAcceptance

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
