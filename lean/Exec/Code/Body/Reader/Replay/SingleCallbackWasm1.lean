import Exec.Code.Body.Reader.Publication.NonScopeCallbackPublication
import Itasca.Visitor.StepRefinement

namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- Accepted base-reader steps outside scope boundaries and branch-table
collection call exactly one visitor event at their returned validator state. -/
theorem reader_single_callback_wasm1 {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (opcode : U8) (before after : V) (out : code.OpIterState)
    (blocked : opcode ≠ code.OP_BLOCK ∧ opcode ≠ code.OP_LOOP ∧ opcode ≠ code.OP_IF ∧
      opcode ≠ code.OP_END ∧ opcode ≠ code.OP_BR_TABLE)
    (accepted : code.step visitor st data env ctx opcode before = .ok (.Ok (),out,after)) :
    ∃ action, NoScopeBoundary action ∧ PublicationActionRange action ∧
      invoke visitor before (.op out action) = .ok (.Ok (),after) := by
  cases hn : Numeric.opcodeMeaning opcode with
  | some operation =>
    obtain ⟨hook,hhook,_,_⟩ := NumericHook.of_meaning hn
    rw [dispatch_numeric visitor st data env ctx before opcode operation hook hn hhook] at accepted
    obtain ⟨arg,_,callback⟩ := reader_run_success _ _ _ _ _ accepted
    refine ⟨_,?_,?_,callback⟩ <;> trivial
  | none =>
    cases hm : MemoryMeaning.opcodeMeaning opcode with
    | some operation =>
      obtain ⟨hook,hhook,_,_⟩ := MemoryHook.of_meaning hm
      rw [dispatch_memory visitor st data env ctx before opcode operation hook hm hhook] at accepted
      obtain ⟨arg,_,callback⟩ := reader_run_success _ _ _ _ _ accepted
      refine ⟨_,?_,?_,callback⟩ <;> trivial
    | none =>
      by_cases h_nop : opcode = code.OP_NOP
      · subst opcode
        rw [dispatch_nop visitor st data env ctx before] at accepted
        obtain ⟨arg,_,callback⟩ := reader_run_success _ _ _ _ _ accepted
        refine ⟨_,?_,?_,callback⟩ <;> trivial
      by_cases h_unreachable : opcode = code.OP_UNREACHABLE
      · subst opcode
        rw [dispatch_unreachable visitor st data env ctx before] at accepted
        obtain ⟨arg,_,callback⟩ := reader_run_success _ _ _ _ _ accepted
        refine ⟨_,?_,?_,callback⟩ <;> trivial
      by_cases h_i32_const : opcode = code.OP_I32_CONST
      · subst opcode
        rw [dispatch_i32_const visitor st data env ctx before] at accepted
        obtain ⟨arg,_,callback⟩ := reader_run_success _ _ _ _ _ accepted
        refine ⟨_,?_,?_,callback⟩ <;> trivial
      by_cases h_i64_const : opcode = code.OP_I64_CONST
      · subst opcode
        rw [dispatch_i64_const visitor st data env ctx before] at accepted
        obtain ⟨arg,_,callback⟩ := reader_run_success _ _ _ _ _ accepted
        refine ⟨_,?_,?_,callback⟩ <;> trivial
      by_cases h_f32_const : opcode = code.OP_F32_CONST
      · subst opcode
        rw [dispatch_f32_const visitor st data env ctx before] at accepted
        obtain ⟨arg,_,callback⟩ := reader_run_success _ _ _ _ _ accepted
        refine ⟨_,?_,?_,callback⟩ <;> trivial
      by_cases h_f64_const : opcode = code.OP_F64_CONST
      · subst opcode
        rw [dispatch_f64_const visitor st data env ctx before] at accepted
        obtain ⟨arg,_,callback⟩ := reader_run_success _ _ _ _ _ accepted
        refine ⟨_,?_,?_,callback⟩ <;> trivial
      by_cases h_drop : opcode = code.OP_DROP
      · subst opcode
        rw [dispatch_drop visitor st data env ctx before] at accepted
        obtain ⟨arg,_,callback⟩ := reader_run_success _ _ _ _ _ accepted
        refine ⟨_,?_,?_,callback⟩ <;> trivial
      by_cases h_select : opcode = code.OP_SELECT
      · subst opcode
        rw [dispatch_select visitor st data env ctx before] at accepted
        obtain ⟨arg,_,callback⟩ := reader_run_success _ _ _ _ _ accepted
        refine ⟨_,?_,?_,callback⟩ <;> trivial
      by_cases h_block : opcode = code.OP_BLOCK
      · exact False.elim (blocked.1 h_block)
      by_cases h_loop : opcode = code.OP_LOOP
      · exact False.elim (blocked.2.1 h_loop)
      by_cases h_if : opcode = code.OP_IF
      · exact False.elim (blocked.2.2.1 h_if)
      by_cases h_else : opcode = code.OP_ELSE
      · subst opcode
        rw [dispatch_else visitor st data env ctx before] at accepted
        obtain ⟨arg,_,callback⟩ := reader_run_success _ _ _ _ _ accepted
        refine ⟨_,?_,?_,callback⟩ <;> trivial
      by_cases h_end : opcode = code.OP_END
      · exact False.elim (blocked.2.2.2.1 h_end)
      by_cases h_br : opcode = code.OP_BR
      · subst opcode
        rw [dispatch_br visitor st data env ctx before] at accepted
        obtain ⟨arg,_,callback⟩ := reader_run_success _ _ _ _ _ accepted
        refine ⟨_,?_,?_,callback⟩ <;> trivial
      by_cases h_br_if : opcode = code.OP_BR_IF
      · subst opcode
        rw [dispatch_br_if visitor st data env ctx before] at accepted
        obtain ⟨arg,_,callback⟩ := reader_run_success _ _ _ _ _ accepted
        refine ⟨_,?_,?_,callback⟩ <;> trivial
      by_cases h_br_table : opcode = code.OP_BR_TABLE
      · exact False.elim (blocked.2.2.2.2 h_br_table)
      by_cases h_return : opcode = code.OP_RETURN
      · subst opcode
        rw [dispatch_return visitor st data env ctx before] at accepted
        obtain ⟨arg,_,callback⟩ := reader_run_success _ _ _ _ _ accepted
        refine ⟨_,?_,?_,callback⟩ <;> trivial
      by_cases h_call : opcode = code.OP_CALL
      · subst opcode
        rw [dispatch_call visitor st data env ctx before] at accepted
        obtain ⟨arg,_,callback⟩ := reader_run_success _ _ _ _ _ accepted
        refine ⟨_,?_,?_,callback⟩ <;> trivial
      by_cases h_call_indirect : opcode = code.OP_CALL_INDIRECT
      · subst opcode
        rw [dispatch_call_indirect visitor st data env ctx before] at accepted
        obtain ⟨arg,_,callback⟩ := reader_run_success _ _ _ _ _ accepted
        refine ⟨_,?_,?_,callback⟩ <;> trivial
      by_cases h_local_get : opcode = code.OP_LOCAL_GET
      · subst opcode
        rw [dispatch_local_get visitor st data env ctx before] at accepted
        obtain ⟨arg,_,callback⟩ := reader_run_success _ _ _ _ _ accepted
        refine ⟨_,?_,?_,callback⟩ <;> trivial
      by_cases h_local_set : opcode = code.OP_LOCAL_SET
      · subst opcode
        rw [dispatch_local_set visitor st data env ctx before] at accepted
        obtain ⟨arg,_,callback⟩ := reader_run_success _ _ _ _ _ accepted
        refine ⟨_,?_,?_,callback⟩ <;> trivial
      by_cases h_local_tee : opcode = code.OP_LOCAL_TEE
      · subst opcode
        rw [dispatch_local_tee visitor st data env ctx before] at accepted
        obtain ⟨arg,_,callback⟩ := reader_run_success _ _ _ _ _ accepted
        refine ⟨_,?_,?_,callback⟩ <;> trivial
      by_cases h_global_get : opcode = code.OP_GLOBAL_GET
      · subst opcode
        rw [dispatch_global_get visitor st data env ctx before] at accepted
        obtain ⟨arg,_,callback⟩ := reader_run_success _ _ _ _ _ accepted
        refine ⟨_,?_,?_,callback⟩ <;> trivial
      by_cases h_global_set : opcode = code.OP_GLOBAL_SET
      · subst opcode
        rw [dispatch_global_set visitor st data env ctx before] at accepted
        obtain ⟨arg,_,callback⟩ := reader_run_success _ _ _ _ _ accepted
        refine ⟨_,?_,?_,callback⟩ <;> trivial
      by_cases h_memory_size : opcode = code.OP_MEMORY_SIZE
      · subst opcode
        rw [dispatch_memory_size visitor st data env ctx before] at accepted
        obtain ⟨arg,_,callback⟩ := reader_run_success _ _ _ _ _ accepted
        refine ⟨_,?_,?_,callback⟩ <;> trivial
      by_cases h_memory_grow : opcode = code.OP_MEMORY_GROW
      · subst opcode
        rw [dispatch_memory_grow visitor st data env ctx before] at accepted
        obtain ⟨arg,_,callback⟩ := reader_run_success _ _ _ _ _ accepted
        refine ⟨_,?_,?_,callback⟩ <;> trivial
      have heqval (a b : U8) : a = b ↔ a.val = b.val :=
        ⟨fun h => congrArg UScalar.val h,UScalar.eq_of_val_eq⟩
      have dispatch : code.step visitor st data env ctx opcode before = code.step_memory visitor st data env opcode before := by
        unfold code.step
        split <;> simp_all [global_simps,U8.ofNat,UScalar.ofNat,UScalar.ofNatCore]
      rw [dispatch,OpDispatch.memory_fallback visitor st data env opcode before hm h_memory_size h_memory_grow,
        code.step_numeric.unrecognized visitor st opcode before hn] at accepted
      simp at accepted

end Exec.Code
