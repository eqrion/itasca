import Itasca.Wasm1.Trace.Leaves
import Itasca.Wasm1.Trace.Control
import Itasca.Wasm1.Trace.BodyContract

/-!
# Step contract for all opcodes

`VisitorTrace.steps` proves `StepContract` by case analysis on the opcode byte, combining the
leaf and control `StepRecords` theorems with the silent cases for unrecognized numeric opcodes
and reserved bytes.
-/

open Aeneas Aeneas.Std

namespace Itasca.VisitorTrace

private theorem memory_meaning_exists (opcode : U8)
    (hlo : 0x28 ≤ opcode.val) (hhi : opcode.val ≤ 0x3E) :
    ∃ operation, MemoryMeaning.opcodeMeaning opcode = some operation := by
  rcases opcode with ⟨⟨n, hn⟩⟩
  change 40 ≤ n at hlo
  change n ≤ 62 at hhi
  interval_cases n <;> exact ⟨_, rfl⟩

/-- For all 256 opcode bytes, every successful callback has independent byte provenance, and a
rejection leaves exactly the callbacks reported so far. -/
theorem steps {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (hrecords : Records visitor observe) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (bt : code.BlockType) :
    StepContract visitor observe data env ctx bt := by
  intro st p
  generalize hbyte : data.val[p.start.val]'p.inbounds = opcode
  by_cases hhigh : 0x45 ≤ opcode.val
  · cases hm : Numeric.opcodeMeaning opcode with
    | some operation => exact step_numeric p visitor observe hrecords opcode operation hbyte hm
    | none =>
      intro v result final v' h
      rw [code.step.numeric_dispatch visitor st data env ctx opcode v hhigh,
        code.step_numeric.unrecognized visitor st opcode v hm] at h
      simp only [Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨[], by simp, .silent _ _ (.empty _)⟩
  by_cases hmemory : 0x28 ≤ opcode.val ∧ opcode.val ≤ 0x3E
  · obtain ⟨operation, hm⟩ := memory_meaning_exists opcode hmemory.1 hmemory.2
    exact step_memory p visitor observe hrecords opcode operation hbyte hm
  by_cases h_nop : opcode = code.OP_NOP
  · rw [h_nop] at hbyte ⊢
    exact step_nop p visitor observe hrecords hbyte
  by_cases h_unreachable : opcode = code.OP_UNREACHABLE
  · rw [h_unreachable] at hbyte ⊢
    exact step_unreachable p visitor observe hrecords hbyte
  by_cases h_i32_const : opcode = code.OP_I32_CONST
  · rw [h_i32_const] at hbyte ⊢
    exact step_i32_const p visitor observe hrecords hbyte
  by_cases h_i64_const : opcode = code.OP_I64_CONST
  · rw [h_i64_const] at hbyte ⊢
    exact step_i64_const p visitor observe hrecords hbyte
  by_cases h_f32_const : opcode = code.OP_F32_CONST
  · rw [h_f32_const] at hbyte ⊢
    exact step_f32_const p visitor observe hrecords hbyte
  by_cases h_f64_const : opcode = code.OP_F64_CONST
  · rw [h_f64_const] at hbyte ⊢
    exact step_f64_const p visitor observe hrecords hbyte
  by_cases h_drop : opcode = code.OP_DROP
  · rw [h_drop] at hbyte ⊢
    exact step_drop p visitor observe hrecords hbyte
  by_cases h_select : opcode = code.OP_SELECT
  · rw [h_select] at hbyte ⊢
    exact step_select p visitor observe hrecords hbyte
  by_cases h_block : opcode = code.OP_BLOCK
  · rw [h_block] at hbyte ⊢
    exact step_block p visitor observe hrecords hbyte
  by_cases h_loop : opcode = code.OP_LOOP
  · rw [h_loop] at hbyte ⊢
    exact step_loop p visitor observe hrecords hbyte
  by_cases h_if : opcode = code.OP_IF
  · rw [h_if] at hbyte ⊢
    exact step_if p visitor observe hrecords hbyte
  by_cases h_else : opcode = code.OP_ELSE
  · rw [h_else] at hbyte ⊢
    exact step_else p visitor observe hrecords hbyte
  by_cases h_end : opcode = code.OP_END
  · rw [h_end] at hbyte ⊢
    exact step_end p visitor observe hrecords hbyte
  by_cases h_br : opcode = code.OP_BR
  · rw [h_br] at hbyte ⊢
    exact step_br p visitor observe hrecords hbyte
  by_cases h_br_if : opcode = code.OP_BR_IF
  · rw [h_br_if] at hbyte ⊢
    exact step_br_if p visitor observe hrecords hbyte
  by_cases h_br_table : opcode = code.OP_BR_TABLE
  · rw [h_br_table] at hbyte ⊢
    exact step_br_table p visitor observe hrecords hbyte
  by_cases h_return : opcode = code.OP_RETURN
  · rw [h_return] at hbyte ⊢
    exact step_return p visitor observe hrecords hbyte
  by_cases h_local_get : opcode = code.OP_LOCAL_GET
  · rw [h_local_get] at hbyte ⊢
    exact step_local_get p visitor observe hrecords hbyte
  by_cases h_local_set : opcode = code.OP_LOCAL_SET
  · rw [h_local_set] at hbyte ⊢
    exact step_local_set p visitor observe hrecords hbyte
  by_cases h_local_tee : opcode = code.OP_LOCAL_TEE
  · rw [h_local_tee] at hbyte ⊢
    exact step_local_tee p visitor observe hrecords hbyte
  by_cases h_global_get : opcode = code.OP_GLOBAL_GET
  · rw [h_global_get] at hbyte ⊢
    exact step_global_get p visitor observe hrecords hbyte
  by_cases h_global_set : opcode = code.OP_GLOBAL_SET
  · rw [h_global_set] at hbyte ⊢
    exact step_global_set p visitor observe hrecords hbyte
  by_cases h_call : opcode = code.OP_CALL
  · rw [h_call] at hbyte ⊢
    exact step_call p visitor observe hrecords hbyte
  by_cases h_call_indirect : opcode = code.OP_CALL_INDIRECT
  · rw [h_call_indirect] at hbyte ⊢
    exact step_call_indirect p visitor observe hrecords hbyte
  by_cases h_memory_size : opcode = code.OP_MEMORY_SIZE
  · rw [h_memory_size] at hbyte ⊢
    exact step_memory_size p visitor observe hrecords hbyte
  by_cases h_memory_grow : opcode = code.OP_MEMORY_GROW
  · rw [h_memory_grow] at hbyte ⊢
    exact step_memory_grow p visitor observe hrecords hbyte
  have hreserved : (0x06 ≤ opcode.val ∧ opcode.val ≤ 0x0A) ∨
      (0x12 ≤ opcode.val ∧ opcode.val ≤ 0x19) ∨
      (0x1C ≤ opcode.val ∧ opcode.val ≤ 0x1F) ∨
      (0x25 ≤ opcode.val ∧ opcode.val ≤ 0x27) := by
    simp only [global_simps] at *
    scalar_tac
  intro v result final v' h
  rw [code.step.reserved visitor st data env ctx opcode v hreserved] at h
  simp only [Result.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨[], by simp, .silent _ _ (.empty _)⟩

end Itasca.VisitorTrace
