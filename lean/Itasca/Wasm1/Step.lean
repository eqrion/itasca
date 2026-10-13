import Itasca.Wasm1.Run
import Itasca.Wasm1.StepScalar
import Itasca.Wasm1.StepEnv
import Itasca.Wasm1.StepControl
import Itasca.Wasm1.StepBranch

open Aeneas Aeneas.Std

namespace Itasca.Wasm


private theorem memory_meaning_exists (opcode : U8)
    (hlo : 0x28 ≤ opcode.val) (hhi : opcode.val ≤ 0x3E) :
    ∃ operation, MemoryMeaning.opcodeMeaning opcode = some operation := by
  rcases opcode with ⟨⟨n, hn⟩⟩
  change 40 ≤ n at hlo
  change n ≤ 62 at hhi
  interval_cases n <;> exact ⟨_, rfl⟩

/-- Every possible opcode byte either preserves the invariant or returns an
ordinary validation error. No lexical or immediate-validity premise is used. -/
theorem steps {V : Type} (visitor : code.OpVisitor V) (hvisitor : FullVisitor.Total visitor)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (bt : code.BlockType) :
    Steps visitor data env ctx bt := by
  intro st p v
  generalize hbyte : data.val[p.start.val]'p.inbounds = opcode
  by_cases hhigh : 0x45 ≤ opcode.val
  · exact p.step_numeric visitor hvisitor v opcode hbyte hhigh
  by_cases hmemory : 0x28 ≤ opcode.val ∧ opcode.val ≤ 0x3E
  · obtain ⟨operation, hm⟩ := memory_meaning_exists opcode hmemory.1 hmemory.2
    exact p.step_memory visitor v hvisitor opcode operation hbyte hm
  by_cases h_nop : opcode = code.OP_NOP
  · rw [h_nop] at hbyte ⊢
    exact p.step_nop visitor hvisitor v hbyte
  by_cases h_unreachable : opcode = code.OP_UNREACHABLE
  · rw [h_unreachable] at hbyte ⊢
    exact p.step_unreachable visitor hvisitor v hbyte
  by_cases h_i32Const : opcode = code.OP_I32_CONST
  · rw [h_i32Const] at hbyte ⊢
    exact p.step_i32Const visitor hvisitor v hbyte
  by_cases h_i64Const : opcode = code.OP_I64_CONST
  · rw [h_i64Const] at hbyte ⊢
    exact p.step_i64Const visitor hvisitor v hbyte
  by_cases h_f32Const : opcode = code.OP_F32_CONST
  · rw [h_f32Const] at hbyte ⊢
    exact p.step_f32Const visitor hvisitor v hbyte
  by_cases h_f64Const : opcode = code.OP_F64_CONST
  · rw [h_f64Const] at hbyte ⊢
    exact p.step_f64Const visitor hvisitor v hbyte
  by_cases h_drop : opcode = code.OP_DROP
  · rw [h_drop] at hbyte ⊢
    exact p.step_drop visitor hvisitor v hbyte
  by_cases h_select : opcode = code.OP_SELECT
  · rw [h_select] at hbyte ⊢
    exact p.step_select visitor hvisitor v hbyte
  by_cases h_block : opcode = code.OP_BLOCK
  · rw [h_block] at hbyte ⊢
    exact p.step_block visitor hvisitor v hbyte
  by_cases h_loop : opcode = code.OP_LOOP
  · rw [h_loop] at hbyte ⊢
    exact p.step_loop visitor hvisitor v hbyte
  by_cases h_if : opcode = code.OP_IF
  · rw [h_if] at hbyte ⊢
    exact p.step_if visitor hvisitor v hbyte
  by_cases h_else : opcode = code.OP_ELSE
  · rw [h_else] at hbyte ⊢
    exact p.step_else visitor hvisitor v hbyte
  by_cases h_end : opcode = code.OP_END
  · rw [h_end] at hbyte ⊢
    exact p.step_end visitor hvisitor v hbyte
  by_cases h_br : opcode = code.OP_BR
  · rw [h_br] at hbyte ⊢
    exact p.step_br visitor hvisitor v hbyte
  by_cases h_brIf : opcode = code.OP_BR_IF
  · rw [h_brIf] at hbyte ⊢
    exact p.step_brIf visitor hvisitor v hbyte
  by_cases h_brTable : opcode = code.OP_BR_TABLE
  · rw [h_brTable] at hbyte ⊢
    exact p.step_brTable visitor hvisitor v hbyte
  by_cases h_return : opcode = code.OP_RETURN
  · rw [h_return] at hbyte ⊢
    exact p.step_return visitor hvisitor v hbyte
  by_cases h_local_get : opcode = code.OP_LOCAL_GET
  · rw [h_local_get] at hbyte ⊢
    exact p.step_local_get visitor v hvisitor (by simpa only [code.OP_LOCAL_GET] using hbyte)
  by_cases h_local_set : opcode = code.OP_LOCAL_SET
  · rw [h_local_set] at hbyte ⊢
    exact p.step_local_set visitor v hvisitor (by simpa only [code.OP_LOCAL_SET] using hbyte)
  by_cases h_local_tee : opcode = code.OP_LOCAL_TEE
  · rw [h_local_tee] at hbyte ⊢
    exact p.step_local_tee visitor v hvisitor (by simpa only [code.OP_LOCAL_TEE] using hbyte)
  by_cases h_global_get : opcode = code.OP_GLOBAL_GET
  · rw [h_global_get] at hbyte ⊢
    exact p.step_global_get visitor v hvisitor (by simpa only [code.OP_GLOBAL_GET] using hbyte)
  by_cases h_global_set : opcode = code.OP_GLOBAL_SET
  · rw [h_global_set] at hbyte ⊢
    exact p.step_global_set visitor v hvisitor (by simpa only [code.OP_GLOBAL_SET] using hbyte)
  by_cases h_call : opcode = code.OP_CALL
  · rw [h_call] at hbyte ⊢
    exact p.step_call visitor v hvisitor (by simpa only [code.OP_CALL] using hbyte)
  by_cases h_call_indirect : opcode = code.OP_CALL_INDIRECT
  · rw [h_call_indirect] at hbyte ⊢
    exact p.step_call_indirect visitor v hvisitor (by simpa only [code.OP_CALL_INDIRECT] using hbyte)
  by_cases h_memory_size : opcode = code.OP_MEMORY_SIZE
  · rw [h_memory_size] at hbyte ⊢
    exact p.step_memory_size visitor v hvisitor (by simpa only [code.OP_MEMORY_SIZE] using hbyte)
  by_cases h_memory_grow : opcode = code.OP_MEMORY_GROW
  · rw [h_memory_grow] at hbyte ⊢
    exact p.step_memory_grow visitor v hvisitor (by simpa only [code.OP_MEMORY_GROW] using hbyte)
  have hreserved : (0x06 ≤ opcode.val ∧ opcode.val ≤ 0x0A) ∨
      (0x12 ≤ opcode.val ∧ opcode.val ≤ 0x19) ∨
      (0x1C ≤ opcode.val ∧ opcode.val ≤ 0x1F) ∨
      (0x25 ≤ opcode.val ∧ opcode.val ≤ 0x27) := by
    simp only [global_simps] at *
    scalar_tac
  rw [code.step.reserved visitor st data env ctx opcode v hreserved]
  simp

end Itasca.Wasm
