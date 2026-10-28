import Itasca.Runtime.Code.Body.Reader.Replay.SingleCallbackExtended
import Itasca.Runtime.Code.Body.Reader.Simd.SingleCallbackSimd

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace Itasca.Wasm2
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

/-- Every accepted complete-profile noncontrol dispatcher step selects one
actual callback at its returned state, with source-bounded SIMD arguments. -/
theorem reader_single_callback_wasm2 {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (opcode : U8) (before after : V) (out : code.OpIterState)
    (accepted : code.step_wasm2 visitor st data env ctx opcode before = .ok (.Ok (),out,after)) :
    ∃ action, NoScopeBoundary action ∧ PublicationActionRange action ∧
      invoke visitor before (.op out action) = .ok (.Ok (),after) := by
  by_cases h253 : opcode = 253#u8
  · subst opcode
    exact reader_single_callback_simd visitor st data env before after out accepted
  by_cases h28 : opcode = 28#u8
  · rw [h28,code.step_wasm2.typed_select] at accepted
    obtain ⟨arg,_,callback⟩ := reader_run_success _ _ _ _ _ accepted
    exact ⟨.select_typed arg,True.intro,True.intro,callback⟩
  by_cases h37 : opcode = 37#u8
  · rw [h37,code.step_wasm2.table_get] at accepted
    obtain ⟨arg,_,callback⟩ := reader_run_success _ _ _ _ _ accepted
    exact ⟨.table_get arg,True.intro,True.intro,callback⟩
  by_cases h38 : opcode = 38#u8
  · rw [h38,code.step_wasm2.table_set] at accepted
    obtain ⟨arg,_,callback⟩ := reader_run_success _ _ _ _ _ accepted
    exact ⟨.table_set arg,True.intro,True.intro,callback⟩
  by_cases h208 : opcode = 208#u8
  · rw [h208,code.step_wasm2.ref_null] at accepted
    obtain ⟨arg,_,callback⟩ := reader_run_success _ _ _ _ _ accepted
    exact ⟨.ref_null arg,True.intro,True.intro,callback⟩
  by_cases h209 : opcode = 209#u8
  · rw [h209,code.step_wasm2.ref_is_null] at accepted
    obtain ⟨arg,_,callback⟩ := reader_run_success _ _ _ _ _ accepted
    exact ⟨.ref_is_null,True.intro,True.intro,callback⟩
  by_cases h210 : opcode = 210#u8
  · rw [h210,code.step_wasm2.ref_func] at accepted
    obtain ⟨arg,_,callback⟩ := reader_run_success _ _ _ _ _ accepted
    exact ⟨.ref_func arg,True.intro,True.intro,callback⟩
  by_cases h252 : opcode = 252#u8
  · rw [h252,code.step_wasm2.prefixed] at accepted
    obtain ⟨read,called⟩ := reader.read_u32_leb.total data st.pos
    simp only [wasm2PrefixedStep,called,bind_ok] at accepted
    cases read with
    | Err error => simp at accepted
    | Ok pair =>
      obtain ⟨sub,next⟩ := pair
      dsimp only at accepted
      split at accepted
      · exact reader_single_callback_extended visitor st data env ctx 0xfc#u8 before after out accepted
      · exact reader_single_callback_bulk visitor {st with pos := next} data env sub before after out accepted
  have base : opcode.val ∉ [28,37,38,208,209,210,252,253] := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
    have neq {a b : U8} (h : a ≠ b) : a.val ≠ b.val := fun same => h (UScalar.eq_of_val_eq same)
    exact ⟨neq h28,neq h37,neq h38,neq h208,neq h209,neq h210,neq h252,neq h253⟩
  rw [code.step_wasm2.base visitor st data env ctx opcode before base] at accepted
  exact reader_single_callback_extended visitor st data env ctx opcode before after out accepted

end Itasca.Runtime.Code
