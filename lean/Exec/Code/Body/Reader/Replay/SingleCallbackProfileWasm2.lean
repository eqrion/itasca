import Exec.Code.Body.Reader.Replay.SingleCallbackWasm2
import Exec.Code.Body.Reader.Common.ReaderProfile
import Exec.Code.Body.Reader.Common.ReaderEnterWasm2
import Itasca.Wasm2.Trace.ControlRecords

namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace Itasca.Wasm2
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- Wasm 2 profile dispatch outside entry, END and table collection selects one
actual event at the returned core state, including its control callbacks. -/
theorem reader_single_callback_profile_wasm2 {V : Type} (visitor : code.OpVisitor V)
    (st out : code.BodyState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (index : U32) (opcode : U8) (before after : V)
    (blocked : opcode ≠ code.OP_BLOCK ∧ opcode ≠ code.OP_LOOP ∧ opcode ≠ code.OP_IF ∧
      opcode ≠ code.OP_END ∧ opcode ≠ code.OP_BR_TABLE)
    (accepted : code.step_profile visitor st data env ctx index .Wasm2 opcode before = .ok (.Ok (),out,after)) :
    ∃ action, NoScopeBoundary action ∧ PublicationActionRange action ∧
      invoke visitor before (.op out.core action) = .ok (.Ok (),after) := by
  by_cases h5 : opcode = 5#u8
  · rw [h5,CallbackTrace.dispatch_else] at accepted
    obtain ⟨arg,_,callback⟩ := reader_body_success _ _ _ _ _ _ accepted
    exact ⟨.else_ arg.2,True.intro,True.intro,callback⟩
  by_cases h12 : opcode = 12#u8
  · rw [h12,CallbackTrace.dispatch_br] at accepted
    obtain ⟨arg,_,callback⟩ := reader_body_success _ _ _ _ _ _ accepted
    exact ⟨.br arg.1 arg.2,True.intro,True.intro,callback⟩
  by_cases h13 : opcode = 13#u8
  · rw [h13,CallbackTrace.dispatch_br_if] at accepted
    obtain ⟨arg,_,callback⟩ := reader_body_success _ _ _ _ _ _ accepted
    exact ⟨.br_if arg.1 arg.2,True.intro,True.intro,callback⟩
  by_cases h15 : opcode = 15#u8
  · rw [h15,CallbackTrace.dispatch_return] at accepted
    obtain ⟨arg,_,callback⟩ := reader_body_success _ _ _ _ _ _ accepted
    exact ⟨.return_,True.intro,True.intro,callback⟩
  by_cases h16 : opcode = 16#u8
  · rw [h16,CallbackTrace.dispatch_call] at accepted
    obtain ⟨arg,_,callback⟩ := reader_body_success _ _ _ _ _ _ accepted
    exact ⟨.call arg,True.intro,True.intro,callback⟩
  by_cases h17 : opcode = 17#u8
  · rw [h17,CallbackTrace.dispatch_call_indirect] at accepted
    obtain ⟨arg,_,callback⟩ := reader_body_success _ _ _ _ _ _ accepted
    exact ⟨.call_indirect arg.1 arg.2,True.intro,True.intro,callback⟩
  have blocked' : opcode ≠ 2#u8 ∧ opcode ≠ 3#u8 ∧ opcode ≠ 4#u8 ∧ opcode ≠ 11#u8 ∧ opcode ≠ 14#u8 := by
    simpa only [global_simps] using blocked
  have ordinary : opcode.val ∉ controlOpcodes := by
    simp only [controlOpcodes,List.mem_cons,List.not_mem_nil,or_false,not_or]
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    all_goals intro same
    all_goals first
    | exact blocked'.1 (UScalar.eq_of_val_eq same)
    | exact blocked'.2.1 (UScalar.eq_of_val_eq same)
    | exact blocked'.2.2.1 (UScalar.eq_of_val_eq same)
    | exact blocked'.2.2.2.1 (UScalar.eq_of_val_eq same)
    | exact blocked'.2.2.2.2 (UScalar.eq_of_val_eq same)
    | exact h5 (UScalar.eq_of_val_eq same)
    | exact h12 (UScalar.eq_of_val_eq same)
    | exact h13 (UScalar.eq_of_val_eq same)
    | exact h15 (UScalar.eq_of_val_eq same)
    | exact h16 (UScalar.eq_of_val_eq same)
    | exact h17 (UScalar.eq_of_val_eq same)
  obtain ⟨_,raw⟩ := profile_scalar_success visitor st out data env ctx index opcode before after ordinary accepted
  exact reader_single_callback_wasm2 visitor st.core data env ctx opcode before after out.core blocked raw

end Exec.Code
