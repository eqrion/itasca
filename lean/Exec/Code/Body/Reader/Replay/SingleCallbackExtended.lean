import Exec.Code.Body.Reader.Replay.SingleCallbackRun
import Exec.Code.Body.Reader.Replay.SingleCallbackWasm1
import Itasca.Wasm2.Trace.Refinement

namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace Itasca.Wasm2
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

/-- Every accepted bulk-reader step invokes one bounded non-scope event. -/
theorem reader_single_callback_bulk {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (opcode : U32)
    (before after : V) (out : code.OpIterState)
    (accepted : code.step_bulk visitor st data env opcode before = .ok (.Ok (),out,after)) :
    ∃ action, NoScopeBoundary action ∧ PublicationActionRange action ∧
      invoke visitor before (.op out action) = .ok (.Ok (),after) := by
  rw [code.step_bulk.eq_runs] at accepted
  unfold bulkStep at accepted
  split at accepted
  case h_1 =>
    exact reader_single_callback_of_run visitor _ (fun _ a => .memory_init a) before after out
      (by intro arg; exact ⟨True.intro,True.intro⟩) accepted
  case h_2 =>
    exact reader_single_callback_of_run visitor _ (fun _ a => .data_drop a) before after out
      (by intro arg; exact ⟨True.intro,True.intro⟩) accepted
  case h_3 =>
    exact reader_single_callback_of_run visitor _ (fun _ _ => .memory_copy) before after out
      (by intro arg; exact ⟨True.intro,True.intro⟩) accepted
  case h_4 =>
    exact reader_single_callback_of_run visitor _ (fun _ _ => .memory_fill) before after out
      (by intro arg; exact ⟨True.intro,True.intro⟩) accepted
  case h_5 =>
    exact reader_single_callback_of_run visitor _ (fun _ (a : U32 × U32) => .table_init a.1 a.2) before after out
      (by intro arg; exact ⟨True.intro,True.intro⟩) accepted
  case h_6 =>
    exact reader_single_callback_of_run visitor _ (fun _ (a : U32 × types.ValueType) => .elem_drop a.1) before after out
      (by intro arg; exact ⟨True.intro,True.intro⟩) accepted
  case h_7 =>
    exact reader_single_callback_of_run visitor _ (fun _ (a : U32 × U32) => .table_copy a.1 a.2) before after out
      (by intro arg; exact ⟨True.intro,True.intro⟩) accepted
  case h_8 =>
    exact reader_single_callback_of_run visitor _ (fun _ a => .table_grow a) before after out
      (by intro arg; exact ⟨True.intro,True.intro⟩) accepted
  case h_9 =>
    exact reader_single_callback_of_run visitor _ (fun _ a => .table_size a) before after out
      (by intro arg; exact ⟨True.intro,True.intro⟩) accepted
  case h_10 =>
    exact reader_single_callback_of_run visitor _ (fun _ a => .table_fill a) before after out
      (by intro arg; exact ⟨True.intro,True.intro⟩) accepted
  case h_11 => simp at accepted

/-- Accepted sign-extension, saturating conversion and base-reader steps
retain an exact event, with scope and table boundaries explicitly excluded. -/
theorem reader_single_callback_extended {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (opcode : U8) (before after : V) (out : code.OpIterState)
    (blocked : opcode ≠ code.OP_BLOCK ∧ opcode ≠ code.OP_LOOP ∧ opcode ≠ code.OP_IF ∧
      opcode ≠ code.OP_END ∧ opcode ≠ code.OP_BR_TABLE)
    (accepted : code.step_extended visitor st data env ctx opcode before = .ok (.Ok (),out,after)) :
    ∃ action, NoScopeBoundary action ∧ PublicationActionRange action ∧
      invoke visitor before (.op out action) = .ok (.Ok (),after) := by
  cases hm : NumericExtensions.signMeaning opcode with
  | some op =>
    rw [code.step_extended.sign visitor st data env ctx opcode op before hm] at accepted
    have bounds := (NumericExtensions.sign_properties hm).2.2
    rcases opcode with ⟨⟨n,hn⟩⟩
    change 192 ≤ n ∧ n ≤ 196 at bounds
    obtain ⟨lower,upper⟩ := bounds
    interval_cases n
    all_goals first
    | exact reader_single_callback_of_run visitor _ (fun _ _ => .extendedNumeric .i32_extend8_s) before after out
        (by intro arg; exact ⟨True.intro,True.intro⟩) accepted
    | exact reader_single_callback_of_run visitor _ (fun _ _ => .extendedNumeric .i32_extend16_s) before after out
        (by intro arg; exact ⟨True.intro,True.intro⟩) accepted
    | exact reader_single_callback_of_run visitor _ (fun _ _ => .extendedNumeric .i64_extend8_s) before after out
        (by intro arg; exact ⟨True.intro,True.intro⟩) accepted
    | exact reader_single_callback_of_run visitor _ (fun _ _ => .extendedNumeric .i64_extend16_s) before after out
        (by intro arg; exact ⟨True.intro,True.intro⟩) accepted
    | exact reader_single_callback_of_run visitor _ (fun _ _ => .extendedNumeric .i64_extend32_s) before after out
        (by intro arg; exact ⟨True.intro,True.intro⟩) accepted
  | none =>
    by_cases prefixByte : opcode = code.OP_MISC_PREFIX
    · have byte : opcode = 0xfc#u8 := by simpa [global_simps] using prefixByte
      rw [byte,code.step_extended.prefixed] at accepted
      obtain ⟨read,called⟩ := reader.read_u32_leb.total data st.pos
      simp only [prefixedStep,called,bind_ok] at accepted
      cases read with
      | Err error => simp at accepted
      | Ok pair =>
        obtain ⟨sub,next⟩ := pair
        cases hs : NumericExtensions.saturatingMeaning sub with
        | none => simp [hs] at accepted
        | some op =>
          simp only [hs] at accepted
          have bound : sub.val < 8 := by
            unfold NumericExtensions.saturatingMeaning at hs
            split at hs <;> simp_all
          rcases sub with ⟨⟨n,hn⟩⟩
          change n < 8 at bound
          interval_cases n
          all_goals first
          | exact reader_single_callback_of_run visitor _ (fun _ _ => .extendedNumeric .i32_trunc_sat_f32_s) before after out
              (by intro arg; exact ⟨True.intro,True.intro⟩) accepted
          | exact reader_single_callback_of_run visitor _ (fun _ _ => .extendedNumeric .i32_trunc_sat_f32_u) before after out
              (by intro arg; exact ⟨True.intro,True.intro⟩) accepted
          | exact reader_single_callback_of_run visitor _ (fun _ _ => .extendedNumeric .i32_trunc_sat_f64_s) before after out
              (by intro arg; exact ⟨True.intro,True.intro⟩) accepted
          | exact reader_single_callback_of_run visitor _ (fun _ _ => .extendedNumeric .i32_trunc_sat_f64_u) before after out
              (by intro arg; exact ⟨True.intro,True.intro⟩) accepted
          | exact reader_single_callback_of_run visitor _ (fun _ _ => .extendedNumeric .i64_trunc_sat_f32_s) before after out
              (by intro arg; exact ⟨True.intro,True.intro⟩) accepted
          | exact reader_single_callback_of_run visitor _ (fun _ _ => .extendedNumeric .i64_trunc_sat_f32_u) before after out
              (by intro arg; exact ⟨True.intro,True.intro⟩) accepted
          | exact reader_single_callback_of_run visitor _ (fun _ _ => .extendedNumeric .i64_trunc_sat_f64_s) before after out
              (by intro arg; exact ⟨True.intro,True.intro⟩) accepted
          | exact reader_single_callback_of_run visitor _ (fun _ _ => .extendedNumeric .i64_trunc_sat_f64_u) before after out
              (by intro arg; exact ⟨True.intro,True.intro⟩) accepted
    · rw [code.step_extended.base visitor st data env ctx opcode before hm prefixByte] at accepted
      exact reader_single_callback_wasm1 visitor st data env ctx opcode before after out blocked accepted

end Exec.Code
