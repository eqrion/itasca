import Itasca.Runtime.Compiler.Body.Reader.Publication.NonScopeCallbackPublication
import Itasca.Wasm2.Trace.Refinement

/-!
Single-callback replay through scalar and extended operations. SIMD replay remains separate because it consumes this construction.
-/

/-! ## Single Callback Run -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Extract the actual accepted callback at the reader's returned state. The
classification concerns event arguments only, independently of compiler code. -/
theorem reader_single_callback_of_run {X V : Type} (visitor : code.OpVisitor V)
    (read : Result (core.result.Result X error.OpError × code.OpIterState))
    (event : code.OpIterState → X → Action) (before after : V) (out : code.OpIterState)
    (supported : ∀ arg, NoScopeBoundary (event out arg) ∧ PublicationActionRange (event out arg))
    (accepted : CoreVisitor.run read (fun v state arg => invoke visitor v (.op state (event state arg))) before =
      .ok (.Ok (),out,after)) :
    ∃ action, NoScopeBoundary action ∧ PublicationActionRange action ∧
      invoke visitor before (.op out action) = .ok (.Ok (),after) := by
  obtain ⟨arg,_,callback⟩ := CoreVisitor.run.accepted _ _ _ _ _ accepted
  exact ⟨event out arg,(supported arg).1,(supported arg).2,callback⟩

end Itasca.Runtime.Compiler

end

/-! ## Single Callback Extended -/

section

namespace Itasca.Runtime.Compiler
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

/-- Accepted base-reader steps call exactly one non-scope visitor event at their returned
validator state. -/
theorem reader_single_callback_base {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (opcode : U8) (before after : V) (out : code.OpIterState)
    (accepted : code.step visitor st data env ctx opcode before = .ok (.Ok (),out,after)) :
    ∃ action, NoScopeBoundary action ∧ PublicationActionRange action ∧
      invoke visitor before (.op out action) = .ok (.Ok (),after) := by
  cases hn : Numeric.opcodeMeaning opcode with
  | some operation =>
    obtain ⟨hook,hhook,_,_⟩ := NumericHook.of_meaning hn
    rw [dispatch_numeric visitor st data env ctx before opcode operation hook hn hhook] at accepted
    obtain ⟨arg,_,callback⟩ := CoreVisitor.run.accepted _ _ _ _ _ accepted
    refine ⟨_,?_,?_,callback⟩ <;> trivial
  | none =>
    cases hm : MemoryMeaning.opcodeMeaning opcode with
    | some operation =>
      obtain ⟨hook,hhook,_,_⟩ := MemoryHook.of_meaning hm
      rw [dispatch_memory visitor st data env ctx before opcode operation hook hm hhook] at accepted
      obtain ⟨arg,_,callback⟩ := CoreVisitor.run.accepted _ _ _ _ _ accepted
      refine ⟨_,?_,?_,callback⟩ <;> trivial
    | none =>
      by_cases h_nop : opcode = code.OP_NOP
      · subst opcode
        rw [dispatch_nop visitor st data env ctx before] at accepted
        obtain ⟨arg,_,callback⟩ := CoreVisitor.run.accepted _ _ _ _ _ accepted
        refine ⟨_,?_,?_,callback⟩ <;> trivial
      by_cases h_unreachable : opcode = code.OP_UNREACHABLE
      · subst opcode
        rw [dispatch_unreachable visitor st data env ctx before] at accepted
        obtain ⟨arg,_,callback⟩ := CoreVisitor.run.accepted _ _ _ _ _ accepted
        refine ⟨_,?_,?_,callback⟩ <;> trivial
      by_cases h_i32_const : opcode = code.OP_I32_CONST
      · subst opcode
        rw [dispatch_i32_const visitor st data env ctx before] at accepted
        obtain ⟨arg,_,callback⟩ := CoreVisitor.run.accepted _ _ _ _ _ accepted
        refine ⟨_,?_,?_,callback⟩ <;> trivial
      by_cases h_i64_const : opcode = code.OP_I64_CONST
      · subst opcode
        rw [dispatch_i64_const visitor st data env ctx before] at accepted
        obtain ⟨arg,_,callback⟩ := CoreVisitor.run.accepted _ _ _ _ _ accepted
        refine ⟨_,?_,?_,callback⟩ <;> trivial
      by_cases h_f32_const : opcode = code.OP_F32_CONST
      · subst opcode
        rw [dispatch_f32_const visitor st data env ctx before] at accepted
        obtain ⟨arg,_,callback⟩ := CoreVisitor.run.accepted _ _ _ _ _ accepted
        refine ⟨_,?_,?_,callback⟩ <;> trivial
      by_cases h_f64_const : opcode = code.OP_F64_CONST
      · subst opcode
        rw [dispatch_f64_const visitor st data env ctx before] at accepted
        obtain ⟨arg,_,callback⟩ := CoreVisitor.run.accepted _ _ _ _ _ accepted
        refine ⟨_,?_,?_,callback⟩ <;> trivial
      by_cases h_drop : opcode = code.OP_DROP
      · subst opcode
        rw [dispatch_drop visitor st data env ctx before] at accepted
        obtain ⟨arg,_,callback⟩ := CoreVisitor.run.accepted _ _ _ _ _ accepted
        refine ⟨_,?_,?_,callback⟩ <;> trivial
      by_cases h_select : opcode = code.OP_SELECT
      · subst opcode
        rw [dispatch_select visitor st data env ctx before] at accepted
        obtain ⟨arg,_,callback⟩ := CoreVisitor.run.accepted _ _ _ _ _ accepted
        refine ⟨_,?_,?_,callback⟩ <;> trivial
      by_cases h_local_get : opcode = code.OP_LOCAL_GET
      · subst opcode
        rw [dispatch_local_get visitor st data env ctx before] at accepted
        obtain ⟨arg,_,callback⟩ := CoreVisitor.run.accepted _ _ _ _ _ accepted
        refine ⟨_,?_,?_,callback⟩ <;> trivial
      by_cases h_local_set : opcode = code.OP_LOCAL_SET
      · subst opcode
        rw [dispatch_local_set visitor st data env ctx before] at accepted
        obtain ⟨arg,_,callback⟩ := CoreVisitor.run.accepted _ _ _ _ _ accepted
        refine ⟨_,?_,?_,callback⟩ <;> trivial
      by_cases h_local_tee : opcode = code.OP_LOCAL_TEE
      · subst opcode
        rw [dispatch_local_tee visitor st data env ctx before] at accepted
        obtain ⟨arg,_,callback⟩ := CoreVisitor.run.accepted _ _ _ _ _ accepted
        refine ⟨_,?_,?_,callback⟩ <;> trivial
      by_cases h_global_get : opcode = code.OP_GLOBAL_GET
      · subst opcode
        rw [dispatch_global_get visitor st data env ctx before] at accepted
        obtain ⟨arg,_,callback⟩ := CoreVisitor.run.accepted _ _ _ _ _ accepted
        refine ⟨_,?_,?_,callback⟩ <;> trivial
      by_cases h_global_set : opcode = code.OP_GLOBAL_SET
      · subst opcode
        rw [dispatch_global_set visitor st data env ctx before] at accepted
        obtain ⟨arg,_,callback⟩ := CoreVisitor.run.accepted _ _ _ _ _ accepted
        refine ⟨_,?_,?_,callback⟩ <;> trivial
      by_cases h_memory_size : opcode = code.OP_MEMORY_SIZE
      · subst opcode
        rw [dispatch_memory_size visitor st data env ctx before] at accepted
        obtain ⟨arg,_,callback⟩ := CoreVisitor.run.accepted _ _ _ _ _ accepted
        refine ⟨_,?_,?_,callback⟩ <;> trivial
      by_cases h_memory_grow : opcode = code.OP_MEMORY_GROW
      · subst opcode
        rw [dispatch_memory_grow visitor st data env ctx before] at accepted
        obtain ⟨arg,_,callback⟩ := CoreVisitor.run.accepted _ _ _ _ _ accepted
        refine ⟨_,?_,?_,callback⟩ <;> trivial
      have heqval (a b : U8) : a = b ↔ a.val = b.val :=
        ⟨fun h => congrArg UScalar.val h,UScalar.eq_of_val_eq⟩
      have dispatch : code.step visitor st data env ctx opcode before = code.step_memory visitor st data env opcode before := by
        unfold code.step
        split <;> simp_all [global_simps,U8.ofNat,UScalar.ofNat,UScalar.ofNatCore]
      rw [dispatch,OpDispatch.memory_fallback visitor st data env opcode before hm h_memory_size h_memory_grow,
        code.step_numeric.unrecognized visitor st opcode before hn] at accepted
      simp at accepted

/-- Accepted sign-extension, saturating conversion and base-reader steps
retain an exact event, with scope and table boundaries explicitly excluded. -/
theorem reader_single_callback_extended {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (opcode : U8) (before after : V) (out : code.OpIterState)
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
      exact reader_single_callback_base visitor st data env ctx opcode before after out accepted

end Itasca.Runtime.Compiler

end
