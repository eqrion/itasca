import Itasca.Wasm2.Simd.Visitor
import Itasca.Wasm2.Bulk.Visitor
import Itasca.Visitor.Refinement
import Itasca.Visitor.StepRefinement

/-!
# Exact visitor refinement for Wasm 2.0 dispatch

Exact visitor replacement for the extracted `code.step_bulk`, `code.step_extended`,
`code.step_simd` and `code.step_wasm2`. Unlike accepting transfer in `Wasm2/Visitor/Transfer`,
these statements preserve callback rejection, exact immediate values and both final states.
-/

open Aeneas Aeneas.Std

namespace Itasca

open VisitorTrace Wasm2

/-- All bulk callback identities and immediate arguments refine exactly, even
when the reader or callback rejects the instruction. -/
theorem code.step_bulk.refines {V W : Type}
    (visitor : code.OpVisitor V) (replacement : code.OpVisitor W)
    (related : V → W → Prop) (hrefines : Refines visitor replacement related)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (opcode : U32)
    (v : V) (w : W) (hrelated : related v w)
    (res : core.result.Result Unit error.OpError) (final : code.OpIterState) (v' : V)
    (h : code.step_bulk visitor st data env opcode v = .ok (res, final, v')) :
    ∃ w', code.step_bulk replacement st data env opcode w =
      .ok (res, final, w') ∧ related v' w' := by
  rw [code.step_bulk.eq_runs] at h ⊢
  unfold bulkStep at h ⊢
  split at h
  case h_1 =>
    exact CoreVisitor.run.refines _ visitor replacement related hrefines
      (fun s a => .op s (.memory_init a)) v w hrelated res final v' h
  case h_2 =>
    exact CoreVisitor.run.refines _ visitor replacement related hrefines
      (fun s a => .op s (.data_drop a)) v w hrelated res final v' h
  case h_3 =>
    exact CoreVisitor.run.refines _ visitor replacement related hrefines
      (fun s _ => .op s .memory_copy) v w hrelated res final v' h
  case h_4 =>
    exact CoreVisitor.run.refines _ visitor replacement related hrefines
      (fun s _ => .op s .memory_fill) v w hrelated res final v' h
  case h_5 =>
    exact CoreVisitor.run.refines _ visitor replacement related hrefines
      (fun s (a : U32 × U32) => .op s (.table_init a.1 a.2)) v w hrelated res final v' h
  case h_6 =>
    exact CoreVisitor.run.refines _ visitor replacement related hrefines
      (fun s (a : U32 × types.ValueType) => .op s (.elem_drop a.1)) v w hrelated res final v' h
  case h_7 =>
    exact CoreVisitor.run.refines _ visitor replacement related hrefines
      (fun s (a : U32 × U32) => .op s (.table_copy a.1 a.2)) v w hrelated res final v' h
  case h_8 =>
    exact CoreVisitor.run.refines _ visitor replacement related hrefines
      (fun s a => .op s (.table_grow a)) v w hrelated res final v' h
  case h_9 =>
    exact CoreVisitor.run.refines _ visitor replacement related hrefines
      (fun s a => .op s (.table_size a)) v w hrelated res final v' h
  case h_10 =>
    exact CoreVisitor.run.refines _ visitor replacement related hrefines
      (fun s a => .op s (.table_fill a)) v w hrelated res final v' h
  case h_11 =>
    simp only [Result.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨w, rfl, hrelated⟩

end Itasca

namespace Itasca

open VisitorTrace Wasm2

/-- Exact replacement for sign-extension, saturating conversion and Wasm 1.0 scalar
callbacks, preserving errors and the full post-operator state. -/
theorem code.step_extended.refines {V W : Type}
    (visitor : code.OpVisitor V) (replacement : code.OpVisitor W)
    (related : V → W → Prop) (hrefines : Refines visitor replacement related)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (opcode : U8)
    (v : V) (w : W) (hrelated : related v w)
    (res : core.result.Result Unit error.OpError) (final : code.OpIterState) (v' : V)
    (h : code.step_extended visitor st data env ctx opcode v = .ok (res, final, v')) :
    ∃ w', code.step_extended replacement st data env ctx opcode w =
      .ok (res, final, w') ∧ related v' w' := by
  cases hm : NumericExtensions.signMeaning opcode with
  | some op =>
    rw [code.step_extended.sign visitor st data env ctx opcode op v hm] at h
    rw [code.step_extended.sign replacement st data env ctx opcode op w hm]
    have bounds := (NumericExtensions.sign_properties hm).2.2
    rcases opcode with ⟨⟨n, hn⟩⟩
    change 192 ≤ n ∧ n ≤ 196 at bounds
    obtain ⟨lower, upper⟩ := bounds
    interval_cases n
    all_goals first
      | exact CoreVisitor.run.refines _ visitor replacement related hrefines
          (fun s _ => .op s (.extendedNumeric .i32_extend8_s)) v w hrelated res final v' h
      | exact CoreVisitor.run.refines _ visitor replacement related hrefines
          (fun s _ => .op s (.extendedNumeric .i32_extend16_s)) v w hrelated res final v' h
      | exact CoreVisitor.run.refines _ visitor replacement related hrefines
          (fun s _ => .op s (.extendedNumeric .i64_extend8_s)) v w hrelated res final v' h
      | exact CoreVisitor.run.refines _ visitor replacement related hrefines
          (fun s _ => .op s (.extendedNumeric .i64_extend16_s)) v w hrelated res final v' h
      | exact CoreVisitor.run.refines _ visitor replacement related hrefines
          (fun s _ => .op s (.extendedNumeric .i64_extend32_s)) v w hrelated res final v' h
  | none =>
    by_cases hp : opcode = code.OP_MISC_PREFIX
    · have he : opcode = 0xFC#u8 := by simpa [global_simps] using hp
      rw [he] at h ⊢
      rw [code.step_extended.prefixed] at h ⊢
      obtain ⟨r, hr⟩ := reader.read_u32_leb.total data st.pos
      simp only [prefixedStep, hr, bind_ok] at h ⊢
      cases r with
      | Err e =>
        simp only [Result.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨w, rfl, hrelated⟩
      | Ok pair =>
        obtain ⟨subopcode, next⟩ := pair
        cases hs : NumericExtensions.saturatingMeaning subopcode with
        | none =>
          simp only [hs, Result.ok.injEq, Prod.mk.injEq] at h ⊢
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact ⟨w, ⟨rfl, rfl, rfl⟩, hrelated⟩
        | some op =>
          simp only [hs] at h ⊢
          have hbound : subopcode.val < 8 := by
            unfold NumericExtensions.saturatingMeaning at hs
            split at hs <;> simp_all
          rcases subopcode with ⟨⟨n, hn⟩⟩
          change n < 8 at hbound
          interval_cases n
          all_goals first
            | exact CoreVisitor.run.refines _ visitor replacement related hrefines
                (fun s _ => .op s (.extendedNumeric .i32_trunc_sat_f32_s)) v w hrelated res final v' h
            | exact CoreVisitor.run.refines _ visitor replacement related hrefines
                (fun s _ => .op s (.extendedNumeric .i32_trunc_sat_f32_u)) v w hrelated res final v' h
            | exact CoreVisitor.run.refines _ visitor replacement related hrefines
                (fun s _ => .op s (.extendedNumeric .i32_trunc_sat_f64_s)) v w hrelated res final v' h
            | exact CoreVisitor.run.refines _ visitor replacement related hrefines
                (fun s _ => .op s (.extendedNumeric .i32_trunc_sat_f64_u)) v w hrelated res final v' h
            | exact CoreVisitor.run.refines _ visitor replacement related hrefines
                (fun s _ => .op s (.extendedNumeric .i64_trunc_sat_f32_s)) v w hrelated res final v' h
            | exact CoreVisitor.run.refines _ visitor replacement related hrefines
                (fun s _ => .op s (.extendedNumeric .i64_trunc_sat_f32_u)) v w hrelated res final v' h
            | exact CoreVisitor.run.refines _ visitor replacement related hrefines
                (fun s _ => .op s (.extendedNumeric .i64_trunc_sat_f64_s)) v w hrelated res final v' h
            | exact CoreVisitor.run.refines _ visitor replacement related hrefines
                (fun s _ => .op s (.extendedNumeric .i64_trunc_sat_f64_u)) v w hrelated res final v' h
    · rw [code.step_extended.base visitor st data env ctx opcode v hm hp] at h
      rw [code.step_extended.base replacement st data env ctx opcode w hm hp]
      exact code.step.refines visitor replacement related hrefines
        st data env ctx opcode v w hrelated res final v' h

end Itasca

namespace Itasca.Wasm2.Simd

open VisitorTrace

/-- Exact refinement covers all SIMD classes and preserves the raw constants, shuffle
words, memory arguments and lane indices delivered to callbacks. -/
theorem subStep.refines {V W : Type}
    (visitor : code.OpVisitor V) (replacement : code.OpVisitor W)
    (related : V → W → Prop) (hrefines : Refines visitor replacement related)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (opcode : U32)
    (v : V) (w : W) (hrelated : related v w)
    (res : core.result.Result Unit error.OpError) (final : code.OpIterState) (v' : V)
    (h : subStep visitor st data env opcode v = .ok (res, final, v')) :
    ∃ w', subStep replacement st data env opcode w =
      .ok (res, final, w') ∧ related v' w' := by
  unfold subStep at h ⊢
  rw [pure_table] at h ⊢
  cases hm : pureMeaning opcode.val with
  | some op =>
    simp only [hm, Option.map_some, bind_ok] at h ⊢
    exact CoreVisitor.run.refines _ visitor replacement related hrefines
      (fun s _ => .op s (.simd opcode)) v w hrelated res final v' h
  | none =>
    simp only [hm, Option.map_none, bind_ok] at h ⊢
    rw [lane_table] at h ⊢
    cases hl : laneMeaning opcode.val with
    | some lane =>
      simp only [hl, Option.map_some, bind_ok] at h ⊢
      rcases he : lane.runtime with ⟨ty, count, replace⟩
      simp only [he] at h ⊢
      exact CoreVisitor.run.refines _ visitor replacement related hrefines
        (fun s a => .op s (.simd_lane opcode a)) v w hrelated res final v' h
    | none =>
      simp only [hl, Option.map_none, bind_ok] at h ⊢
      rw [memory_table] at h ⊢
      cases hm : memoryMeaning opcode.val with
      | some mem =>
        simp only [hm, Option.map_some, bind_ok] at h ⊢
        rcases he : mem.runtime with ⟨align, store, count⟩
        simp only [he] at h ⊢
        split at h
        · rename_i hc
          simp only [hc, if_true]
          exact CoreVisitor.run.refines _ visitor replacement related hrefines
            (fun s (a : code.MemArg × U8) => .op s (.simd_memory_lane opcode a.1 a.2)) v w hrelated res final v' h
        · rename_i hc
          simp only [hc]
          cases store <;> simp only [Bool.false_eq_true, if_true, if_false] at h ⊢
          all_goals
            exact CoreVisitor.run.refines _ visitor replacement related hrefines
              (fun s a => .op s (.simd_memory opcode a)) v w hrelated res final v' h
      | none =>
        simp only [hm, Option.map_none, bind_ok] at h ⊢
        split at h
        · exact CoreVisitor.run.refines _ visitor replacement related hrefines
            (fun s (a : U64 × U64) => .op s (.simd_const a.1 a.2)) v w hrelated res final v' h
        · exact CoreVisitor.run.refines _ visitor replacement related hrefines
            (fun s (a : U64 × U64) => .op s (.simd_shuffle a.1 a.2)) v w hrelated res final v' h
        · simp only [Result.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact ⟨w, rfl, hrelated⟩

end Itasca.Wasm2.Simd

namespace Itasca

open VisitorTrace Wasm2.Simd

/-- SIMD prefix decoding and exact callback refinement preserve every ordinary
return, including malformed prefix bytes and observed rejection. -/
theorem code.step_simd.refines {V W : Type}
    (visitor : code.OpVisitor V) (replacement : code.OpVisitor W)
    (related : V → W → Prop) (hrefines : Refines visitor replacement related)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env)
    (v : V) (w : W) (hrelated : related v w)
    (res : core.result.Result Unit error.OpError) (final : code.OpIterState) (v' : V)
    (h : code.step_simd visitor st data env v = .ok (res, final, v')) :
    ∃ w', code.step_simd replacement st data env w =
      .ok (res, final, w') ∧ related v' w' := by
  rw [code.step_simd.eq_runs] at h ⊢
  unfold prefixStep at h ⊢
  obtain ⟨r, hr⟩ := reader.read_u32_leb.total data st.pos
  simp only [hr, bind_ok] at h ⊢
  cases r with
  | Err e =>
    simp only [Result.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨w, rfl, hrelated⟩
  | Ok pair =>
    obtain ⟨opcode, next⟩ := pair
    exact subStep.refines visitor replacement related hrefines
      _ data env opcode v w hrelated res final v' h

end Itasca

namespace Itasca

open VisitorTrace Wasm2

/-- Exact callback refinement for the complete `code.step_wasm2` dispatcher (scalar, reference,
bulk and SIMD), preserving reader failure, callback rejection and both states. -/
theorem code.step_wasm2.refines {V W : Type}
    (visitor : code.OpVisitor V) (replacement : code.OpVisitor W)
    (related : V → W → Prop) (hrefines : Refines visitor replacement related)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (opcode : U8)
    (v : V) (w : W) (hrelated : related v w)
    (res : core.result.Result Unit error.OpError) (final : code.OpIterState) (v' : V)
    (h : code.step_wasm2 visitor st data env ctx opcode v = .ok (res, final, v')) :
    ∃ w', code.step_wasm2 replacement st data env ctx opcode w =
      .ok (res, final, w') ∧ related v' w' := by
  by_cases h253 : opcode = 253#u8
  · subst opcode
    exact code.step_simd.refines visitor replacement related hrefines st data env
      v w hrelated res final v' h
  by_cases h28 : opcode = 28#u8
  · rw [h28, code.step_wasm2.typed_select] at h ⊢
    exact CoreVisitor.run.refines _ visitor replacement related hrefines
      (fun s a => .op s (.select_typed a)) v w hrelated res final v' h
  by_cases h37 : opcode = 37#u8
  · rw [h37, code.step_wasm2.table_get] at h ⊢
    exact CoreVisitor.run.refines _ visitor replacement related hrefines
      (fun s a => .op s (.table_get a)) v w hrelated res final v' h
  by_cases h38 : opcode = 38#u8
  · rw [h38, code.step_wasm2.table_set] at h ⊢
    exact CoreVisitor.run.refines _ visitor replacement related hrefines
      (fun s a => .op s (.table_set a)) v w hrelated res final v' h
  by_cases h208 : opcode = 208#u8
  · rw [h208, code.step_wasm2.ref_null] at h ⊢
    exact CoreVisitor.run.refines _ visitor replacement related hrefines
      (fun s a => .op s (.ref_null a)) v w hrelated res final v' h
  by_cases h209 : opcode = 209#u8
  · rw [h209, code.step_wasm2.ref_is_null] at h ⊢
    exact CoreVisitor.run.refines _ visitor replacement related hrefines
      (fun s _ => .op s .ref_is_null) v w hrelated res final v' h
  by_cases h210 : opcode = 210#u8
  · rw [h210, code.step_wasm2.ref_func] at h ⊢
    exact CoreVisitor.run.refines _ visitor replacement related hrefines
      (fun s a => .op s (.ref_func a)) v w hrelated res final v' h
  by_cases h252 : opcode = 252#u8
  · rw [h252, code.step_wasm2.prefixed] at h ⊢
    obtain ⟨r, hr⟩ := reader.read_u32_leb.total data st.pos
    simp only [wasm2PrefixedStep, hr, bind_ok] at h ⊢
    cases r with
    | Err e =>
      simp only [Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨w, rfl, hrelated⟩
    | Ok pair =>
      obtain ⟨subopcode, next⟩ := pair
      dsimp only at *
      split at h
      · rename_i hs
        simp only [if_pos hs]
        exact code.step_extended.refines visitor replacement related hrefines
          st data env ctx 0xfc#u8 v w hrelated res final v' h
      · rename_i hs
        simp only [if_neg hs]
        exact code.step_bulk.refines visitor replacement related hrefines
          {st with pos := next} data env subopcode v w hrelated res final v' h
  have hbase : opcode.val ∉ [28, 37, 38, 208, 209, 210, 252, 253] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    have neq {a b : U8} (h : a ≠ b) : a.val ≠ b.val :=
      fun he => h (UScalar.eq_of_val_eq he)
    exact ⟨neq h28, neq h37, neq h38, neq h208, neq h209, neq h210, neq h252, neq h253⟩
  rw [code.step_wasm2.base visitor st data env ctx opcode v hbase] at h
  rw [code.step_wasm2.base replacement st data env ctx opcode w hbase]
  exact code.step_extended.refines visitor replacement related hrefines
    st data env ctx opcode v w hrelated res final v' h

end Itasca
