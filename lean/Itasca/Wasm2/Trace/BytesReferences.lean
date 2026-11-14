import Itasca.Wasm2.Simd.Visitor
import Itasca.Wasm2.Bulk.Visitor
import Itasca.Visitor.EventTables
import Itasca.Visitor.BodyReplay
import Itasca.Wasm2.Visitor.Step
import Itasca.Binary.Wasm2.EncodingUnique
import Itasca.Visitor.RunTrace
import Itasca.Wasm2.References.Step
import Itasca.Wasm2.Bulk.Step

/-!
Sections, each formerly its own module: Refinement, ControlRefinement, Basic, Bytes, BytesReferences.
-/

/-! ## Refinement -/

section

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
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (opcode : U32)
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
      (fun s (a : U32 × wasm_types.ValueType) => .op s (.elem_drop a.1)) v w hrelated res final v' h
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
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env)
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
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (opcode : U32)
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
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env)
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
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env)
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

end

/-! ## ControlRefinement -/

section

/-!
# Exact refinement of control dispatch

Exact visitor refinement for the `br_table` loop (`tableRest.refines`, `tableBody.refines`,
`code.branch_table_with_loop.refines`, `code.branch_table_with.refines`) and for the whole
`code.step_profile` (`code.step_profile.refines`), preserving computed signatures, partial tables
and callback rejection.
-/

open Aeneas Aeneas.Std Result ControlFlow

namespace Itasca.Wasm2.Visitor

open VisitorTrace

/-- The visitor state of one `br_table` iteration result. -/
def tableVisitor {V : Type} :
    ControlFlow (code.OpIterState × V × Option Usize × U32)
      (core.result.Result Unit error.OpError × code.BodyState × V) → V
  | .cont (_, v, _, _) => v
  | .done (_, _, v) => v

/-- Exact visitor-state refinement through the suffix check and final table hook. -/
theorem tableRest.refines {V W : Type} (visitor : code.OpVisitor V)
    (replacement : code.OpVisitor W) (related : V → W → Prop)
    (hrefines : Refines visitor replacement related)
    (st : code.BodyState) (env : metadata.Env) (count i depth : U32)
    (ts : signature.ResultType) (arity : Option Usize) (v : V) (w : W) (hrelated : related v w) (cf)
    (h : tableRest visitor st env count i depth ts arity v = .ok cf) :
    ∃ cf', tableRest replacement st env count i depth ts arity w = .ok cf' ∧
      tableObserve cf' = tableObserve cf ∧ related (tableVisitor cf) (tableVisitor cf') := by
  unfold tableRest at h ⊢
  obtain ⟨r, hr, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
  rw [hr]
  cases r with
  | Err e =>
    simp only [ok.injEq] at h
    subst cf
    exact ⟨.done (.Err e, st, w), by simp, rfl, hrelated⟩
  | Ok nextArity =>
    simp only [bind_ok] at h ⊢
    by_cases he : i = count
    · simp only [he, if_true] at h ⊢
      obtain ⟨ois, ho, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
      rw [ho]
      simp only [bind_ok]
      obtain ⟨⟨reply, v'⟩, hv, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
      obtain ⟨w', hw, hr'⟩ := hrefines v w (.op ois (.br_table depth ts)) reply v' hrelated hv
      change replacement.on_br_table w ois depth ts = .ok (reply, w') at hw
      rw [hw]
      cases reply <;> simp [code.visit] at h ⊢
      all_goals subst cf; exact ⟨rfl, hr'⟩
    · simp only [he, if_false] at h ⊢
      obtain ⟨j, hj, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
      simp only [ok.injEq] at h
      subst cf
      exact ⟨.cont (st.core, w, nextArity, j), by simp [hj], rfl, hrelated⟩

/-- A table iteration includes every label callback, even the label whose later
type compatibility check fails. A rejecting callback remains last. -/
theorem tableBody.refines {V W : Type} (visitor : code.OpVisitor V)
    (replacement : code.OpVisitor W) (related : V → W → Prop)
    (hrefines : Refines visitor replacement related)
    (data : Slice U8) (env : metadata.Env) (count : U32)
    (st : code.BodyState) (v : V) (w : W) (hrelated : related v w) (arity : Option Usize)
    (i : U32) (cf)
    (h : tableBody visitor data env count st v arity i = .ok cf) :
    ∃ cf', tableBody replacement data env count st w arity i = .ok cf' ∧
      tableObserve cf' = tableObserve cf ∧ related (tableVisitor cf) (tableVisitor cf') := by
  unfold tableBody at h ⊢
  obtain ⟨⟨r, s⟩, hr, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
  rw [hr]
  cases r with
  | Err e =>
    simp at h
    subst cf
    exact ⟨.done (.Err e, s, w), by simp, rfl, hrelated⟩
  | Ok pair =>
    obtain ⟨depth, ts⟩ := pair
    simp only [bind_ok, Std.uncurry] at h ⊢
    by_cases he : i = count
    · simp only [he, bne_self_eq_false, Bool.false_eq_true, if_false] at h ⊢
      exact tableRest.refines visitor replacement related hrefines s env count count depth ts arity
        v w hrelated cf h
    · simp only [bne_iff_ne, if_pos he] at h ⊢
      obtain ⟨⟨reply, v'⟩, hv, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
      obtain ⟨w', hw, hr'⟩ := hrefines v w (.op s.core (.br_table_label depth)) reply v' hrelated hv
      change replacement.on_br_table_label w s.core depth = .ok (reply, w') at hw
      rw [hw]
      cases reply with
      | Err e =>
        simp [code.visit] at h ⊢
        subst cf
        exact ⟨rfl, hr'⟩
      | Ok u =>
        simp [code.visit] at h ⊢
        exact tableRest.refines visitor replacement related hrefines s env count i depth ts arity
          v' w' hr' cf h

end Itasca.Wasm2.Visitor

namespace Itasca

open VisitorTrace Wasm2.Visitor

/-- Exact refinement of every table-loop outcome, including a partial vector
ending at a rejected label or failed target check. -/
theorem code.branch_table_with_loop.refines {V W : Type}
    (visitor : code.OpVisitor V) (replacement : code.OpVisitor W)
    (related : V → W → Prop) (hrefines : Refines visitor replacement related)
    (st : code.BodyState) (data : Slice U8) (env : metadata.Env)
    (v : V) (w : W) (hrelated : related v w)
    (count : U32) (arity : Option Usize) (i : U32)
    (hi : i.val ≤ count.val)
    (res : core.result.Result Unit error.OpError) (final : code.BodyState) (v' : V)
    (h : code.branch_table_with_loop visitor st.core data env v count arity i =
      .ok (res, final, v')) :
    ∃ w', code.branch_table_with_loop replacement st.core data env w count arity i =
      .ok (res, final, w') ∧ related v' w' := by
  generalize hn : count.val - i.val = n
  induction n using Nat.strong_induction_on generalizing st v w arity i with
  | h n ih =>
    unfold code.branch_table_with_loop at h ⊢
    rw [loop] at h ⊢
    simp only [tableBody_eq visitor data env count st v arity i] at h
    simp only [tableBody_eq replacement data env count st w arity i]
    obtain ⟨cf, hs, ht⟩ := ResultFacts.bind_ok_inv _ _ _ h
    obtain ⟨cf', hw, ho, hr⟩ := tableBody.refines visitor replacement related hrefines
      data env count st v w hrelated arity i cf hs
    rw [hw]
    cases cf with
    | done result =>
      obtain ⟨r, s, v1⟩ := result
      simp only [ok.injEq, Prod.mk.injEq] at ht
      obtain ⟨rfl, rfl, rfl⟩ := ht
      cases cf' with
      | cont p => simp [tableObserve] at ho
      | done p =>
        obtain ⟨r, s, w'⟩ := p
        simp only [tableObserve, ControlFlow.done.injEq, Prod.mk.injEq] at ho
        obtain ⟨rfl, rfl⟩ := ho
        exact ⟨w', by simp, hr⟩
    | cont next =>
      obtain ⟨ois, v1, arity1, j⟩ := next
      have hp := tableBody.cont_progress visitor data env count st v arity i
        ois v1 arity1 j hi hs
      cases cf' with
      | done p => simp [tableObserve] at ho
      | cont p =>
        obtain ⟨ois', w1, arity1', j'⟩ := p
        simp only [tableObserve, ControlFlow.cont.injEq, Prod.mk.injEq] at ho
        obtain ⟨rfl, rfl, rfl⟩ := ho
        have hrec : code.branch_table_with_loop visitor ois' data env v1 count arity1'
            j' = .ok (res, final, v') := ht
        obtain ⟨w', hw', hr'⟩ := ih (count.val - j'.val) (by omega)
          ⟨ois'⟩ v1 w1 hr arity1' j' hp.2 hrec rfl
        exact ⟨w', by simpa only [bind_ok, code.branch_table_with_loop] using hw', hr'⟩

theorem code.branch_table_with.refines {V W : Type}
    (visitor : code.OpVisitor V) (replacement : code.OpVisitor W)
    (related : V → W → Prop) (hrefines : Refines visitor replacement related)
    (st : code.BodyState) (data : Slice U8) (env : metadata.Env)
    (v : V) (w : W) (hrelated : related v w)
    (res : core.result.Result Unit error.OpError) (final : code.BodyState) (v' : V)
    (h : code.branch_table_with visitor st data env v = .ok (res, final, v')) :
    ∃ w', code.branch_table_with replacement st data env w =
      .ok (res, final, w') ∧ related v' w' := by
  unfold code.branch_table_with at h ⊢
  obtain ⟨r, hr, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
  rw [hr]
  cases r with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h ⊢
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, rfl, hrelated⟩
  | Ok pair =>
    obtain ⟨count, next⟩ := pair
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Std.uncurry] at h ⊢
    obtain ⟨⟨r, ois⟩, hr, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
    rw [hr]
    cases r with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h ⊢
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨rfl, rfl, hrelated⟩
    | Ok u =>
      simp only [bind_ok, Std.uncurry] at h ⊢
      exact code.branch_table_with_loop.refines visitor replacement related hrefines
        ⟨ois⟩ data env v w hrelated count none 0#u32 (by simp) res final v' h

end Itasca

namespace Itasca

open VisitorTrace Wasm2.Visitor

set_option maxHeartbeats 2000000 in
/-- Instruction dispatch, including control instructions, preserves every ordinary result under exact
callback refinement, including computed signatures and partial tables. -/
theorem code.step_profile.refines {V W : Type}
    (visitor : code.OpVisitor V) (replacement : code.OpVisitor W)
    (related : V → W → Prop) (hrefines : Refines visitor replacement related)
    (st : code.BodyState) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) (opcode : U8)
    (v : V) (w : W) (hrelated : related v w)
    (res : core.result.Result Unit error.OpError) (final : code.BodyState) (v' : V)
    (h : code.step_profile visitor st data env ctx index opcode v =
      .ok (res, final, v')) :
    ∃ w', code.step_profile replacement st data env ctx index opcode w =
      .ok (res, final, w') ∧ related v' w' := by
  unfold code.step_profile at h ⊢
  split at h
  case h_1 | h_2 | h_3 | h_4 | h_5 | h_6 | h_7 | h_10 | h_11 =>
    try simp_all only [↓reduceIte]
    obtain ⟨⟨r, s⟩, hr, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
    rw [hr]
    cases r with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h ⊢
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨rfl, rfl, hrelated⟩
    | Ok a =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Std.uncurry] at h ⊢
      obtain ⟨⟨reply, v1⟩, hv, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
      first
      | (change invoke visitor v (.op s.core (.block a)) = .ok (reply, v1) at hv
         obtain ⟨w1, hw, hr1⟩ := hrefines v w (.op s.core (.block a)) reply v1 hrelated hv)
      | (change invoke visitor v (.op s.core (.loop a)) = .ok (reply, v1) at hv
         obtain ⟨w1, hw, hr1⟩ := hrefines v w (.op s.core (.loop a)) reply v1 hrelated hv)
      | (change invoke visitor v (.op s.core (.if_ a)) = .ok (reply, v1) at hv
         obtain ⟨w1, hw, hr1⟩ := hrefines v w (.op s.core (.if_ a)) reply v1 hrelated hv)
      | (change invoke visitor v (.op s.core (.else_ a.2)) = .ok (reply, v1) at hv
         obtain ⟨w1, hw, hr1⟩ := hrefines v w (.op s.core (.else_ a.2)) reply v1 hrelated hv)
      | (change invoke visitor v (.op s.core (.end_ a.1 a.2)) = .ok (reply, v1) at hv
         obtain ⟨w1, hw, hr1⟩ := hrefines v w (.op s.core (.end_ a.1 a.2)) reply v1 hrelated hv)
      | (change invoke visitor v (.op s.core (.br a.1 a.2)) = .ok (reply, v1) at hv
         obtain ⟨w1, hw, hr1⟩ := hrefines v w (.op s.core (.br a.1 a.2)) reply v1 hrelated hv)
      | (change invoke visitor v (.op s.core (.br_if a.1 a.2)) = .ok (reply, v1) at hv
         obtain ⟨w1, hw, hr1⟩ := hrefines v w (.op s.core (.br_if a.1 a.2)) reply v1 hrelated hv)
      | (change invoke visitor v (.op s.core (.call a)) = .ok (reply, v1) at hv
         obtain ⟨w1, hw, hr1⟩ := hrefines v w (.op s.core (.call a)) reply v1 hrelated hv)
      | (change invoke visitor v (.op s.core (.call_indirect a.1 a.2)) = .ok (reply, v1) at hv
         obtain ⟨w1, hw, hr1⟩ := hrefines v w (.op s.core (.call_indirect a.1 a.2)) reply v1 hrelated hv)
      all_goals
        simp only [invoke] at hw
        rw [hw]
        cases reply <;> simp [code.visit,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h ⊢
        all_goals obtain ⟨rfl, rfl, rfl⟩ := h; exact ⟨rfl, rfl, hr1⟩
  case h_8 =>
    try simp_all only [↓reduceIte]
    obtain ⟨⟨r, s, v1⟩, hs, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
    obtain ⟨w1, hw, hr1⟩ := code.branch_table_with.refines visitor replacement related hrefines
      st data env v w hrelated r s v1 hs
    rw [hw]
    cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h ⊢
    all_goals obtain ⟨rfl, rfl, rfl⟩ := h; exact ⟨rfl, rfl, hr1⟩
  case h_9 =>
    try simp_all only [↓reduceIte]
    obtain ⟨⟨r, ois⟩, hr, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
    rw [hr]
    cases r with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h ⊢
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨rfl, rfl, hrelated⟩
    | Ok u =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Std.uncurry] at h ⊢
      obtain ⟨ois', ho, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
      rw [ho]
      simp only [bind_ok]
      obtain ⟨⟨reply, v1⟩, hv, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
      obtain ⟨w1, hw, hr1⟩ := hrefines v w (.op ois' .return_) reply v1 hrelated hv
      change replacement.on_return w ois' = .ok (reply, w1) at hw
      rw [hw]
      cases reply <;> simp [code.visit,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h ⊢
      all_goals obtain ⟨rfl, rfl, rfl⟩ := h; exact ⟨rfl, rfl, hr1⟩
  case h_12 =>
    try simp_all only
    split at h
    · rename_i hcap
      simp only [hcap, if_true]
      simp only [ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨w, rfl, hrelated⟩
    · rename_i hcap
      simp only [hcap, if_false]
      obtain ⟨⟨r, ois, v1⟩, hs, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
      obtain ⟨w1, hw, hr1⟩ := code.step_wasm2.refines visitor replacement related hrefines
        st.core data env ctx opcode v w hrelated r ois v1 hs
      rw [hw]
      cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h ⊢
      all_goals obtain ⟨rfl, rfl, rfl⟩ := h; exact ⟨rfl, rfl, hr1⟩

end Itasca

end

/-! ## Basic -/

section

/-!
# Callback byte provenance for Wasm 2.0

Defines the relations that tie a visitor's callback observations to the independent encoding of a
body: `Chunk` (the callbacks of one decoded instruction), `StepTrace` (one step, including failure),
`Completed` (a sequence of chunks) and `BodyTrace` (a whole run). Block tokens keep their indexed
signatures. This file gives the relations and their composition laws; `Wasm2/Trace/Correspondence`
shows that the extracted validator satisfies them.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2.CallbackTrace

open VisitorTrace

/-- The Wasm 2.0 token of an operator callback. Block, loop and if tokens keep their indexed
parameter and result signatures. -/
def actionToken (action : Action) (pending : List U32) : Option Token :=
  match action with
  | .block bt => some (.block bt)
  | .loop bt => some (.loop bt)
  | .if_ bt => some (.if_ bt)
  | _ => action.token pending

/-- Exactly the callbacks for one fully decoded instruction. The table case
separates vector entries from its default target, which has no label callback.
Computed metadata and state snapshots remain in the observations. -/
inductive Chunk (data : Slice U8) (start : Usize) :
    List Observation → Token → Usize → Prop where
  | single (st : code.OpIterState) (action : Action) (reply : VisitResult) (token : Token) :
      actionToken action [] = some token → action.opcode ≠ some 0x0E#u8 →
      At data start token st.pos →
      Chunk data start [⟨.op st action, reply⟩] token st.pos
  | table {pos count first labels depths last fallback st bt reply} :
      Wasm1.BytesAt data start [0x0E#u8] pos →
      Leb128.Decoded data pos count first →
      LabelsAt data first labels depths last → depths.length = count.val →
      Leb128.Decoded data last fallback st.pos →
      At data start
        (.plain (.BR_TABLE (depths.map (fun i => .mk_uN i.val)) (.mk_uN fallback.val))) st.pos →
      Chunk data start (labels ++ [⟨.op st (.br_table fallback bt), reply⟩])
        (.plain (.BR_TABLE (depths.map (fun i => .mk_uN i.val)) (.mk_uN fallback.val))) st.pos

theorem Chunk.encoded {data start observations token next}
    (h : Chunk data start observations token next) : At data start token next := by
  cases h <;> assumption

/-- One actual step's callback trace, including ordinary failure. -/
inductive StepTrace (data : Slice U8) (start : Usize) :
    List Observation → BodyResult → code.OpIterState → Prop where
  | silent (e : error.OpError) (st : code.OpIterState) : Outcomes [] (.Err e) →
      StepTrace data start [] (.Err e) st
  | complete {observations token st result} : Chunk data start observations token st.pos →
      Outcomes observations result → StepTrace data start observations result st
  | unfinished {observations st} (e : error.OpError) : PartialTable data start observations →
      Outcomes observations (.Err e) → StepTrace data start observations (.Err e) st

theorem StepTrace.outcomes {data start observations result st}
    (h : StepTrace data start observations result st) : Outcomes observations result := by
  cases h <;> assumption

theorem StepTrace.accepted {data start observations st}
    (h : StepTrace data start observations (.Ok ()) st) :
    ∃ token, Chunk data start observations token st.pos := by
  cases h with
  | complete hc _ => exact ⟨_, hc⟩

/-- Concatenation of complete instruction chunks, independently of execution. -/
inductive Completed (data : Slice U8) :
    Usize → List Observation → List Token → Usize → Prop where
  | nil (pos : Usize) (bound : pos.val ≤ data.length) : Completed data pos [] [] pos
  | cons {start first token middle rest tokens next} :
      Chunk data start first token middle → Completed data middle rest tokens next →
      Completed data start (first ++ rest) (token :: tokens) next

theorem Completed.encoded {data start observations tokens next}
    (h : Completed data start observations tokens next) : Consumed data start tokens next := by
  induction h with
  | nil pos hb => exact .nil pos hb
  | cons hc _ ih =>
      simpa using (Consumed.snoc (.nil _ (by have := hc.encoded.span; omega)) hc.encoded).append ih

/-- Whole-run byte provenance. Only the final rejected table can be partial. -/
def BodyTrace (data : Slice U8) (start : Usize) (observations : List Observation)
    (result : BodyResult) : Prop :=
  Outcomes observations result ∧ ∃ complete tokens cursor tail,
    observations = complete ++ tail ∧ Completed data start complete tokens cursor ∧
    (tail = [] ∨ PartialTable data cursor tail) ∧
    (result = .Ok () → tail = [] ∧ cursor.val = data.length)

theorem BodyTrace.accepted {data start observations}
    (h : BodyTrace data start observations (.Ok ())) :
    AllAccepted observations ∧ ∃ tokens cursor,
      Completed data start observations tokens cursor ∧ cursor.val = data.length := by
  obtain ⟨ho, complete, tokens, cursor, tail, heq, hc, _, hend⟩ := h
  obtain ⟨rfl, hp⟩ := hend rfl
  simp only [List.append_nil] at heq
  exact ⟨ho, tokens, cursor, heq ▸ hc, hp⟩


/-- Lifts independent success-byte provenance through a single recorded callback.
Failure before the callback is silent; the callback's own rejection is recorded. -/
theorem run_step_trace {A V : Type} (data : Slice U8) (start : Usize)
    (read : Result (core.result.Result A error.OpError × code.OpIterState))
    (visitor : code.OpVisitor V) (observe : V → List Observation)
    (hrecords : Records visitor observe) (action : A → Action)
    (hbytes : ∀ s a, read = .ok (.Ok a, s) → ∃ token,
      actionToken (action a) [] = some token ∧ (action a).opcode ≠ some 0x0E#u8 ∧
      At data start token s.pos)
    (v : V) (result : BodyResult) (final : code.OpIterState) (v' : V)
    (h : CoreVisitor.run read (fun v s a => invoke visitor v (.op s (action a))) v =
      .ok (result, final, v')) :
    ∃ observations, observe v' = observe v ++ observations ∧
      StepTrace data start observations result final := by
  rcases CoreVisitor.run.recorded read visitor observe hrecords (fun s a => .op s (action a))
      v result final v' h with ⟨err, _, rfl, hlog⟩ | ⟨a, reply, hr, rfl, hlog⟩
  · exact ⟨[], by simpa using hlog, .silent err final (Outcomes.empty _)⟩
  · obtain ⟨token, ht, hn, hb⟩ := hbytes final a hr
    refine ⟨[⟨.op final (action a), reply⟩], hlog,
      .complete (.single final (action a) reply token ht hn hb) ?_⟩
    exact Outcomes.single (.op final (action a)) reply


end Itasca.Wasm2.CallbackTrace

end

/-! ## Bytes -/

section

/-!
# Byte provenance for Wasm 2.0 leaf callbacks

Defines `StepRecords` and `ReadBytes`, the contracts for the callback trace of one
`code.step_wasm2` leaf, and proves the shared lemmas `metadata_post`, `metadata_bytes` and
`metadata_bytes_at` for readers that decode metadata and then apply a fixed operand effect. Reader
failures are silent, successful reads record the decoded arguments even when the callback rejects,
and no accepting-visitor premise is used.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2.CallbackBytes

open VisitorTrace CallbackTrace

/-- The callback trace of one `code.step_wasm2` leaf is a `StepTrace` under the independent
pending-byte cursor. -/
def StepRecords {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (ctx : code.Context) (opcode : U8) : Prop :=
  ∀ v result final v', code.step_wasm2 visitor st.core data env ctx opcode v =
      .ok (result, final, v') →
    ∃ observations, observe v' = observe v ++ observations ∧
      CallbackTrace.StepTrace data p.start observations result final

/-- A property of the decoded metadata and cursor still holds after the fixed checker, whose
stack operations do not move the byte cursor. It applies to ordinary successful returns without
visitor premises. -/
theorem metadata_post {A B : Type} (st : code.OpIterState)
    (outer segment : List code.StackType)
    (values : st.vals.val = outer ++ segment) (base : (Control.base st).val = outer.length)
    (capacity : st.vals.val.length < Usize.max)
    (decode : Result (core.result.Result A error.OpError × code.OpIterState))
    (pops : A → List wasm_types.ValueType) (output : A → Option wasm_types.ValueType)
    (metadata : A → B) (P : B → Usize → Prop)
    (decoded : decode ⦃ r => r.2.vals = st.vals ∧ r.2.ctrls = st.ctrls ∧
      ∀ a, r.1 = .Ok a → P (metadata a) r.2.pos ⦄)
    (value : B) (final : code.OpIterState)
    (run : metadataOperands decode pops output metadata = .ok (.Ok value, final)) :
    P value final.pos := by
  obtain ⟨⟨res, middle⟩, hr, hv, hc, hp⟩ := WP.spec_imp_exists decoded
  dsimp only at hv hc hp
  cases res with
  | Err e => simp [metadataOperands, hr] at run
  | Ok a =>
    obtain ⟨⟨res, out⟩, hout, _, hpos, _⟩ := WP.spec_imp_exists
      (Simd.readFixed.segment middle (pops a) (output a) outer segment
        (by simpa [hv] using values) (by simpa [Control.base, hc] using base)
        (by simpa [hv] using capacity))
    dsimp only at hpos
    cases res with
    | Err e => simp [metadataOperands, hr, hout] at run
    | Ok u =>
      cases u
      simp only [metadataOperands, hr, bind_ok, Std.uncurry] at run
      rw [hout] at run
      simp only [bind_ok, Std.uncurry, Result.ok.injEq,
        Prod.mk.injEq, core.result.Result.Ok.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      simpa [hpos] using hp a rfl

theorem metadata_bytes {data env locals index st} (p : Pending data env locals index st)
    {A B : Type}
    (decode : Result (core.result.Result A error.OpError × code.OpIterState))
    (pops : A → List wasm_types.ValueType) (output : A → Option wasm_types.ValueType)
    (metadata : A → B) (P : B → Usize → Prop)
    (decoded : decode ⦃ r => r.2.vals = st.core.vals ∧ r.2.ctrls = st.core.ctrls ∧
      ∀ a, r.1 = .Ok a → P (metadata a) r.2.pos ⦄)
    (capacity : st.core.vals.val.length < Usize.max)
    (value : B) (final : code.OpIterState)
    (run : metadataOperands decode pops output metadata = .ok (.Ok value, final)) :
    P value final.pos := by
  obtain ⟨_, outer, _, _, base, _, ctrls, _, stack⟩ := p.opened
  exact metadata_post st.core outer p.current.vals stack
    (by simp [Control.base, ctrls, base]) capacity decode pops output metadata P decoded value final run

theorem metadata_bytes_at {data env locals index st} (p : Pending data env locals index st)
    (next : Usize) {A B : Type}
    (decode : Result (core.result.Result A error.OpError × code.OpIterState))
    (pops : A → List wasm_types.ValueType) (output : A → Option wasm_types.ValueType)
    (metadata : A → B) (P : B → Usize → Prop)
    (decoded : decode ⦃ r => r.2.vals = st.core.vals ∧ r.2.ctrls = st.core.ctrls ∧
      ∀ a, r.1 = .Ok a → P (metadata a) r.2.pos ⦄)
    (capacity : st.core.vals.val.length < Usize.max)
    (value : B) (final : code.OpIterState)
    (run : metadataOperands decode pops output metadata = .ok (.Ok value, final)) :
    P value final.pos := by
  obtain ⟨_, outer, _, _, base, _, ctrls, _, stack⟩ := p.opened
  exact metadata_post {st.core with pos := next} outer p.current.vals stack
    (by simp [Control.base, ctrls, base]) capacity decode pops output metadata P decoded value final run

/-- A metadata reader that succeeds supplies an independent token and its byte span. -/
def ReadBytes {A : Type} (data : Slice U8) (start : Usize)
    (read : Result (core.result.Result A error.OpError × code.OpIterState))
    (action : A → Action) : Prop :=
  ∀ s a, read = .ok (.Ok a, s) → ∃ token,
    actionToken (action a) [] = some token ∧ (action a).opcode ≠ some 0x0E#u8 ∧
    At data start token s.pos

end Itasca.Wasm2.CallbackBytes

end

/-! ## BytesReferences -/

section

/-!
# Byte provenance for reference and table callbacks

`StepRecords` facts for `ref.null`, `ref.is_null`, `ref.func`, `table.get`, `table.set` and typed
`select`: each callback receives the independently decoded instruction and its exact byte span.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2.CallbackBytes

open VisitorTrace CallbackTrace

theorem ref_null {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (ctx : code.Context)
    (capacity : st.core.vals.val.length < Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 208#u8) :
    StepRecords p visitor observe ctx 208#u8 := by
  intro v result final v' run
  rw [code.step_wasm2.ref_null] at run
  apply CallbackTrace.run_step_trace data p.start _ visitor observe records .ref_null ?_ v result final v' run
  intro s a hr
  refine ⟨.plain (.REF_NULL (Translate.referenceType a)), rfl, by simp [Action.opcode], ?_⟩
  rw [code.read_ref_null.fixed] at hr
  apply metadata_bytes p _ _ _ _ (fun rt pos => At data p.start (.plain (.REF_NULL (Translate.referenceType rt))) pos) ?_ capacity a s hr
  apply WP.spec_mono (code.take_reference_type.spec st.core data)
  rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
  exact ⟨hv, hc, fun rt hok => At.of_immediate p.inbounds byte p.pos
    (.reference (.refNull rt)) (hd rt hok)⟩

theorem typed_select {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (ctx : code.Context)
    (capacity : st.core.vals.val.length < Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 28#u8) :
    StepRecords p visitor observe ctx 28#u8 := by
  intro v result final v' run
  rw [code.step_wasm2.typed_select] at run
  apply CallbackTrace.run_step_trace data p.start _ visitor observe records .select_typed ?_ v result final v' run
  intro s a hr
  refine ⟨.plain (.SELECT (some [Translate.valueType a])), rfl, by simp [Action.opcode], ?_⟩
  rw [code.read_typed_select.fixed] at hr
  apply metadata_bytes p _ _ _ _ (fun ty pos => At data p.start (.plain (.SELECT (some [Translate.valueType ty]))) pos) ?_ capacity a s hr
  apply WP.spec_mono (selectType.spec st.core data)
  rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
  refine ⟨hv, hc, ?_⟩
  intro ty hok
  obtain ⟨count, hb, he⟩ := hd ty hok
  exact At.of_immediate p.inbounds byte p.pos (.reference (.selectTyped ty he)) hb

theorem table_get {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (ctx : code.Context)
    (capacity : st.core.vals.val.length < Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 37#u8) :
    StepRecords p visitor observe ctx 37#u8 := by
  intro v result final v' run
  rw [code.step_wasm2.table_get] at run
  apply CallbackTrace.run_step_trace data p.start _ visitor observe records .table_get ?_ v result final v' run
  intro s a hr
  refine ⟨.plain (.TABLE_GET (.mk_uN a.val)), rfl, by simp [Action.opcode], ?_⟩
  rw [code.read_table_get.fixed] at hr
  apply metadata_bytes p _ _ _ _ (fun idx pos => At data p.start (.plain (.TABLE_GET (.mk_uN idx.val))) pos) ?_ capacity a s hr
  apply WP.spec_mono (code.take_table.spec st.core data env)
  rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
  refine ⟨hv, hc, ?_⟩
  rintro ⟨idx, ty⟩ hok
  obtain ⟨bytes, hs, hl, hb, he⟩ := (hd idx ty hok).1
  exact At.of_immediate p.inbounds byte p.pos (.reference (.tableGet idx he)) ⟨hs, hl, hb⟩

theorem table_set {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (ctx : code.Context)
    (capacity : st.core.vals.val.length < Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 38#u8) :
    StepRecords p visitor observe ctx 38#u8 := by
  intro v result final v' run
  rw [code.step_wasm2.table_set] at run
  apply CallbackTrace.run_step_trace data p.start _ visitor observe records .table_set ?_ v result final v' run
  intro s a hr
  refine ⟨.plain (.TABLE_SET (.mk_uN a.val)), rfl, by simp [Action.opcode], ?_⟩
  rw [code.read_table_set.fixed] at hr
  apply metadata_bytes p _ _ _ _ (fun idx pos => At data p.start (.plain (.TABLE_SET (.mk_uN idx.val))) pos) ?_ capacity a s hr
  apply WP.spec_mono (code.take_table.spec st.core data env)
  rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
  refine ⟨hv, hc, ?_⟩
  rintro ⟨idx, ty⟩ hok
  obtain ⟨bytes, hs, hl, hb, he⟩ := (hd idx ty hok).1
  exact At.of_immediate p.inbounds byte p.pos (.reference (.tableSet idx he)) ⟨hs, hl, hb⟩

theorem ref_func {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (ctx : code.Context)
    (capacity : st.core.vals.val.length < Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 210#u8) :
    StepRecords p visitor observe ctx 210#u8 := by
  intro v result final v' run
  rw [code.step_wasm2.ref_func] at run
  apply CallbackTrace.run_step_trace data p.start _ visitor observe records .ref_func ?_ v result final v' run
  intro s a hr
  refine ⟨.plain (.REF_FUNC (.mk_uN a.val)), rfl, by simp [Action.opcode], ?_⟩
  have spec := code.read_ref_func.spec st.core data env capacity
  rw [hr, WP.spec_ok] at spec
  obtain ⟨bytes, hs, hl, hb, he⟩ := (spec.2 a rfl).1
  exact At.of_immediate p.inbounds byte p.pos (.reference (.refFunc a he)) ⟨hs, hl, hb⟩

theorem ref_is_null {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (ctx : code.Context)
    (capacity : st.core.vals.val.length < Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 209#u8) :
    StepRecords p visitor observe ctx 209#u8 := by
  intro v result final v' run
  rw [code.step_wasm2.ref_is_null] at run
  apply CallbackTrace.run_step_trace data p.start _ visitor observe records (fun _ => .ref_is_null) ?_ v result final v' run
  intro s a hr
  refine ⟨.plain .REF_IS_NULL, rfl, by simp [Action.opcode], ?_⟩
  obtain ⟨_, outer, _, _, base, _, ctrls, _, stack⟩ := p.opened
  have spec := code.read_ref_is_null.segment st.core outer p.current.vals stack
    (by simp [Control.base, ctrls, base]) capacity
  rw [hr, WP.spec_ok] at spec
  dsimp only at spec
  exact At.of_immediate p.inbounds byte p.pos (.reference .refIsNull)
    (by simpa [spec.2.1] using Wasm1.BytesAt.nil data st.core.pos (by have := p.pos; have := p.inbounds; omega))

end Itasca.Wasm2.CallbackBytes

end
