import Itasca.Binary.Body.Encoding
import Itasca.Body.Step.ScalarContext
import Itasca.Visitor.Total
import Itasca.Body.Scalar.Env
import Itasca.Visitor.RunTrace

/-!
Proofs for Body / NumericExt.

This module collects Total, Visitor.
Each section documents its contracts and consumers.
-/

/-! ## Total -/

section

/-! ## Dispatch -/

section

/-!
# Numeric extension dispatch

Unfolding equations for the extracted `code.step_extended`, which adds the sign-extension and
saturating truncation opcodes on top of the shared `code.step`. `sign_table` and `saturating_table`
relate the extracted type tables to the independent meanings, `code.step_extended.sign`,
`code.step_extended.base` and `code.step_extended.prefixed` give the three dispatch arms, and
`Body.prefixedStep` is the independent view of the `0xfc` prefix arm.
-/

open Aeneas Aeneas.Std

namespace Itasca.Body.NumericExtensions

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- Sign-extension effects agree with the independent opcode meaning. -/
theorem sign_table (opcode : U8) :
    code.sign_extension_type opcode = .ok ((signMeaning opcode).map (·.input)) := by
  rcases opcode with ⟨⟨n, hn⟩⟩
  change n < 256 at hn
  interval_cases n <;> (with_unfolding_all rfl)

/-- Saturating conversion effects agree with the independent prefix meaning. -/
theorem saturating_table (opcode : U32) :
    code.saturating_types opcode =
      .ok ((saturatingMeaning opcode).map (fun op => (op.input, op.output))) := by
  by_cases h : opcode.val < 8
  · rcases opcode with ⟨⟨n, hn⟩⟩
    change n < 8 at h
    interval_cases n <;> (with_unfolding_all rfl)
  · have hn : 8 ≤ opcode.val := by omega
    simp [code.saturating_types, saturatingMeaning, show opcode.val ≠ 0 by omega,
      show opcode.val ≠ 1 by omega, show opcode.val ≠ 2 by omega,
      show opcode.val ≠ 3 by omega, show opcode.val ≠ 4 by omega,
      show opcode.val ≠ 5 by omega, show opcode.val ≠ 6 by omega,
      show opcode.val ≠ 7 by omega]
    split <;> simp_all
    all_goals exact (by decide : ¬ (8 ≤ _)) hn

/-- Sign extensions are unary, keep their type, and occupy opcodes `0xc0` to `0xc4`. -/
theorem sign_properties {opcode op} (h : signMeaning opcode = some op) :
    op.binary = false ∧ op.output = op.input ∧ 192 ≤ opcode.val ∧ opcode.val ≤ 196 := by
  unfold signMeaning at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> try contradiction
  all_goals subst op; simp_all [i32Extend8, i32Extend16, i64Extend8, i64Extend16, i64Extend32]

/-- Saturating truncations are unary. -/
theorem saturating_unary {opcode op} (h : saturatingMeaning opcode = some op) :
    op.binary = false := by
  unfold saturatingMeaning at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> try contradiction
  all_goals subst op; rfl

end Itasca.Body.NumericExtensions

namespace Itasca.Body

/-- `code.step_extended` observes local types but never function results, like `code.step`. -/
theorem extended_context {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env)
    (ctx ctx' : code.Context) (opcode : U8) (v : V)
    (hscalar : opcode.val ∉ controlOpcodes) (hlocals : ctx.locals = ctx'.locals) :
    code.step_extended visitor st data env ctx opcode v =
      code.step_extended visitor st data env ctx' opcode v := by
  unfold code.step_extended
  rw [scalar_context visitor st data env ctx ctx' opcode v hscalar hlocals]

end Itasca.Body

namespace Itasca

/-- Sign extensions perform the independently specified unary operation. -/
theorem code.step_extended.sign {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (opcode : U8) (op : Body.Numeric.Operation) (v : V)
    (hmap : Body.NumericExtensions.signMeaning opcode = some op) :
    code.step_extended visitor st data env ctx opcode v =
      Visitor.Core.run (code.read_conversion st op.input op.output)
        (fun v s (_ : Unit) => code.visit_sign_extension visitor v s opcode) v := by
  have ht := Body.NumericExtensions.sign_table opcode
  rw [hmap] at ht
  have ho := (Body.NumericExtensions.sign_properties hmap).2.1
  simp only [Option.map_some] at ht
  simp only [code.step_extended, ht, bind_ok]
  rw [ho]
  unfold Visitor.Core.run
  congr 1
  funext pair
  obtain ⟨r, s⟩ := pair
  cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1

/-- Opcodes that are neither sign extensions nor the `0xfc` prefix are handled by `code.step`. -/
theorem code.step_extended.base {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (opcode : U8) (v : V)
    (hmap : Body.NumericExtensions.signMeaning opcode = none)
    (hprefix : opcode ≠ code.OP_MISC_PREFIX) :
    code.step_extended visitor st data env ctx opcode v =
      code.step visitor st data env ctx opcode v := by
  have ht := Body.NumericExtensions.sign_table opcode
  simp [hmap] at ht
  simp [code.step_extended, ht, hprefix]

end Itasca

namespace Itasca.Body

/-- The `0xfc` arm of `code.step_extended`. Prefix decoding keeps the full unsigned LEB subopcode
and exact reader state. -/
def prefixedStep {V : Type} (visitor : code.OpVisitor V) (st : code.OpIterState)
    (data : Slice U8) (v : V) :
    Result (core.result.Result Unit error.OpError × code.OpIterState × V) := do
  let decoded ← reader.read_u32_leb data st.pos
  match decoded with
  | .Err e => .ok (.Err e, st, v)
  | .Ok (subopcode, next) =>
    let s := {st with pos := next}
    match NumericExtensions.saturatingMeaning subopcode with
    | none => .ok (.Err .UnrecognizedOpcode, s, v)
    | some op =>
      Visitor.Core.run (code.read_conversion s op.input op.output)
        (fun v s (_ : Unit) => code.visit_saturating visitor v s subopcode) v

end Itasca.Body

namespace Itasca

/-- `Body.prefixedStep` is an exact factorization of the `0xfc` arm of extracted dispatch. -/
theorem code.step_extended.prefixed {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (v : V) :
    code.step_extended visitor st data env ctx 0xFC#u8 v =
      Body.prefixedStep visitor st data v := by
  unfold code.step_extended
  have he : code.sign_extension_type 0xFC#u8 = .ok none := rfl
  rw [he]
  simp only [bind_ok, global_simps, ↓reduceIte, Body.prefixedStep]
  congr 1
  funext r
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
    obtain ⟨subopcode, next⟩ := pair
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      Body.NumericExtensions.saturating_table, Std.uncurry]
    try dsimp only
    cases hm : Body.NumericExtensions.saturatingMeaning subopcode with
    | none => simp
    | some op =>
      simp only [Option.map_some]
      try dsimp only
      unfold Visitor.Core.run
      congr 1
      funext pair
      obtain ⟨r, s⟩ := pair
      cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      congr 1

end Itasca

end

/-! ## Total -/

section

/-!
# Numeric extension totality

Totality of `code.step_extended`. `extended_total` shows that it terminates on structurally
bounded stacks and keeps control depth for any visitor whose callbacks return, and the
`Visitor.Total` and `Visitor.Accepts` lemmas show that the sign-extension and saturating
callbacks return or accept accordingly.
-/

open Aeneas Aeneas.Std

namespace Itasca.Visitor

theorem Total.visit_sign_extension {V : Type} {visitor : code.OpVisitor V}
    (h : Total visitor) (v : V) (st : code.OpIterState) (opcode : U8) :
    ∃ res v', code.visit_sign_extension visitor v st opcode = .ok (res, v') := by
  unfold code.visit_sign_extension
  split
  · exact h.on_i32_extend8_s v st
  · exact h.on_i32_extend16_s v st
  · exact h.on_i64_extend8_s v st
  · exact h.on_i64_extend16_s v st
  · exact h.on_i64_extend32_s v st
  · exact ⟨.Ok (), v, rfl⟩

theorem Total.visit_saturating {V : Type} {visitor : code.OpVisitor V}
    (h : Total visitor) (v : V) (st : code.OpIterState) (opcode : U32) :
    ∃ res v', code.visit_saturating visitor v st opcode = .ok (res, v') := by
  unfold code.visit_saturating
  split
  · exact h.on_i32_trunc_sat_f32_s v st
  · exact h.on_i32_trunc_sat_f32_u v st
  · exact h.on_i32_trunc_sat_f64_s v st
  · exact h.on_i32_trunc_sat_f64_u v st
  · exact h.on_i64_trunc_sat_f32_s v st
  · exact h.on_i64_trunc_sat_f32_u v st
  · exact h.on_i64_trunc_sat_f64_s v st
  · exact h.on_i64_trunc_sat_f64_u v st
  · exact ⟨.Ok (), v, rfl⟩

theorem Accepts.visit_sign_extension {V : Type} {visitor : code.OpVisitor V}
    (h : Accepts visitor) (v : V) (st : code.OpIterState) (opcode : U8) :
    ∃ v', code.visit_sign_extension visitor v st opcode = .ok (.Ok (), v') := by
  unfold code.visit_sign_extension
  split
  · exact h.on_i32_extend8_s v st
  · exact h.on_i32_extend16_s v st
  · exact h.on_i64_extend8_s v st
  · exact h.on_i64_extend16_s v st
  · exact h.on_i64_extend32_s v st
  · exact ⟨v, rfl⟩

theorem Accepts.visit_saturating {V : Type} {visitor : code.OpVisitor V}
    (h : Accepts visitor) (v : V) (st : code.OpIterState) (opcode : U32) :
    ∃ v', code.visit_saturating visitor v st opcode = .ok (.Ok (), v') := by
  unfold code.visit_saturating
  split
  · exact h.on_i32_trunc_sat_f32_s v st
  · exact h.on_i32_trunc_sat_f32_u v st
  · exact h.on_i32_trunc_sat_f64_s v st
  · exact h.on_i32_trunc_sat_f64_u v st
  · exact h.on_i64_trunc_sat_f32_s v st
  · exact h.on_i64_trunc_sat_f32_u v st
  · exact h.on_i64_trunc_sat_f64_s v st
  · exact h.on_i64_trunc_sat_f64_u v st
  · exact ⟨v, rfl⟩

end Itasca.Visitor

namespace Itasca.Body

private theorem conversion_total (st : code.OpIterState) (input output : wasm_types.ValueType)
    (hs : Body.Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
    code.read_conversion st input output ⦃ r => Body.Control.Shape r.2 ∧
      r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ⦄ := by
  let n := (Body.Control.base st).val
  have hn : n ≤ st.vals.val.length := hs.base_le
  obtain ⟨⟨res, s⟩, hr, hc, hp, after, hv, _, _⟩ := WP.spec_imp_exists
    (code.read_conversion.segment st (st.vals.val.take n) (st.vals.val.drop n) input output
      (List.take_append_drop ..).symm (by simp [n, Nat.min_eq_left hn]) hsize)
  rw [hr, WP.spec_ok]
  refine ⟨hs.replace_operands hc ?_, hc, hp⟩
  simp [hv, n, Nat.min_eq_left hn]

private theorem conversion_run_total {V : Type} (st : code.OpIterState)
    (input output : wasm_types.ValueType)
    (hook : V → code.OpIterState → Unit → Result (core.result.Result Unit error.VisitError × V))
    (v : V) (hs : Body.Control.Shape st) (hsize : st.vals.val.length < Usize.max)
    (hh : ∀ s a, ∃ res v', hook v s a = .ok (res, v')) :
    Visitor.Core.run (code.read_conversion st input output) hook v ⦃ r =>
      Body.Control.Shape r.2.1 ∧ r.2.1.ctrls = st.ctrls ∧ r.2.1.pos = st.pos ⦄ := by
  apply WP.spec_mono (Visitor.Core.run.spec _ _ v
    (fun s => Body.Control.Shape s ∧ s.ctrls = st.ctrls ∧ s.pos = st.pos) (fun _ _ => True) ?_ hh)
  · intro r h
    exact h.1
  · apply WP.spec_mono (conversion_total st input output hs hsize)
    exact fun _ h => ⟨h, by simp⟩

/-- `code.step_extended` terminates with ordinary returning hooks. -/
theorem extended_total {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (opcode : U8) (v : V) (hs : Body.Control.Shape st)
    (hsize : st.vals.val.length < Usize.max)
    (hscalar : opcode.val ∉ controlOpcodes) (hv : Visitor.Total visitor) :
    code.step_extended visitor st data env ctx opcode v ⦃ r => Body.Control.Shape r.2.1 ∧
      r.2.1.ctrls.val.length = st.ctrls.val.length ∧ st.pos.val ≤ r.2.1.pos.val ⦄ := by
  cases hm : NumericExtensions.signMeaning opcode with
  | some op =>
    rw [code.step_extended.sign visitor st data env ctx opcode op v hm]
    apply WP.spec_mono (conversion_run_total st op.input op.output _ v hs hsize
      (fun s _ => hv.visit_sign_extension v s opcode))
    rintro r ⟨hh, hc, hp⟩
    exact ⟨hh, by simp [hc], by simp [hp]⟩
  | none =>
    by_cases hp : opcode = code.OP_MISC_PREFIX
    · have he : opcode = 0xFC#u8 := by simpa [global_simps] using hp
      rw [he]
      rw [code.step_extended.prefixed]
      obtain ⟨r, hr, hd⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data st.pos)
      unfold prefixedStep
      rw [hr]
      simp only [bind_ok]
      cases r with
      | Err e => simp [hs]
      | Ok pair =>
        obtain ⟨subopcode, next⟩ := pair
        have hspan := Binary.Leb128.Decoded.span data st.pos subopcode next hd
        cases hm : NumericExtensions.saturatingMeaning subopcode with
        | none =>
          simp only [hm, WP.spec_ok]
          exact ⟨⟨hs.ordered, hs.bounded⟩, trivial, Nat.le_of_lt hspan.1⟩
        | some op =>
          simp only [hm]
          apply WP.spec_mono (conversion_run_total {st with pos := next} op.input op.output _ v
            ⟨hs.ordered, hs.bounded⟩ hsize (fun s _ => hv.visit_saturating v s subopcode))
          rintro r ⟨hh, hc, hp⟩
          exact ⟨hh, by simp [hc], by simpa [hp] using Nat.le_of_lt hspan.1⟩
    · rw [code.step_extended.base visitor st data env ctx opcode v hm hp]
      exact scalar_total visitor st data env ctx opcode v hs hsize hscalar hv

end Itasca.Body

end

end

/-! ## Visitor -/

section

/-!
# Numeric extension visitor transfer

`Body.Visitor.extended_transfer` shows that a successful `code.step_extended` run under any
visitor can be replayed with a replacement visitor whose callbacks accept, ending in the same
operand state.
-/

open Aeneas Aeneas.Std

namespace Itasca.Body.Visitor

/-- Accepting replacement hooks preserve the state of every successful scalar
extension, including the cursor after a nonminimal prefix encoding. -/
theorem extended_transfer {V W : Type} (visitor : code.OpVisitor V)
    (replacement : code.OpVisitor W) (ha : Visitor.Accepts replacement)
    (st final : code.OpIterState) (data : Slice U8) (env : metadata.Env)
    (ctx ctx' : code.Context) (opcode : U8) (v : V) (v' : V) (w : W)
    (hscalar : opcode.val ∉ controlOpcodes) (hlocals : ctx.locals = ctx'.locals)
    (h : code.step_extended visitor st data env ctx opcode v = .ok (.Ok (), final, v')) :
    ∃ w', code.step_extended replacement st data env ctx' opcode w = .ok (.Ok (), final, w') := by
  cases hm : NumericExtensions.signMeaning opcode with
  | some op =>
    rw [code.step_extended.sign visitor st data env ctx opcode op v hm] at h
    rw [code.step_extended.sign replacement st data env ctx' opcode op w hm]
    exact Visitor.Core.run.accepted_lift _ _ _ v w final v' h
      (fun _ => ha.visit_sign_extension w final opcode)
  | none =>
    by_cases hp : opcode = code.OP_MISC_PREFIX
    · have he : opcode = 0xFC#u8 := by simpa [global_simps] using hp
      rw [he] at h ⊢
      rw [code.step_extended.prefixed] at h ⊢
      obtain ⟨r, hr⟩ := reader.read_u32_leb.total data st.pos
      simp only [prefixedStep, hr, bind_ok] at h ⊢
      cases r with
      | Err e => simp at h
      | Ok pair =>
        obtain ⟨subopcode, next⟩ := pair
        cases hm : NumericExtensions.saturatingMeaning subopcode with
        | none => simp [hm] at h
        | some op =>
          simp only [hm] at h ⊢
          exact Visitor.Core.run.accepted_lift _ _ _ v w final v' h
            (fun _ => ha.visit_saturating w final subopcode)
    · rw [code.step_extended.base visitor st data env ctx opcode v hm hp] at h
      rw [code.step_extended.base replacement st data env ctx' opcode w hm hp]
      have he := code.step.accepted_erase visitor st final data env ctx opcode v v' h
      rw [scalar_context _ _ data env ctx ctx' opcode () hscalar hlocals] at he
      exact code.step.accepted_lift replacement ha st final data env ctx' opcode w he

end Itasca.Body.Visitor

end
