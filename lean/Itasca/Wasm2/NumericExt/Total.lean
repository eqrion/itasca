import Itasca.Binary.Wasm2.DeclaredReferences
import Itasca.Wasm2.Step.ScalarContext
import Itasca.Visitor.Accepts
import Itasca.Wasm2.Scalar.Env

/-!
Sections, each formerly its own module: Dispatch, Total.
-/

/-! ## Dispatch -/

section

/-!
# Numeric extension dispatch

Unfolding equations for the extracted `code.step_extended`, which adds the sign-extension and
saturating truncation opcodes on top of the shared `code.step`. `sign_table` and `saturating_table`
relate the extracted type tables to the independent meanings, `code.step_extended.sign`,
`code.step_extended.base` and `code.step_extended.prefixed` give the three dispatch arms, and
`Wasm2.prefixedStep` is the independent view of the `0xfc` prefix arm.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2.NumericExtensions

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

end Itasca.Wasm2.NumericExtensions

namespace Itasca.Wasm2

/-- `code.step_extended` observes local types but never function results, like `code.step`. -/
theorem extended_context {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env)
    (ctx ctx' : code.Context) (opcode : U8) (v : V)
    (hscalar : opcode.val ∉ controlOpcodes) (hlocals : ctx.locals = ctx'.locals) :
    code.step_extended visitor st data env ctx opcode v =
      code.step_extended visitor st data env ctx' opcode v := by
  unfold code.step_extended
  rw [scalar_context visitor st data env ctx ctx' opcode v hscalar hlocals]

end Itasca.Wasm2

namespace Itasca

/-- Sign extensions perform the independently specified unary operation. -/
theorem code.step_extended.sign {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (opcode : U8) (op : Numeric.Operation) (v : V)
    (hmap : Wasm2.NumericExtensions.signMeaning opcode = some op) :
    code.step_extended visitor st data env ctx opcode v =
      CoreVisitor.run (code.read_conversion st op.input op.output)
        (fun v s (_ : Unit) => code.visit_sign_extension visitor v s opcode) v := by
  have ht := Wasm2.NumericExtensions.sign_table opcode
  rw [hmap] at ht
  have ho := (Wasm2.NumericExtensions.sign_properties hmap).2.1
  simp only [Option.map_some] at ht
  simp only [code.step_extended, ht, bind_ok]
  rw [ho]
  unfold CoreVisitor.run
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
    (hmap : Wasm2.NumericExtensions.signMeaning opcode = none)
    (hprefix : opcode ≠ code.OP_MISC_PREFIX) :
    code.step_extended visitor st data env ctx opcode v =
      code.step visitor st data env ctx opcode v := by
  have ht := Wasm2.NumericExtensions.sign_table opcode
  simp [hmap] at ht
  simp [code.step_extended, ht, hprefix]

end Itasca

namespace Itasca.Wasm2

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
      CoreVisitor.run (code.read_conversion s op.input op.output)
        (fun v s (_ : Unit) => code.visit_saturating visitor v s subopcode) v

end Itasca.Wasm2

namespace Itasca

/-- `Wasm2.prefixedStep` is an exact factorization of the `0xfc` arm of extracted dispatch. -/
theorem code.step_extended.prefixed {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (v : V) :
    code.step_extended visitor st data env ctx 0xFC#u8 v =
      Wasm2.prefixedStep visitor st data v := by
  unfold code.step_extended
  have he : code.sign_extension_type 0xFC#u8 = .ok none := rfl
  rw [he]
  simp only [bind_ok, global_simps, ↓reduceIte, Wasm2.prefixedStep]
  congr 1
  funext r
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
    obtain ⟨subopcode, next⟩ := pair
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      Wasm2.NumericExtensions.saturating_table, Std.uncurry]
    try dsimp only
    cases hm : Wasm2.NumericExtensions.saturatingMeaning subopcode with
    | none => simp
    | some op =>
      simp only [Option.map_some]
      try dsimp only
      unfold CoreVisitor.run
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
`FullVisitor.Total` and `FullVisitor.Accepts` lemmas show that the sign-extension and saturating
callbacks return or accept accordingly.
-/

open Aeneas Aeneas.Std

namespace Itasca.FullVisitor

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

end Itasca.FullVisitor

namespace Itasca.Wasm2

private theorem conversion_total (st : code.OpIterState) (input output : wasm_types.ValueType)
    (hs : Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
    code.read_conversion st input output ⦃ r => Control.Shape r.2 ∧
      r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ⦄ := by
  let n := (Control.base st).val
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
    (v : V) (hs : Control.Shape st) (hsize : st.vals.val.length < Usize.max)
    (hh : ∀ s a, ∃ res v', hook v s a = .ok (res, v')) :
    CoreVisitor.run (code.read_conversion st input output) hook v ⦃ r =>
      Control.Shape r.2.1 ∧ r.2.1.ctrls = st.ctrls ∧ r.2.1.pos = st.pos ⦄ := by
  apply WP.spec_mono (CoreVisitor.run.spec _ _ v
    (fun s => Control.Shape s ∧ s.ctrls = st.ctrls ∧ s.pos = st.pos) (fun _ _ => True) ?_ hh)
  · intro r h
    exact h.1
  · apply WP.spec_mono (conversion_total st input output hs hsize)
    exact fun _ h => ⟨h, by simp⟩

/-- `code.step_extended` terminates with ordinary returning hooks. -/
theorem extended_total {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (opcode : U8) (v : V) (hs : Control.Shape st)
    (hsize : st.vals.val.length < Usize.max)
    (hscalar : opcode.val ∉ controlOpcodes) (hv : FullVisitor.Total visitor) :
    code.step_extended visitor st data env ctx opcode v ⦃ r => Control.Shape r.2.1 ∧
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
        have hspan := Leb128.Decoded.span data st.pos subopcode next hd
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

end Itasca.Wasm2

end
