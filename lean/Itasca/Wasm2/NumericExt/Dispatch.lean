import Itasca.Binary.Wasm2.NumericExtensions
import Itasca.Wasm2.Step.ScalarContext
import Itasca.Visitor.Accepts

open Aeneas Aeneas.Std

namespace Itasca.MultiValue.NumericExtensions

private theorem scalar_eq {ty} {a b : UScalar ty} : a = b ↔ a.val = b.val :=
  ⟨congrArg UScalar.val, UScalar.eq_of_val_eq⟩

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
    simp [code.saturating_types, saturatingMeaning, scalar_eq, show opcode.val ≠ 0 by omega,
      show opcode.val ≠ 1 by omega, show opcode.val ≠ 2 by omega,
      show opcode.val ≠ 3 by omega, show opcode.val ≠ 4 by omega,
      show opcode.val ≠ 5 by omega, show opcode.val ≠ 6 by omega,
      show opcode.val ≠ 7 by omega]
    split <;> simp_all
    all_goals exact (by decide : ¬ (8 ≤ _)) hn

theorem sign_properties {opcode op} (h : signMeaning opcode = some op) :
    op.binary = false ∧ op.output = op.input ∧ 192 ≤ opcode.val ∧ opcode.val ≤ 196 := by
  unfold signMeaning at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> try contradiction
  all_goals subst op; simp_all [i32Extend8, i32Extend16, i64Extend8, i64Extend16, i64Extend32]

theorem saturating_unary {opcode op} (h : saturatingMeaning opcode = some op) :
    op.binary = false := by
  unfold saturatingMeaning at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> try contradiction
  all_goals subst op; rfl

end Itasca.MultiValue.NumericExtensions

namespace Itasca.MultiValue

/-- The new scalar dispatcher retains the same context dependence as base instructions. -/
theorem extended_context {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env)
    (ctx ctx' : code.Context) (opcode : U8) (v : V)
    (hscalar : opcode.val ∉ controlOpcodes) (hlocals : ctx.locals = ctx'.locals) :
    code.step_extended visitor st data env ctx opcode v =
      code.step_extended visitor st data env ctx' opcode v := by
  unfold code.step_extended
  rw [scalar_context visitor st data env ctx ctx' opcode v hscalar hlocals]

end Itasca.MultiValue

namespace Itasca

/-- Sign extensions perform the independently specified unary operation. -/
theorem code.step_extended.sign {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (opcode : U8) (op : Numeric.Operation) (v : V)
    (hmap : MultiValue.NumericExtensions.signMeaning opcode = some op) :
    code.step_extended visitor st data env ctx opcode v =
      CoreVisitor.run (code.read_conversion st op.input op.output)
        (fun v s (_ : Unit) => code.visit_sign_extension visitor v s opcode) v := by
  have ht := MultiValue.NumericExtensions.sign_table opcode
  rw [hmap] at ht
  have ho := (MultiValue.NumericExtensions.sign_properties hmap).2.1
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

/-- Ordinary scalar opcodes retain the previous dispatcher. -/
theorem code.step_extended.base {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (opcode : U8) (v : V)
    (hmap : MultiValue.NumericExtensions.signMeaning opcode = none)
    (hprefix : opcode ≠ code.OP_MISC_PREFIX) :
    code.step_extended visitor st data env ctx opcode v =
      code.step visitor st data env ctx opcode v := by
  have ht := MultiValue.NumericExtensions.sign_table opcode
  simp [hmap] at ht
  simp [code.step_extended, ht, hprefix]

end Itasca

namespace Itasca.MultiValue

/-- Prefix decoding keeps the full unsigned LEB subopcode and exact reader state. -/
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

end Itasca.MultiValue

namespace Itasca

/-- The independent prefix adapter is an exact factorization of extracted dispatch. -/
theorem code.step_extended.prefixed {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (v : V) :
    code.step_extended visitor st data env ctx 0xFC#u8 v =
      MultiValue.prefixedStep visitor st data v := by
  unfold code.step_extended
  have he : code.sign_extension_type 0xFC#u8 = .ok none := rfl
  rw [he]
  simp only [bind_ok, global_simps, ↓reduceIte, MultiValue.prefixedStep]
  congr 1
  funext r
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
    obtain ⟨subopcode, next⟩ := pair
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      MultiValue.NumericExtensions.saturating_table, Std.uncurry]
    try dsimp only
    cases hm : MultiValue.NumericExtensions.saturatingMeaning subopcode with
    | none => simp [hm]
    | some op =>
      simp only [hm, Option.map_some, bind_ok, Std.uncurry]
      try dsimp only
      unfold CoreVisitor.run
      congr 1
      funext pair
      obtain ⟨r, s⟩ := pair
      cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      congr 1

end Itasca
