import Itasca.Wasm2.NumericExt.Dispatch
import Itasca.Binary.Leb128

/-!
# `step_wasm2` dispatch

Unfolding equations for the extracted `code.step_wasm2`, which adds references, bulk memory and
SIMD on top of `code.step_extended`. `code.step_wasm2.base` delegates ordinary opcodes,
`code.step_wasm2.prefixed` and `Wasm2.wasm2PrefixedStep` describe the `0xfc` prefix, and the
remaining `code.step_wasm2.*` lemmas give the reference, table and bulk arms as visitor runs.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

/-- Reference, table, bulk and SIMD dispatch do not inspect the result context. -/
theorem wasm2_context {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env)
    (ctx ctx' : code.Context) (opcode : U8) (v : V)
    (hscalar : opcode.val ∉ controlOpcodes) (hlocals : ctx.locals = ctx'.locals) :
    code.step_wasm2 visitor st data env ctx opcode v =
      code.step_wasm2 visitor st data env ctx' opcode v := by
  unfold code.step_wasm2
  simp only [extended_context visitor st data env ctx ctx' opcode v hscalar hlocals]

/-- The `0xfc` arm of `code.step_wasm2`: the miscellaneous prefix chooses the saturating
truncation and bulk families after one complete unsigned-LEB subopcode. -/
def wasm2PrefixedStep {V : Type} (visitor : code.OpVisitor V) (st : code.OpIterState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    Result (core.result.Result Unit error.OpError × code.OpIterState × V) := do
  let r ← reader.read_u32_leb data st.pos
  match r with
  | .Err e => .ok (.Err e, st, v)
  | .Ok (subopcode, next) =>
    if subopcode < 8#u32 then code.step_extended visitor st data env ctx 0xfc#u8 v
    else code.step_bulk visitor {st with pos := next} data env subopcode v

end Itasca.Wasm2

namespace Itasca

/-- Opcodes outside the reference, table, bulk and SIMD arms are handled by `code.step_extended`
without changing state. -/
theorem code.step_wasm2.base {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (opcode : U8) (v : V)
    (h : opcode.val ∉ [28, 37, 38, 208, 209, 210, 252, 253]) :
    code.step_wasm2 visitor st data env ctx opcode v =
      code.step_extended visitor st data env ctx opcode v := by
  unfold code.step_wasm2
  split <;> try rfl
  all_goals exact False.elim (h (by decide))

/-- Saturating subopcodes delegate with the original cursor, so the scalar
reader consumes the same complete unsigned-LEB prefix. -/
theorem code.step_wasm2.saturating {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (v : V) (subopcode : U32) (next : Usize)
    (hd : Leb128.Decoded data st.pos subopcode next) (hs : subopcode.val < 8) :
    code.step_wasm2 visitor st data env ctx 0xfc#u8 v =
      code.step_extended visitor st data env ctx 0xfc#u8 v := by
  have hr := reader.read_u32_leb.complete data st.pos subopcode next hd
  simp [code.step_wasm2, hr, core.result.Result.Insts.CoreOpsTry.branch, hs]

/-- The `0xfc` arm of `code.step_wasm2` equals `Wasm2.wasm2PrefixedStep`. -/
theorem code.step_wasm2.prefixed {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step_wasm2 visitor st data env ctx 0xfc#u8 v =
      Wasm2.wasm2PrefixedStep visitor st data env ctx v := by
  simp [code.step_wasm2, Wasm2.wasm2PrefixedStep]
  congr 1
  funext r
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
    obtain ⟨subopcode, next⟩ := pair
    simp [core.result.Result.Insts.CoreOpsTry.branch]

/-- `ref.null` (`0xd0`) runs `code.read_ref_null` and its visitor callback. -/
theorem code.step_wasm2.ref_null {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step_wasm2 visitor st data env ctx 208#u8 v =
      CoreVisitor.run (code.read_ref_null st data) (fun v s a => visitor.on_ref_null v s a) v := by
  simp [code.step_wasm2, CoreVisitor.run]
  congr 1
  funext pair
  obtain ⟨r, s⟩ := pair
  cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext pair
  obtain ⟨reply, w⟩ := pair
  cases reply <;> simp [code.visit]

/-- `ref.is_null` (`0xd1`) runs `code.read_ref_is_null` and its visitor callback. -/
theorem code.step_wasm2.ref_is_null {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step_wasm2 visitor st data env ctx 209#u8 v =
      CoreVisitor.run (code.read_ref_is_null st) (fun v s _ => visitor.on_ref_is_null v s) v := by
  simp [code.step_wasm2, CoreVisitor.run]
  congr 1
  funext pair
  obtain ⟨r, s⟩ := pair
  cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext pair
  obtain ⟨reply, w⟩ := pair
  cases reply <;> simp [code.visit]

/-- `ref.func` (`0xd2`) runs `code.read_ref_func` and its visitor callback. -/
theorem code.step_wasm2.ref_func {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step_wasm2 visitor st data env ctx 210#u8 v =
      CoreVisitor.run (code.read_ref_func st data env) (fun v s a => visitor.on_ref_func v s a) v := by
  simp [code.step_wasm2, CoreVisitor.run]
  congr 1
  funext pair
  obtain ⟨r, s⟩ := pair
  cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext pair
  obtain ⟨reply, w⟩ := pair
  cases reply <;> simp [code.visit]

/-- Typed `select` (`0x1c`) runs `code.read_typed_select` and its visitor callback. -/
theorem code.step_wasm2.typed_select {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step_wasm2 visitor st data env ctx 28#u8 v =
      CoreVisitor.run (code.read_typed_select st data) (fun v s a => visitor.on_select_typed v s a) v := by
  simp [code.step_wasm2, CoreVisitor.run]
  congr 1
  funext pair
  obtain ⟨r, s⟩ := pair
  cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext pair
  obtain ⟨reply, w⟩ := pair
  cases reply <;> simp [code.visit]

/-- `table.get` (`0x25`) runs `code.read_table_get` and its visitor callback. -/
theorem code.step_wasm2.table_get {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step_wasm2 visitor st data env ctx 37#u8 v =
      CoreVisitor.run (code.read_table_get st data env) (fun v s a => visitor.on_table_get v s a) v := by
  simp [code.step_wasm2, CoreVisitor.run]
  congr 1
  funext pair
  obtain ⟨r, s⟩ := pair
  cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext pair
  obtain ⟨reply, w⟩ := pair
  cases reply <;> simp [code.visit]

/-- `table.set` (`0x26`) runs `code.read_table_set` and its visitor callback. -/
theorem code.step_wasm2.table_set {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V) :
    code.step_wasm2 visitor st data env ctx 38#u8 v =
      CoreVisitor.run (code.read_table_set st data env) (fun v s a => visitor.on_table_set v s a) v := by
  simp [code.step_wasm2, CoreVisitor.run]
  congr 1
  funext pair
  obtain ⟨r, s⟩ := pair
  cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext pair
  obtain ⟨reply, w⟩ := pair
  cases reply <;> simp [code.visit]

/-- Every bulk subopcode is decoded once, before its selected metadata reader. -/
theorem code.step_wasm2.bulk {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (subopcode : U32) (next : Usize) (v : V)
    (hd : Leb128.Decoded data st.pos subopcode next) (hs : 8 ≤ subopcode.val) :
    code.step_wasm2 visitor st data env ctx 252#u8 v =
      code.step_bulk visitor {st with pos := next} data env subopcode v := by
  rw [code.step_wasm2.prefixed]
  have hr := reader.read_u32_leb.complete data st.pos subopcode next hd
  simp [Wasm2.wasm2PrefixedStep, hr, Nat.not_lt.mpr hs]

end Itasca
