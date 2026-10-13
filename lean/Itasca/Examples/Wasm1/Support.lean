import Itasca.Wasm1.Loop
import Itasca.Handler.End

/-!
# Shared helpers for Wasm 1.0 body examples

Lemmas that unfold `code.validate_body_with_loop` one step at a time, for both a general visitor
(`loop_step_with`, `loop_done_with`, `loop_error_with`, `loop_trailing_with`) and the empty
visitor (`loop_step`, `loop_done`, `loop_error`, `loop_trailing`). `public_of_loop` connects a
loop run from the initial frame to the public `code.validate_body`. `read_at` and `step_end`
discharge opcode reads and `end` steps.
-/

open Aeneas Aeneas.Std

namespace Itasca.Examples.Wasm1Support

/-- A bounded slice literal. Fixtures are checked by the kernel, with no external evaluator. -/
def bytes (xs : List U8) (h : xs.length ≤ Usize.max := by scalar_tac) : Slice U8 :=
  alloc.vec.Vec.deref (alloc.vec.Vec.from xs h)

/-- A visiting loop run from the initial frame determines the public visiting body result. -/
theorem public_of_loop_with {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (bt : code.BlockType) (result : core.result.Result Unit error.OpError) (v v' : V)
    (hsize : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (hresults : ctx.results.val = Control.results bt)
    (hloop : code.validate_body_with_loop visitor data env ctx.locals ctx.results v (Wasm1.Loop.initial bt) =
      .ok (result, v')) :
    code.validate_body_with visitor data env ctx v = .ok (result, v') := by
  have hguard : ¬ Slice.len data > limits.MAX_FUNCTION_BYTES := by scalar_tac
  simp [code.validate_body_with.eq_model, code.validate_body_with_model, hguard,
    code.start_function.spec (alloc.vec.Vec.deref ctx.results) bt
      (by simpa [alloc.vec.Vec.deref] using hresults), hloop]

/-- A visiting loop with no open frame accepts at the end of the input. -/
theorem loop_done_with {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V)
    (st : code.OpIterState) (hc : st.ctrls.val = []) (hp : st.pos = Slice.len data) :
    code.validate_body_with_loop visitor data env ctx.locals ctx.results v st = .ok (.Ok (), v) := by
  unfold code.validate_body_with_loop
  rw [loop]
  simp [code.validate_body_with_loop.body, code.control_stack_empty, alloc.vec.Vec.is_empty, hc, hp]

/-- A visiting loop with no open frame rejects bytes after the final `end`. -/
theorem loop_trailing_with {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V)
    (st : code.OpIterState) (hc : st.ctrls.val = []) (hp : st.pos ≠ Slice.len data) :
    code.validate_body_with_loop visitor data env ctx.locals ctx.results v st =
      .ok (.Err .TrailingBytes, v) := by
  unfold code.validate_body_with_loop
  rw [loop]
  simp [code.validate_body_with_loop.body, code.control_stack_empty, alloc.vec.Vec.is_empty, hc, hp]

/-- One accepted visiting step continues the loop from the step's state. -/
theorem loop_step_with {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (v v' : V)
    (st decoded next : code.OpIterState) (opcode : U8) (hc : st.ctrls.val ≠ [])
    (hr : code.read_op st data = .ok (.Ok opcode, decoded))
    (hs : code.step visitor decoded data env ctx opcode v = .ok (.Ok (), next, v')) :
    code.validate_body_with_loop visitor data env ctx.locals ctx.results v st =
      code.validate_body_with_loop visitor data env ctx.locals ctx.results v' next := by
  have hempty : st.ctrls.val.isEmpty = false := by simpa using hc
  unfold code.validate_body_with_loop
  conv_lhs => rw [loop]
  simp [code.validate_body_with_loop.body, code.control_stack_empty, alloc.vec.Vec.is_empty,
    hempty, hr, hs, core.result.Result.Insts.CoreOpsTry.branch]

/-- One rejected visiting step ends the loop with the step's error. -/
theorem loop_error_with {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (v v' : V)
    (st decoded next : code.OpIterState) (opcode : U8) (e : error.OpError) (hc : st.ctrls.val ≠ [])
    (hr : code.read_op st data = .ok (.Ok opcode, decoded))
    (hs : code.step visitor decoded data env ctx opcode v = .ok (.Err e, next, v')) :
    code.validate_body_with_loop visitor data env ctx.locals ctx.results v st = .ok (.Err e, v') := by
  have hempty : st.ctrls.val.isEmpty = false := by simpa using hc
  unfold code.validate_body_with_loop
  rw [loop]
  simp [code.validate_body_with_loop.body, code.control_stack_empty, alloc.vec.Vec.is_empty,
    hempty, hr, hs, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- An empty-visitor loop run from the initial frame determines the public body result. -/
theorem public_of_loop (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (bt : code.BlockType) (result : core.result.Result Unit error.OpError)
    (hsize : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (hresults : ctx.results.val = Control.results bt)
    (hloop : code.validate_body_with_loop code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      data env ctx.locals ctx.results () (Wasm1.Loop.initial bt) = .ok (result, ())) :
    code.validate_body data env ctx = .ok result := by
  have hguard : ¬ Slice.len data > limits.MAX_FUNCTION_BYTES := by scalar_tac
  simp [code.validate_body, code.validate_body_with.eq_model, code.validate_body_with_model, hguard,
    code.start_function.spec (alloc.vec.Vec.deref ctx.results) bt
      (by simpa [alloc.vec.Vec.deref] using hresults), hloop]

/-- `loop_done_with` for the empty visitor. -/
theorem loop_done (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (st : code.OpIterState) (hc : st.ctrls.val = []) (hp : st.pos = Slice.len data) :
    code.validate_body_with_loop code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      data env ctx.locals ctx.results () st = .ok (.Ok (), ()) :=
  loop_done_with _ data env ctx () st hc hp

/-- `loop_trailing_with` for the empty visitor. -/
theorem loop_trailing (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (st : code.OpIterState) (hc : st.ctrls.val = []) (hp : st.pos ≠ Slice.len data) :
    code.validate_body_with_loop code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      data env ctx.locals ctx.results () st = .ok (.Err .TrailingBytes, ()) :=
  loop_trailing_with _ data env ctx () st hc hp

/-- `loop_step_with` for the empty visitor. -/
theorem loop_step (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (st decoded next : code.OpIterState) (opcode : U8) (hc : st.ctrls.val ≠ [])
    (hr : code.read_op st data = .ok (.Ok opcode, decoded))
    (hs : code.step code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor decoded data env ctx opcode () =
      .ok (.Ok (), next, ())) :
    code.validate_body_with_loop code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      data env ctx.locals ctx.results () st =
    code.validate_body_with_loop code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      data env ctx.locals ctx.results () next :=
  loop_step_with _ data env ctx () () st decoded next opcode hc hr hs

/-- `loop_error_with` for the empty visitor. -/
theorem loop_error (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (st decoded next : code.OpIterState) (opcode : U8) (e : error.OpError) (hc : st.ctrls.val ≠ [])
    (hr : code.read_op st data = .ok (.Ok opcode, decoded))
    (hs : code.step code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor decoded data env ctx opcode () =
      .ok (.Err e, next, ())) :
    code.validate_body_with_loop code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      data env ctx.locals ctx.results () st = .ok (.Err e, ()) :=
  loop_error_with _ data env ctx () () st decoded next opcode e hc hr hs

/-- Reading an in-bounds opcode advances the cursor by one byte. -/
theorem read_at (data : Slice U8) (st : code.OpIterState) (next : Usize) (opcode : U8)
    (hp : st.pos.val < data.length) (hn : next.val = st.pos.val + 1)
    (hb : data.val[st.pos.val] = opcode) :
    code.read_op st data = .ok (.Ok opcode, {st with pos := next}) := by
  obtain ⟨q, hr, hq⟩ := code.read_op_success st data hp
  have heq : q = next := UScalar.eq_of_val_eq (hq.trans hn.symm)
  simpa [heq, hb] using hr

/-- An accepted `end` read is an accepted empty-visitor step. -/
theorem step_end (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (st next : code.OpIterState) (kind : code.LabelKind) (bt : code.BlockType)
    (hr : code.read_end st = .ok (.Ok (kind, bt), next)) :
    code.step code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor st data env ctx code.OP_END () =
      .ok (.Ok (), next, ()) := by
  simp [global_simps, hr,
    code.OpVisitor.on_end.default, code.visit, core.result.Result.Insts.CoreOpsTry.branch]

end Itasca.Examples.Wasm1Support
