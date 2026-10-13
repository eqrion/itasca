import Itasca.Binary.Wasm1.SyntaxComplete
import Itasca.Binary.Wasm1.EncodingComplete
import Itasca.Wasm1.Loop

open Aeneas Aeneas.Std

namespace Itasca.Wasm

/-- Finite successful execution of actual opcode reads and dispatches. This
relation is proof infrastructure, not the specification of valid input. -/
inductive Execution (data : Slice U8) (env : module.Env) (ctx : code.Context) :
    code.OpIterState → code.OpIterState → Prop where
  | nil (st : code.OpIterState) : Execution data env ctx st st
  | cons (st decoded next last : code.OpIterState) (opcode : U8) :
      st.ctrls.val ≠ [] →
      code.read_op st data = .ok (.Ok opcode, decoded) →
      code.step code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor decoded data env ctx opcode () =
        .ok (.Ok (), next, ()) →
      Execution data env ctx next last → Execution data env ctx st last

theorem Execution.append {data env ctx a b c}
    (hab : Execution data env ctx a b) (hbc : Execution data env ctx b c) :
    Execution data env ctx a c := by
  induction hab with
  | nil => exact hbc
  | cons st decoded next last opcode hc hr hs _ ih =>
    exact .cons st decoded next c opcode hc hr hs (ih hbc)

theorem Execution.single {data env ctx st decoded next opcode}
    (hc : st.ctrls.val ≠ [])
    (hr : code.read_op st data = .ok (.Ok opcode, decoded))
    (hs : code.step code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor decoded data env ctx opcode () =
      .ok (.Ok (), next, ())) : Execution data env ctx st next :=
  .cons st decoded next next opcode hc hr hs (.nil next)

/-- Every finite successful instruction prefix leaves the public loop at
exactly its final state; this theorem assumes no precomputed validator result. -/
theorem Execution.loop_eq {data env ctx st final}
    (h : Execution data env ctx st final) :
    code.validate_body_with_loop code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      data env ctx.locals ctx.results () st =
    code.validate_body_with_loop code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      data env ctx.locals ctx.results () final := by
  induction h with
  | nil => rfl
  | cons st decoded next final opcode hc hr hs _ ih =>
    rw [← ih]
    have hempty : st.ctrls.val.isEmpty = false := by simpa using hc
    unfold code.validate_body_with_loop
    conv_lhs => rw [loop]
    simp [code.validate_body_with_loop.body, code.control_stack_empty,
      alloc.vec.Vec.is_empty, hempty, hr, hs, core.result.Result.Insts.CoreOpsTry.branch]

theorem Execution.finish {data env ctx st final}
    (h : Execution data env ctx st final) (hc : final.ctrls.val = [])
    (hp : final.pos.val = data.length) :
    code.validate_body_with_loop code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      data env ctx.locals ctx.results () st = .ok (.Ok (), ()) := by
  rw [h.loop_eq]
  have hpos : final.pos = Slice.len data := by scalar_tac
  unfold code.validate_body_with_loop
  rw [loop]
  simp [code.validate_body_with_loop.body, code.control_stack_empty,
    alloc.vec.Vec.is_empty, hc, hpos]

theorem Execution.public {data env ctx bt final}
    (h : Execution data env ctx (Body.initial bt) final)
    (hresults : ctx.results.val = Control.results bt)
    (hsize : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (hc : final.ctrls.val = []) (hp : final.pos.val = data.length) :
    code.validate_body data env ctx = .ok (.Ok ()) := by
  have hlimit : ¬ Slice.len data > limits.MAX_FUNCTION_BYTES := by scalar_tac
  have hloop := h.finish hc hp
  simp [code.validate_body, code.validate_body_with.eq_model, code.validate_body_with_model, hlimit,
    code.start_function.spec (alloc.vec.Vec.deref ctx.results) bt
      (by simpa [alloc.vec.Vec.deref] using hresults), hloop]

end Itasca.Wasm
