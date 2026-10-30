import Itasca.Wasm2.LoopDispatch
import Itasca.Wasm2.Control.FuncType
import Itasca.Binary.Wasm2.EncodingComplete
import Itasca.Wasm2.Step.Context

/-!
# Successful loop prefixes

`Execution` is the relation of successful runs of the extracted body loop (`code.body_loop_loop`
with the empty visitor) between two states. `Execution.public` turns a run that ends with no open
frames at the end of the body into acceptance by `code.bodyCore`. This is proof infrastructure for
completeness, which starts from independent typing.
-/

open Aeneas Aeneas.Std Result

namespace Itasca.Wasm2

/-- Successful prefixes of the real byte reader and opcode dispatch. -/
inductive Execution (data : Slice U8) (env : metadata.Env) (profile : ValidationProfile)
    (ctx : code.Context) (index : U32) : code.BodyState → code.BodyState → Prop where
  | nil (st) : Execution data env profile ctx index st st
  | cons (st next last : code.BodyState) (opcode : U8) (pos : Usize) :
      st.blocks.val ≠ [] →
      reader.read_byte data st.core.pos = .ok (.Ok (opcode, pos)) →
      code.check_opcode profile opcode = .ok (.Ok ()) →
      step { st with core := { st.core with pos := pos } } data env profile ctx index opcode =
        .ok (.Ok (), next) →
      Execution data env profile ctx index next last → Execution data env profile ctx index st last

theorem Execution.append {data env profile ctx index a b c}
    (hab : Execution data env profile ctx index a b)
    (hbc : Execution data env profile ctx index b c) :
    Execution data env profile ctx index a c := by
  induction hab with
  | nil => exact hbc
  | cons st next last opcode pos hc hr ho hs _ ih =>
    exact .cons st next c opcode pos hc hr ho hs (ih hbc)

theorem Execution.single {data env profile ctx index st next opcode pos}
    (hc : st.blocks.val ≠ [])
    (hr : reader.read_byte data st.core.pos = .ok (.Ok (opcode, pos)))
    (ho : code.check_opcode profile opcode = .ok (.Ok ()))
    (hs : step { st with core := { st.core with pos := pos } } data env profile ctx index opcode =
      .ok (.Ok (), next)) : Execution data env profile ctx index st next :=
  .cons st next next opcode pos hc hr ho hs (.nil next)

theorem run_unfold (data : Slice U8) (env : metadata.Env) (profile : ValidationProfile)
    (ctx : code.Context) (index : U32) (st : code.BodyState) :
    run data env profile ctx index st = (do
      let r ← loopBody data env profile ctx index st
      match r with
      | .done result => .ok result
      | .cont (s, _) => run data env profile ctx index s) := by
  unfold run Wasm2.emptyVisitorLoop code.body_loop_loop
  conv_lhs => rw [loop]
  dsimp only
  rw [Wasm2.emptyVisitorLoop.body_eq data env ctx]
  simp only [Std.bind_assoc]
  congr 1
  funext r
  cases r with
  | done => simp
  | cont pair => cases pair with | mk s v => cases v; simp only [bind_ok]

theorem Execution.loop_eq {data env profile ctx index st final}
    (h : Execution data env profile ctx index st final) :
    run data env profile ctx index st = run data env profile ctx index final := by
  induction h with
  | nil => rfl
  | cons st next last opcode pos hc hr ho hs _ ih =>
    rw [run_unfold, loopBody_eq]
    have hc' : st.core.ctrls.val ≠ [] := by simpa using hc
    simp [hc', hr, ho, hs, continueStep, ih]

theorem Execution.finish {data env profile ctx index st final}
    (h : Execution data env profile ctx index st final) (hc : final.blocks.val = [])
    (hp : final.core.pos.val = data.length) :
    run data env profile ctx index st = .ok (.Ok ()) := by
  rw [h.loop_eq, run_unfold, loopBody_eq]
  have hpos : final.core.pos = Slice.len data := by scalar_tac
  simp [hc, hpos]

/-- A successful prefix from the initial state to a closed body at the end of the data makes
`code.bodyCore` accept. -/
theorem Execution.public {data env profile locals results index ft final}
    (h : Execution data env profile ⟨locals, results⟩ index (initial index) final)
    (hi : env.types.val[index.val]? = some ft)
    (hparams : ft.params.val.length ≤ 1000) (hresults : ft.results.val.length ≤ 1000)
    (hsize : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (hc : final.blocks.val = []) (hp : final.core.pos.val = data.length) :
    code.bodyCore data env locals results index profile = .ok (.Ok ()) := by
  have hb : index.val < env.types.val.length := List.getElem?_eq_some_iff.mp hi |>.1
  have hloop := h.finish hc hp
  suffices hs : code.bodyCore data env locals results index profile ⦃ r => r = .Ok () ⦄ by
    obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists hs
    exact hr
  unfold code.bodyCore
  dsimp only
  split
  · scalar_tac
  · step
    split
    · scalar_tac
    · step as ⟨actual, hactual⟩
      have he : actual = ft := by
        have hx := (List.getElem?_eq_some_iff.mp hi).2
        simp_all
      rw [he, code.check_func_type.complete ft hparams hresults]
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        code.push_frame.initial]
      change run data env profile ⟨locals, results⟩ index (initial index) ⦃ r => r = .Ok () ⦄
      simp [hloop]

end Itasca.Wasm2

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

/-- Return typing is supplied by the selected signature descriptor, so the
semantic result context can be erased to the runtime's scalar context. -/
theorem Execution.change_context {data env profile ctx index st final}
    (h : Execution data env profile ctx index st final) (ctx' : code.Context)
    (hlocals : ctx.locals = ctx'.locals) : Execution data env profile ctx' index st final := by
  induction h with
  | nil st => exact .nil st
  | cons st next last opcode pos hc hr ho hs _ ih =>
    exact .cons st next last opcode pos hc hr ho
      ((step_context _ data env profile ctx ctx' index opcode hlocals).symm.trans hs) ih

end Itasca.Wasm2
