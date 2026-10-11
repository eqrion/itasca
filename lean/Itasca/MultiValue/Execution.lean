import Itasca.MultiValue.Dispatch
import Itasca.MultiValue.BinaryComplete

open Aeneas Aeneas.Std Result

namespace Itasca.MultiValue

/-- Successful prefixes of the real byte reader and opcode dispatch. This is
proof infrastructure; public completeness starts from independent typing. -/
inductive Execution (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32) :
    code.BodyState → code.BodyState → Prop where
  | nil (st) : Execution data env ctx index st st
  | cons (st next last : code.BodyState) (opcode : U8) (pos : Usize) :
      st.blocks.val ≠ [] →
      reader.read_byte data st.core.pos = .ok (.Ok (opcode, pos)) →
      step { st with core := { st.core with pos := pos } } data env ctx index opcode =
        .ok (.Ok (), next) →
      Execution data env ctx index next last → Execution data env ctx index st last

theorem Execution.append {data env ctx index a b c}
    (hab : Execution data env ctx index a b) (hbc : Execution data env ctx index b c) :
    Execution data env ctx index a c := by
  induction hab with
  | nil => exact hbc
  | cons st next last opcode pos hc hr hs _ ih =>
    exact .cons st next c opcode pos hc hr hs (ih hbc)

theorem Execution.single {data env ctx index st next opcode pos}
    (hc : st.blocks.val ≠ [])
    (hr : reader.read_byte data st.core.pos = .ok (.Ok (opcode, pos)))
    (hs : step { st with core := { st.core with pos := pos } } data env ctx index opcode =
      .ok (.Ok (), next)) : Execution data env ctx index st next :=
  .cons st next next opcode pos hc hr hs (.nil next)

theorem run_unfold (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (index : U32) (st : code.BodyState) :
    run data env ctx index st = (do
      let r ← loopBody data env ctx index st
      match r with
      | .done result => .ok result
      | .cont (s, _) => run data env ctx index s) := by
  unfold run code.validate_multi_value_body_loop code.validate_multi_value_body_with_loop code.body_loop_loop
  conv_lhs => rw [loop]
  dsimp only
  rw [code.validate_multi_value_body_loop.body_eq data env ctx]
  simp only [Std.bind_assoc]
  congr 1
  funext r
  cases r with
  | done => simp
  | cont pair => cases pair with | mk s v => cases v; simp only [bind_ok]

theorem Execution.loop_eq {data env ctx index st final}
    (h : Execution data env ctx index st final) :
    run data env ctx index st = run data env ctx index final := by
  induction h with
  | nil => rfl
  | cons st next last opcode pos hc hr hs _ ih =>
    rw [run_unfold, loopBody_eq]
    have hc' : st.core.ctrls.val ≠ [] := by simpa using hc
    simp [hc', hr, hs, continueStep, ih]

theorem Execution.finish {data env ctx index st final}
    (h : Execution data env ctx index st final) (hc : final.blocks.val = [])
    (hp : final.core.pos.val = data.length) : run data env ctx index st = .ok (.Ok ()) := by
  rw [h.loop_eq, run_unfold, loopBody_eq]
  have hpos : final.core.pos = Slice.len data := by scalar_tac
  simp [hc, hpos]

theorem Execution.public {data env locals index ft final}
    (h : Execution data env ⟨locals, alloc.vec.Vec.new _⟩ index (initial index) final)
    (hi : env.types.val[index.val]? = some ft)
    (hparams : ft.params.val.length ≤ 1000) (hresults : ft.results.val.length ≤ 1000)
    (hsize : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (hc : final.blocks.val = []) (hp : final.core.pos.val = data.length) :
    code.validate_multi_value_body data env locals index = .ok (.Ok ()) := by
  have hb : index.val < env.types.val.length := List.getElem?_eq_some_iff.mp hi |>.1
  have hloop := h.finish hc hp
  suffices hs : code.validate_multi_value_body data env locals index ⦃ r => r = .Ok () ⦄ by
    obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists hs
    exact hr
  rw [code.validate_multi_value_body.eq_core]
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
      change run data env ⟨locals, alloc.vec.Vec.new _⟩ index (initial index) ⦃ r => r = .Ok () ⦄
      simp [hloop]

end Itasca.MultiValue
