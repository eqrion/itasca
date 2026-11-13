import Itasca.Wasm2.LoopDispatch
import Itasca.Wasm2.Control.FuncType
import Itasca.Binary.Wasm2.SyntaxUnique
import Itasca.Wasm2.Step.Context
import Itasca.Wasm2.Visitor.Total

/-!
Sections, each formerly its own module: Execution, Totality, SoundLoop.
-/

/-! ## Execution -/

section

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
inductive Execution (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) : code.BodyState → code.BodyState → Prop where
  | nil (st) : Execution data env ctx index st st
  | cons (st next last : code.BodyState) (opcode : U8) (pos : Usize) :
      st.blocks.val ≠ [] →
      reader.read_byte data st.core.pos = .ok (.Ok (opcode, pos)) →
      step { st with core := { st.core with pos := pos } } data env ctx index opcode =
        .ok (.Ok (), next) →
      Execution data env ctx index next last → Execution data env ctx index st last

theorem Execution.append {data env ctx index a b c}
    (hab : Execution data env ctx index a b)
    (hbc : Execution data env ctx index b c) :
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

theorem run_unfold (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) (st : code.BodyState) :
    run data env ctx index st = (do
      let r ← loopBody data env ctx index st
      match r with
      | .done result => .ok result
      | .cont (s, _) => run data env ctx index s) := by
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
    (hp : final.core.pos.val = data.length) :
    run data env ctx index st = .ok (.Ok ()) := by
  rw [h.loop_eq, run_unfold, loopBody_eq]
  have hpos : final.core.pos = Slice.len data := by scalar_tac
  simp [hc, hpos]

/-- A successful prefix from the initial state to a closed body at the end of the data makes
`code.bodyCore` accept. -/
theorem Execution.public {data env locals results index ft final}
    (h : Execution data env ⟨locals, results⟩ index (initial index) final)
    (hi : env.types.val[index.val]? = some ft)
    (hparams : ft.params.val.length ≤ 1000) (hresults : ft.results.val.length ≤ 1000)
    (hsize : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (hc : final.blocks.val = []) (hp : final.core.pos.val = data.length) :
    code.bodyCore data env locals results index = .ok (.Ok ()) := by
  have hb : index.val < env.types.val.length := List.getElem?_eq_some_iff.mp hi |>.1
  have hloop := h.finish hc hp
  suffices hs : code.bodyCore data env locals results index ⦃ r => r = .Ok () ⦄ by
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
      change run data env ⟨locals, results⟩ index (initial index) ⦃ r => r = .Ok () ⦄
      simp [hloop]

end Itasca.Wasm2

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

/-- Return typing is supplied by the selected signature descriptor, so the
semantic result context can be erased to the runtime's scalar context. -/
theorem Execution.change_context {data env ctx index st final}
    (h : Execution data env ctx index st final) (ctx' : code.Context)
    (hlocals : ctx.locals = ctx'.locals) : Execution data env ctx' index st final := by
  induction h with
  | nil st => exact .nil st
  | cons st next last opcode pos hc hr hs _ ih =>
    exact .cons st next last opcode pos hc hr
      ((step_context _ data env ctx ctx' index opcode hlocals).symm.trans hs) ih

end Itasca.Wasm2

end

/-! ## Totality -/

section

/-!
# Wasm 2.0 body totality

`Wasm2.emptyVisitorLoop.total` specializes the visitor-generic totality proof to the empty
visitor.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- The no-op loop specializes the totality proof for arbitrary returning
visitors; it has no separate termination induction. -/
theorem Wasm2.emptyVisitorLoop.total (data : Slice U8) (env : metadata.Env)
     (locals results : alloc.vec.Vec wasm_types.ValueType)
    (type_index : U32) (st : code.BodyState) (visitor : code.EmptyOpVisitor)
    (hdata : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (hs : Control.Shape st.core)
    (ha : st.blocks.val.length = st.core.ctrls.val.length)
    (hb : st.blocks.val.length ≤ st.core.pos.val + 1) :
    Wasm2.emptyVisitorLoop data env type_index st locals results visitor ⦃ _ => True ⦄ := by
  cases visitor
  obtain ⟨⟨r, v⟩, hr, _⟩ := WP.spec_imp_exists
    (code.body_loop_loop.total
      code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor FullVisitor.empty_total
      data env ⟨locals, results⟩ type_index st () hdata hs ha hb)
  simp [Wasm2.emptyVisitorLoop, hr]

end Itasca

end

/-! ## SoundLoop -/

section

/-!
# Soundness of the body loop

Reduces soundness of the body validator to a per-opcode obligation. `Steps` says that every
opcode step from a `Pending` state preserves the invariant on success, `run.sound` and `run.spec`
lift it through the loop by induction on the cursor, and `public_spec_of_steps` concludes
`Wasm2.Validated` for `code.bodyCore`. `Steps` is discharged in `Wasm2/Soundness`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

/-- Every opcode step from a `Pending` state either fails or yields a state satisfying
`Pending.After`. -/
def Steps (data : Slice U8) (env : metadata.Env)
    (locals : alloc.vec.Vec wasm_types.ValueType) (ctx : code.Context) (index : U32) : Prop :=
  ∀ st (p : Pending data env locals index st),
    step st data env ctx index (data.val[p.start.val]'p.inbounds) ⦃ r =>
      r.1 = .Ok () → p.After r.2 ⦄

/-- Each successful iteration extends the independent syntax and typing
invariant. Its strictly increasing cursor justifies the whole-body induction. -/
theorem run.sound (data : Slice U8) (env : metadata.Env)
    (locals : alloc.vec.Vec wasm_types.ValueType) (ctx : code.Context) (index : U32)
    (hsteps : Steps data env locals ctx index) (st : code.BodyState)
    (hi : State data env locals index st)
    (haccepted : run data env ctx index st = .ok (.Ok ())) :
    Validated data env locals index := by
  generalize he : Usize.max - st.core.pos.val = fuel
  induction fuel using Nat.strong_induction_on generalizing st with
  | h fuel ih =>
    rw [run_unfold, loopBody_eq] at haccepted
    by_cases hc : st.blocks.val = []
    · simp only [hc, if_true, bind_ok] at haccepted
      split at haccepted
      · rename_i hp
        exact hi.finished hc (by simpa using congrArg UScalar.val hp)
      · simp at haccepted
    · simp only [hc, if_false] at haccepted
      by_cases hp : st.core.pos.val < data.length
      · obtain ⟨r, hr, next, heq, hn⟩ := WP.spec_imp_exists (reader.read_byte.spec data st.core.pos hp)
        rw [heq] at hr
        rw [hr] at haccepted
        obtain ⟨p, hstart⟩ := hi.pending hc hp next hn
        obtain ⟨⟨result, s⟩, hs, hout⟩ := WP.spec_imp_exists (hsteps _ p)
        simp only [hstart] at hs
        simp only [bind_ok, hs] at haccepted
        cases result with
        | Err e => simp [continueStep] at haccepted
        | Ok v =>
          cases v
          simp only [continueStep] at haccepted
          obtain ⟨hinv, hprogress, _⟩ := hout rfl
          apply ih (Usize.max - s.core.pos.val) _ s hinv haccepted rfl
          have hmax : s.core.pos.val ≤ Usize.max := by scalar_tac
          have hn' : st.core.pos.val < s.core.pos.val := by
            change next.val ≤ s.core.pos.val at hprogress
            omega
          omega
      · rw [reader.read_byte.eof data st.core.pos (by omega)] at haccepted
        simp at haccepted

/-- If every opcode step preserves the invariant, an accepting run from any `State` proves
`Validated`. -/
theorem run.spec (data : Slice U8) (env : metadata.Env)
    (locals : alloc.vec.Vec wasm_types.ValueType) (ctx : code.Context) (index : U32)
    (hsteps : Steps data env locals ctx index) (st : code.BodyState)
    (hi : State data env locals index st) :
    run data env ctx index st ⦃ r => r = .Ok () → Validated data env locals index ⦄ := by
  obtain ⟨r, hr, _⟩ := WP.spec_imp_exists
    (Wasm2.emptyVisitorLoop.total data env ctx.locals ctx.results index st ()
      hi.bounds.size hi.shape.core hi.shape.aligned hi.bounds.ctrls)
  change run data env ctx index st = .ok r at hr
  rw [hr]
  simp only [WP.spec_ok]
  intro hok
  exact run.sound data env locals ctx index hsteps st hi (by simpa [hok] using hr)

/-- If every opcode step preserves the invariant, `code.bodyCore` accepts only `Validated`
bodies. -/
theorem public_spec_of_steps (data : Slice U8) (env : metadata.Env)
    (locals results : alloc.vec.Vec wasm_types.ValueType) (index : U32)
    (hsteps : Steps data env locals ⟨locals, results⟩ index) :
    code.bodyCore data env locals results index ⦃ r =>
      r = .Ok () → Validated data env locals index ⦄ := by
  unfold code.bodyCore
  dsimp only
  split
  · simp
  · rename_i hsize
    step as ⟨idx, hidx⟩
    split
    · simp
    · rename_i hbound
      step as ⟨ft, hft⟩
      have hi : env.types.val[index.val]? = some ft := by
        rw [List.getElem?_eq_getElem (by scalar_tac)]
        simp_all
      step as ⟨r, hr⟩
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok v =>
        cases v
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
          code.push_frame.initial]
        exact run.spec data env locals ⟨locals, results⟩ index hsteps
          (initial index) (State.start data env locals index ft hi (by scalar_tac))

end Itasca.Wasm2

end
