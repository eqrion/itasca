import Itasca.Wasm2.Totality
import Itasca.Wasm2.Execution

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
def Steps (data : Slice U8) (env : metadata.Env) (profile : ValidationProfile)
    (locals : alloc.vec.Vec wasm_types.ValueType) (ctx : code.Context) (index : U32) : Prop :=
  ∀ st (p : Pending data env profile locals index st),
    step st data env profile ctx index (data.val[p.start.val]'p.inbounds) ⦃ r =>
      r.1 = .Ok () → p.After r.2 ⦄

/-- Each successful iteration extends the independent syntax and typing
invariant. Its strictly increasing cursor justifies the whole-body induction. -/
theorem run.sound (data : Slice U8) (env : metadata.Env) (profile : ValidationProfile)
    (locals : alloc.vec.Vec wasm_types.ValueType) (ctx : code.Context) (index : U32)
    (hsteps : Steps data env profile locals ctx index) (st : code.BodyState)
    (hi : State data env profile locals index st)
    (haccepted : run data env profile ctx index st = .ok (.Ok ())) :
    Validated profile data env locals index := by
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
        obtain ⟨rc, hrc, hop⟩ := WP.spec_imp_exists
          (code.check_opcode.spec profile (data.val[st.core.pos.val]'hp))
        cases rc with
        | Err e => simp [hrc] at haccepted
        | Ok u =>
        cases u
        obtain ⟨p, hstart⟩ := hi.pending hc hp (hop rfl) next hn
        obtain ⟨⟨result, s⟩, hs, hout⟩ := WP.spec_imp_exists (hsteps _ p)
        simp only [hstart] at hs
        simp only [bind_ok, hrc, hs] at haccepted
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
theorem run.spec (data : Slice U8) (env : metadata.Env) (profile : ValidationProfile)
    (locals : alloc.vec.Vec wasm_types.ValueType) (ctx : code.Context) (index : U32)
    (hsteps : Steps data env profile locals ctx index) (st : code.BodyState)
    (hi : State data env profile locals index st) :
    run data env profile ctx index st ⦃ r => r = .Ok () → Validated profile data env locals index ⦄ := by
  obtain ⟨r, hr, _⟩ := WP.spec_imp_exists
    (Wasm2.emptyVisitorLoop.total data env profile ctx.locals ctx.results index st ()
      hi.bounds.size hi.shape.core hi.shape.aligned hi.bounds.ctrls)
  change run data env profile ctx index st = .ok r at hr
  rw [hr]
  simp only [WP.spec_ok]
  intro hok
  exact run.sound data env profile locals ctx index hsteps st hi (by simpa [hok] using hr)

/-- If every opcode step preserves the invariant, `code.bodyCore` accepts only `Validated`
bodies. -/
theorem public_spec_of_steps (data : Slice U8) (env : metadata.Env) (profile : ValidationProfile)
    (locals results : alloc.vec.Vec wasm_types.ValueType) (index : U32)
    (hsteps : Steps data env profile locals ⟨locals, results⟩ index) :
    code.bodyCore data env locals results index profile ⦃ r =>
      r = .Ok () → Validated profile data env locals index ⦄ := by
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
        exact run.spec data env profile locals ⟨locals, results⟩ index hsteps
          (initial index) (State.start data env profile locals index ft hi (by scalar_tac))

end Itasca.Wasm2
