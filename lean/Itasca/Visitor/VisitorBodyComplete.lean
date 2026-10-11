import Itasca.Support.Result
import Itasca.Visitor.VisitorComplete
import Itasca.Visitor.VisitorBodyErasure
import Itasca.Body.WasmComplete

open Aeneas Aeneas.Std

namespace Itasca

private theorem visiting_loop_step {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (st decoded out : code.OpIterState) (opcode : U8) (v w : V)
    (hc : st.ctrls.val ≠ [])
    (hr : code.read_op st data = .ok (.Ok opcode, decoded))
    (hs : code.step visitor decoded data env ctx opcode v = .ok (.Ok (), out, w)) :
    code.validate_body_with_loop visitor data env ctx.locals ctx.results v st =
      code.validate_body_with_loop visitor data env ctx.locals ctx.results w out := by
  have hempty : st.ctrls.val.isEmpty = false := by simpa using hc
  unfold code.validate_body_with_loop
  conv_lhs => rw [loop]
  simp [code.validate_body_with_loop.body, code.control_stack_empty,
    alloc.vec.Vec.is_empty, hempty, hr, hs, core.result.Result.Insts.CoreOpsTry.branch]

/-- Successful empty-visitor iterations supply a decreasing byte measure.
Accepting hooks can change their own state but preserve each validator state. -/
theorem code.validate_body_with_loop.accepted_lift_of_contract {V : Type}
    (visitor : code.OpVisitor V) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (inv : code.OpIterState → Prop)
    (hstep : Body.StepContract code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      data env ctx (fun _ st => inv st))
    (hlift : ∀ st st' opcode v,
      code.step code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor st data env ctx opcode () =
        .ok (.Ok (), st', ()) →
      ∃ v', code.step visitor st data env ctx opcode v = .ok (.Ok (), st', v'))
    (st : code.OpIterState) (v : V) (hi : inv st)
    (h : code.validate_body_with_loop code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      data env ctx.locals ctx.results () st = .ok (.Ok (), ())) :
    ∃ v', code.validate_body_with_loop visitor data env ctx.locals ctx.results v st =
      .ok (.Ok (), v') := by
  generalize hn : data.length - st.pos.val = n
  induction n using Nat.strong_induction_on generalizing st v with
  | h n ih =>
    have horiginal := h
    unfold code.validate_body_with_loop at h
    rw [loop] at h
    simp only [code.validate_body_with_loop.body, code.control_stack_empty,
      alloc.vec.Vec.is_empty, bind_ok] at h
    by_cases hc : st.ctrls.val = []
    · simp only [hc, List.isEmpty_nil, ↓reduceIte] at h
      by_cases hp : st.pos = Slice.len data
      · refine ⟨v, ?_⟩
        unfold code.validate_body_with_loop
        rw [loop]
        simp [code.validate_body_with_loop.body, code.control_stack_empty,
          alloc.vec.Vec.is_empty, hc, hp]
      · simp [hp] at h
    · have hempty : st.ctrls.val.isEmpty = false := by simpa using hc
      simp only [hempty, Bool.false_eq_true, ↓reduceIte] at h
      by_cases hp : st.pos.val < data.length
      · obtain ⟨next, hr, hnext⟩ := code.read_op_success st data hp
        rw [hr] at h
        simp [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_assoc] at h
        obtain ⟨⟨res, out, w⟩, hs, htail⟩ := ResultFacts.bind_ok_inv _ _ _ h
        cases w
        cases res with
        | Err e =>
          simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at htail
        | Ok u =>
          cases u
          have hprogress := hstep st () hi hc hp next hnext
          rw [hs, WP.spec_ok] at hprogress
          obtain ⟨hi', hge, hbound⟩ := hprogress rfl
          dsimp only at hi' hge hbound
          have hmeasure : data.length - out.pos.val < n := by omega
          have htail' : code.validate_body_with_loop code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
              data env ctx.locals ctx.results () out = .ok (.Ok (), ()) := by
            rw [← visiting_loop_step _ data env ctx st {st with pos := next} out _ () () hc hr hs]
            exact horiginal
          obtain ⟨w, hvisit⟩ := hlift {st with pos := next} out data.val[st.pos.val] v hs
          obtain ⟨v', hrest⟩ := ih (data.length - out.pos.val) hmeasure out w hi' htail' rfl
          exact ⟨v', (visiting_loop_step visitor data env ctx st {st with pos := next}
            out _ v w hc hr hvisit).trans hrest⟩
      · rw [code.read_op.eof st data (by omega)] at h
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h

/-- The exact public size guard and initialization retain successful execution
when each accepted empty-visitor step lifts to the chosen visitor. -/
theorem code.validate_body_with.accepted_lift_of_contract {V : Type}
    (visitor : code.OpVisitor V) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (inv : code.OpIterState → Prop)
    (hstep : Body.StepContract code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      data env ctx (fun _ st => inv st))
    (hlift : ∀ st st' opcode v,
      code.step code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor st data env ctx opcode () =
        .ok (.Ok (), st', ()) →
      ∃ v', code.step visitor st data env ctx opcode v = .ok (.Ok (), st', v'))
    (hinit : data.length ≤ limits.MAX_FUNCTION_BYTES.val →
      inv (Body.initial (Body.initialBlockType ctx.results.val)))
    (v : V)
    (h : code.validate_body_with code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      data env ctx () = .ok (.Ok (), ())) :
    ∃ v', code.validate_body_with visitor data env ctx v = .ok (.Ok (), v') := by
  unfold code.validate_body_with at h ⊢
  dsimp only at h ⊢
  by_cases hsize : Slice.len data > limits.MAX_FUNCTION_BYTES
  · simp [hsize] at h
  · rw [if_neg hsize, code.start_function.raw_spec] at h ⊢
    simp only [bind_ok] at h ⊢
    apply code.validate_body_with_loop.accepted_lift_of_contract visitor data env ctx
      inv hstep hlift _ v _ h
    simpa [alloc.vec.Vec.deref] using hinit (by scalar_tac)

/-- Accepting hooks preserve every successful public body validation. No
valid-input, result-shape, or environment restriction is needed for transfer. -/
theorem code.validate_body_with.accepted_lift {V : Type} (visitor : code.OpVisitor V)
    (haccept : FullVisitor.Accepts visitor) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (v : V)
    (haccepted : code.validate_body data env ctx = .ok (.Ok ())) :
    ∃ v', code.validate_body_with visitor data env ctx v = .ok (.Ok (), v') := by
  obtain ⟨⟨result, w⟩, hrun⟩ := code.validate_body_with.wasm_total
    code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor FullVisitor.empty_total data env ctx ()
  cases w
  have hok : result = .Ok () := by simpa [code.validate_body, hrun] using haccepted
  subst result
  let bt := Body.initialBlockType ctx.results.val
  have hsteps := Wasm.steps code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
    FullVisitor.empty_total data env ctx bt
  exact code.validate_body_with.accepted_lift_of_contract visitor data env ctx
    (Wasm.State data env ctx bt)
    (hsteps.contract code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor data env ctx bt)
    (fun st st' opcode v h => code.step.accepted_lift visitor haccept st st' data env ctx opcode v h)
    (fun hsize => Wasm.State.start data env ctx bt hsize) v hrun

/-- Independent Wasm 1.0 byte encoding and generated declarative typing
force public visiting validation to accept when every hook accepts. -/
theorem code.validate_body_with.wasm_complete {V : Type} (visitor : code.OpVisitor V)
    (haccept : FullVisitor.Accepts visitor) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (bt : code.BlockType) (henv : Wasm1.Environment env)
    (hresults : ctx.results.val = Control.results bt)
    (hsize : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (hbody : Wasm1.Body data env ctx bt) (v : V) :
    ∃ v', code.validate_body_with visitor data env ctx v = .ok (.Ok (), v') :=
  code.validate_body_with.accepted_lift visitor haccept data env ctx v
    (code.validate_body.wasm_complete data env ctx bt henv hresults hsize hbody)

end Itasca
