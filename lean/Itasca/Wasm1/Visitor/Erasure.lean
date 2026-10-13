import Itasca.Support.Result
import Itasca.Visitor.StepErasure
import Itasca.Wasm1.Loop
import Itasca.Handler.RawControl
import Itasca.Wasm1.Soundness

open Aeneas Aeneas.Std

namespace Itasca

/-- Byte progress of the empty visitor supplies induction even when the original visitor is not total. -/
theorem code.validate_body_with_loop.accepted_erase_of_contract {V : Type}
    (visitor : code.OpVisitor V) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (inv : code.OpIterState → Prop)
    (hstep : Wasm1.Loop.StepContract code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      data env ctx (fun _ st => inv st))
    (herase : ∀ st st' opcode v v', code.step visitor st data env ctx opcode v = .ok (.Ok (), st', v') →
      code.step code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor st data env ctx opcode () = .ok (.Ok (), st', ()))
    (st : code.OpIterState) (v v' : V) (hi : inv st)
    (h : code.validate_body_with_loop visitor data env ctx.locals ctx.results v st = .ok (.Ok (), v')) :
    code.validate_body_with_loop code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      data env ctx.locals ctx.results () st = .ok (.Ok (), ()) := by
  generalize hn : data.length - st.pos.val = n
  induction n using Nat.strong_induction_on generalizing st v with
  | h n ih =>
    unfold code.validate_body_with_loop at h ⊢
    rw [loop] at h ⊢
    simp only [code.validate_body_with_loop.body, code.control_stack_empty,
      alloc.vec.Vec.is_empty, bind_ok] at h ⊢
    by_cases hc : st.ctrls.val = []
    · simp only [hc, List.isEmpty_nil, ↓reduceIte] at h ⊢
      by_cases hp : st.pos = Slice.len data
      · simp [hp]
      · simp [hp] at h
    · have hempty : st.ctrls.val.isEmpty = false := by simpa using hc
      simp only [hempty, Bool.false_eq_true, ↓reduceIte] at h ⊢
      by_cases hp : st.pos.val < data.length
      · obtain ⟨next, hr, hnext⟩ := code.read_op_success st data hp
        rw [hr] at h ⊢
        simp [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_assoc] at h ⊢
        obtain ⟨⟨res, out, w⟩, hs, htail⟩ := ResultFacts.bind_ok_inv _ _ _ h
        cases res with
        | Err e =>
          simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at htail
        | Ok u =>
          cases u
          have hdefault := herase {st with pos := next} out data.val[st.pos.val] v w hs
          have hprogress := hstep st () hi hc hp next hnext
          rw [hdefault, WP.spec_ok] at hprogress
          obtain ⟨hi', hge, hbound⟩ := hprogress rfl
          dsimp only at hi' hge hbound
          have hmeasure : data.length - out.pos.val < n := by omega
          simp [hdefault]
          simp at htail
          have htail' : code.validate_body_with_loop visitor data env ctx.locals ctx.results w out =
              .ok (.Ok (), v') := by
            simpa [code.validate_body_with_loop, code.validate_body_with_loop.body,
              code.control_stack_empty, alloc.vec.Vec.is_empty,
              core.result.Result.Insts.CoreOpsTry.branch] using htail
          simpa [code.validate_body_with_loop, code.validate_body_with_loop.body,
            code.control_stack_empty, alloc.vec.Vec.is_empty,
            core.result.Result.Insts.CoreOpsTry.branch] using
              ih (data.length - out.pos.val) hmeasure out w hi' htail' rfl
      · rw [code.read_op.eof st data (by omega)] at h
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h

/-- Initialization and the size guard preserve acceptance when callbacks are erased. -/
theorem code.validate_body_with.accepted_erase_of_contract {V : Type}
    (visitor : code.OpVisitor V) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (inv : code.OpIterState → Prop)
    (hstep : Wasm1.Loop.StepContract code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      data env ctx (fun _ st => inv st))
    (herase : ∀ st st' opcode v v', code.step visitor st data env ctx opcode v = .ok (.Ok (), st', v') →
      code.step code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor st data env ctx opcode () = .ok (.Ok (), st', ()))
    (hinit : data.length ≤ limits.MAX_FUNCTION_BYTES.val →
      inv (Wasm1.Loop.initial (Wasm1.Loop.initialBlockType ctx.results.val)))
    (v v' : V)
    (h : code.validate_body_with visitor data env ctx v = .ok (.Ok (), v')) :
    code.validate_body_with code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor data env ctx () =
      .ok (.Ok (), ()) := by
  simp only [code.validate_body_with.eq_model] at h ⊢
  unfold code.validate_body_with_model at h ⊢
  dsimp only at h ⊢
  by_cases hsize : Slice.len data > limits.MAX_FUNCTION_BYTES
  · simp [hsize] at h
  · rw [if_neg hsize, code.start_function.raw_spec] at h ⊢
    simp only [bind_ok] at h ⊢
    apply code.validate_body_with_loop.accepted_erase_of_contract visitor data env ctx
      inv hstep herase _ v v' _ h
    simpa [alloc.vec.Vec.deref] using hinit (by scalar_tac)

/-- Any accepted visitor execution is accepted by the public validator, without assumptions on the visitor. -/
theorem code.validate_body_with.accepted_erase {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (v v' : V)
    (haccepted : code.validate_body_with visitor data env ctx v = .ok (.Ok (), v')) :
    code.validate_body data env ctx = .ok (.Ok ()) := by
  let bt := Wasm1.Loop.initialBlockType ctx.results.val
  have hsteps := Wasm1.steps code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
    FullVisitor.empty_total data env ctx bt
  have hempty := code.validate_body_with.accepted_erase_of_contract visitor data env ctx
    (Wasm1.State data env ctx bt)
    (hsteps.contract code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor data env ctx bt)
    (fun st st' opcode v v' h => code.step.accepted_erase visitor st st' data env ctx opcode v v' h)
    (fun hsize => Wasm1.State.start data env ctx bt hsize) v v' haccepted
  simp [code.validate_body, hempty]

/-- Soundness of accepted bodies needs no visitor totality premise and no prevalidated-byte profile. -/
theorem code.validate_body_with.wasm_sound {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (bt : code.BlockType)
    (hresults : ctx.results.val = Control.results bt) (v v' : V)
    (haccepted : code.validate_body_with visitor data env ctx v = .ok (.Ok (), v')) :
    Wasm1.Validated data env ctx bt :=
  code.validate_body.wasm_sound data env ctx bt hresults
    (code.validate_body_with.accepted_erase visitor data env ctx v v' haccepted)

end Itasca
