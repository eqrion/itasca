import Exec.Code.Local.Source.EntryCallbacks
namespace Exec.Code
open Aeneas Aeneas.Std
open Itasca

/-- Successful instruction execution retains the validator's typed source
zipper at every actual compiler step, not just the callback's byte position. -/
inductive TypedRunWasm1 {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (bt : code.BlockType) :
    code.OpIterState → V → V → Prop where
  | done {st v} (typed : Wasm1.State data env ctx bt st)
      (closed : st.ctrls.val = []) (finished : st.pos = Slice.len data) :
      TypedRunWasm1 visitor data env ctx bt st v v
  | step {st v next out middle final}
      (typed : Wasm1.State data env ctx bt st)
      (pending : Wasm1.Pending data env ctx bt {st with pos := next})
      (start : pending.start = st.pos)
      (advance : next.val = st.pos.val + 1)
      (called : code.step visitor {st with pos := next} data env ctx
        (data.val[pending.start.val]'pending.inbounds) v = .ok (.Ok (), out, middle))
      (rest : TypedRunWasm1 visitor data env ctx bt out middle final) :
      TypedRunWasm1 visitor data env ctx bt st v final

theorem typed_loop_wasm1 {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (bt : code.BlockType)
    (st : code.OpIterState) (before after : V) (typed : Wasm1.State data env ctx bt st)
    (accepted : code.validate_body_with_loop visitor data env ctx.locals ctx.results before st =
      .ok (.Ok (), after)) : TypedRunWasm1 visitor data env ctx bt st before after := by
  generalize hn : data.length - st.pos.val = n
  induction n using Nat.strong_induction_on generalizing st before with
  | h n ih =>
    unfold code.validate_body_with_loop at accepted
    rw [loop] at accepted
    simp only [code.validate_body_with_loop.body, code.control_stack_empty,
      alloc.vec.Vec.is_empty, bind_ok] at accepted
    by_cases closed : st.ctrls.val = []
    · simp only [closed, List.isEmpty_nil, ↓reduceIte] at accepted
      by_cases finished : st.pos = Slice.len data
      · simp [finished] at accepted
        subst after
        exact .done typed closed finished
      · simp [finished] at accepted
    · have nonempty : st.ctrls.val.isEmpty = false := by simpa using closed
      simp only [nonempty, Bool.false_eq_true, ↓reduceIte] at accepted
      by_cases inbounds : st.pos.val < data.length
      · obtain ⟨next, read, advance⟩ := code.read_op_success st data inbounds
        rw [read] at accepted
        simp [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_assoc] at accepted
        obtain ⟨⟨result, out, middle⟩, called, tail⟩ := ResultFacts.bind_ok_inv _ _ _ accepted
        cases result with
        | Err error =>
          simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at tail
        | Ok acceptedUnit =>
          cases acceptedUnit
          obtain ⟨pending, start⟩ := typed.pending closed inbounds next advance
          have erased := code.step.accepted_erase visitor {st with pos := next} out
            data env ctx data.val[st.pos.val] before middle called
          have progress := (Wasm1.steps code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
            FullVisitor.empty_total data env ctx bt).contract
            code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor data env ctx bt st () typed closed inbounds next advance
          rw [erased, WP.spec_ok] at progress
          obtain ⟨outTyped, greater, bound⟩ := progress rfl
          dsimp only at outTyped greater bound
          have smaller : data.length - out.pos.val < n := by omega
          simp at tail
          have tail' : code.validate_body_with_loop visitor data env ctx.locals ctx.results middle out =
              .ok (.Ok (), after) := by
            simpa [code.validate_body_with_loop, code.validate_body_with_loop.body,
              code.control_stack_empty, alloc.vec.Vec.is_empty,
              core.result.Result.Insts.CoreOpsTry.branch] using tail
          exact .step typed pending start advance (by simpa [start] using called)
            (ih _ smaller out middle outTyped tail' rfl)
      · rw [code.read_op.eof st data (by omega)] at accepted
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted

theorem typed_body_wasm1 {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (before after : V)
    (accepted : code.validate_body_with visitor data env ctx before = .ok (.Ok (), after)) :
    TypedRunWasm1 visitor data env ctx (Wasm1.Loop.initialBlockType ctx.results.val)
      (Wasm1.Loop.initial (Wasm1.Loop.initialBlockType ctx.results.val)) before after := by
  simp only [code.validate_body_with.eq_model] at accepted
  unfold code.validate_body_with_model at accepted
  dsimp only at accepted
  by_cases size : Slice.len data > limits.MAX_FUNCTION_BYTES
  · simp [size] at accepted
  · rw [if_neg size, code.start_function.raw_spec] at accepted
    simp only [bind_ok] at accepted
    exact typed_loop_wasm1 visitor data env ctx _ _ before after
      (Wasm1.State.start data env ctx _ (by scalar_tac))
      (by simpa [alloc.vec.Vec.deref] using accepted)
end Exec.Code
