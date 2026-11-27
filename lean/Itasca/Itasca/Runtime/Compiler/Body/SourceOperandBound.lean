import Itasca.Runtime.Compiler.Body.Reader.Replay.SingleCallback
import Itasca.Runtime.Compiler.Body.CapacityTrace
import Itasca.Runtime.Compiler.Local.Source.TypedSteps
import Itasca.Runtime.Compiler.Local.IndependentBodyDemand

/-!
# Source-size bounds for compiler observations

Reference callback logs are proof tools. A successful ordinary instruction
reports its final operand stack; branch-table labels observe a stack no larger
than the incoming one. Bounded source completeness therefore bounds every
recorded operand stack without putting the reference validator in the public
compilation demand.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace
open Result ControlFlow

private theorem demand_append_op (log : List Observation) (state : code.OpIterState)
    (action : Action) (reply : VisitResult) :
    (observationDemand (log ++ [⟨.op state action, reply⟩])).operands =
      max (observationDemand log).operands state.vals.val.length := by
  induction log with
  | nil => simp only [observationDemand, ObservationDemand.join, eventDemand, List.nil_append, Nat.max_zero, Nat.zero_max, alloc.vec.Vec.length]
  | cons head tail ih =>
    simp only [List.cons_append, observationDemand, ObservationDemand.join] at *
    rw [ih, Nat.max_assoc]

private theorem callback_bound {before after : List Observation} {state : code.OpIterState}
    {action : Action} {bound : Nat}
    (initial : (observationDemand before).operands ≤ bound)
    (size : state.vals.val.length ≤ bound)
    (called : invoke recorder before (.op state action) = .ok (.Ok (), after)) :
    (observationDemand after).operands ≤ bound := by
  have recorded := recorder_records before (.op state action) (.Ok ()) after called
  change after = before ++ [⟨.op state action, .Ok ()⟩] at recorded
  rw [recorded, demand_append_op]
  exact max_le initial size

/-- Label callbacks only read the popped selector stack. The final callback
can shrink it by marking the remaining code unreachable. -/
private theorem table_loop_bound (st : code.BodyState) (data : Slice U8) (env : metadata.Env)
    (shape : Body.Control.Shape st.core) (count i : U32) (arity : Option Usize)
    (indexBound : i.val ≤ count.val) (before after : List Observation)
    (out : code.BodyState) (bound : Nat)
    (size : st.core.vals.val.length ≤ bound)
    (initial : (observationDemand before).operands ≤ bound)
    (run : code.branch_table_with_loop recorder st.core data env before count arity i =
      .ok (.Ok (), out, after)) : (observationDemand after).operands ≤ bound := by
  generalize hn : count.val - i.val = n
  induction n using Nat.strong_induction_on generalizing st i arity before with
  | h n ih =>
    rw [code.branch_table_with_loop.step_eq] at run
    obtain ⟨cf, body, tail⟩ := Computation.bind_ok_inv _ _ _ run
    unfold Body.Visitor.tableBody at body
    obtain ⟨⟨result, next⟩, read, vals, ctrls, _⟩ := WP.spec_imp_exists
      (code.read_label_info.bytes st data (code.BodyState.blocks_length st))
    rw [read] at body
    cases result with
    | Err error =>
      simp only [bind_ok, Std.uncurry, Result.ok.injEq] at body
      subst cf
      simp only [Result.ok.injEq, Prod.mk.injEq, reduceCtorEq, false_and] at tail
    | Ok pair =>
      obtain ⟨depth, types⟩ := pair
      dsimp only at vals ctrls
      have nextShape : Body.Control.Shape next.core :=
        ⟨by simpa only [ctrls] using shape.ordered, by simpa only [ctrls, vals] using shape.bounded⟩
      have nextSize : next.core.vals.val.length ≤ bound := by simpa only [vals] using size
      simp only [bind_ok, Std.uncurry] at body
      by_cases last : i = count
      · simp only [last, bne_self_eq_false, Bool.false_eq_true, if_false] at body
        unfold Body.Visitor.tableRest at body
        obtain ⟨checked, check, body⟩ := Computation.bind_ok_inv _ _ _ body
        cases checked with
        | Err error => simp only [Result.ok.injEq] at body; subst cf; simp only [Result.ok.injEq, Prod.mk.injEq, reduceCtorEq, false_and] at tail
        | Ok nextArity =>
          simp only [↓reduceIte] at body
          obtain ⟨core, marked, body⟩ := Computation.bind_ok_inv _ _ _ body
          have markedSpec := code.mark_unreachable_total next.core nextShape
          rw [marked, WP.spec_ok] at markedSpec
          obtain ⟨⟨reply, log⟩, callback, body⟩ := Computation.bind_ok_inv _ _ _ body
          have callback' : invoke recorder before (.op core (.br_table depth types)) =
              .ok (reply, log) := callback
          have replyEq : reply = .Ok () := by
            have fact := callback'
            simp only [recorder, invoke_of_handler, Result.ok.injEq, Prod.mk.injEq] at fact
            exact fact.1.symm
          subst reply
          simp only [code.visit.accepted, bind_ok, Result.ok.injEq, Std.uncurry] at body
          subst cf
          simp only [Result.ok.injEq, Prod.mk.injEq] at tail
          obtain ⟨_, _, rfl⟩ := tail
          exact callback_bound initial (markedSpec.2.2.2.1.trans nextSize) callback'
      · simp only [bne_iff_ne, if_pos last] at body
        obtain ⟨⟨reply, log⟩, callback, body⟩ := Computation.bind_ok_inv _ _ _ body
        have callback' : invoke recorder before (.op next.core (.br_table_label depth)) =
            .ok (reply, log) := callback
        have replyEq : reply = .Ok () := by
          have fact := callback'
          simp only [recorder, invoke_of_handler, Result.ok.injEq, Prod.mk.injEq] at fact
          exact fact.1.symm
        subst reply
        have logBound := callback_bound initial nextSize callback'
        simp only [code.visit.accepted, bind_ok, Std.uncurry] at body
        unfold Body.Visitor.tableRest at body
        obtain ⟨checked, check, body⟩ := Computation.bind_ok_inv _ _ _ body
        cases checked with
        | Err error => simp only [Result.ok.injEq] at body; subst cf; simp only [Result.ok.injEq, Prod.mk.injEq, reduceCtorEq, false_and] at tail
        | Ok nextArity =>
          simp only [last, if_false] at body
          have less : i.val < count.val := by
            have ne : i.val ≠ count.val := fun eq => last (UScalar.eq_of_val_eq eq)
            omega
          obtain ⟨j, added, value⟩ := WP.spec_imp_exists
            (UScalar.add_spec (x := i) (y := 1#u32) (by scalar_tac))
          simp only [added, bind_ok, Result.ok.injEq] at body
          subst cf
          exact ih (count.val - j.val) (by scalar_tac) next nextShape j nextArity
            (by scalar_tac) log nextSize logBound tail rfl

private theorem table_bound (st out : code.BodyState) (data : Slice U8) (env : metadata.Env)
    (before after : List Observation) (bound : Nat)
    (shape : Body.Control.Shape st.core) (size : st.core.vals.val.length ≤ bound)
    (initial : (observationDemand before).operands ≤ bound)
    (run : code.branch_table_with recorder st data env before = .ok (.Ok (), out, after)) :
    (observationDemand after).operands ≤ bound := by
  obtain ⟨count, first, popped, value, _, pop, loopRun⟩ :=
    code.branch_table_with.accepted_entry recorder st out data env before after run
  have moved : Body.Control.Shape {st.core with pos := first} := ⟨shape.ordered, shape.bounded⟩
  have poppedSpec := code.pop_with_type.total {st.core with pos := first} .I32 moved
  rw [pop, WP.spec_ok] at poppedSpec
  exact table_loop_bound ⟨popped⟩ data env poppedSpec.1 count 0#u32 none
    (by scalar_tac) before after out bound (poppedSpec.2.2.2.1.trans size) initial loopRun

/-- Every observed operand vector is either the final instruction state or a
non-growing branch-table selector stack. -/
private theorem step_operand_bound (st out : code.BodyState) (data : Slice U8)
    (env : metadata.Env) (ctx : code.Context) (index : U32) (opcode : U8)
    (before after : List Observation) (bound : Nat)
    (shape : Body.Control.Shape st.core) (size : st.core.vals.val.length ≤ bound)
    (outSize : out.core.vals.val.length ≤ bound)
    (initial : (observationDemand before).operands ≤ bound)
    (accepted : code.step_body recorder st data env ctx index opcode before = .ok (.Ok (),out,after)) :
    (observationDemand after).operands ≤ bound := by
  by_cases block : opcode = 2#u8
  · rw [block, Body.CallbackTrace.dispatch_block] at accepted
    obtain ⟨arg, _, callback⟩ := Body.CallbackTrace.bodyRun.accepted _ _ _ _ _ _ accepted
    exact callback_bound initial outSize callback
  by_cases loop_ : opcode = 3#u8
  · rw [loop_, Body.CallbackTrace.dispatch_loop] at accepted
    obtain ⟨arg, _, callback⟩ := Body.CallbackTrace.bodyRun.accepted _ _ _ _ _ _ accepted
    exact callback_bound initial outSize callback
  by_cases if_ : opcode = 4#u8
  · rw [if_, Body.CallbackTrace.dispatch_if] at accepted
    obtain ⟨arg, _, callback⟩ := Body.CallbackTrace.bodyRun.accepted _ _ _ _ _ _ accepted
    exact callback_bound initial outSize callback
  by_cases end_ : opcode = 11#u8
  · rw [end_, Body.CallbackTrace.dispatch_end] at accepted
    obtain ⟨arg, _, callback⟩ := Body.CallbackTrace.bodyRun.accepted _ _ _ _ _ _ accepted
    exact callback_bound initial outSize callback
  by_cases table : opcode = 14#u8
  · rw [table, Body.CallbackTrace.dispatch_br_table] at accepted
    exact table_bound st out data env before after bound shape size initial accepted
  obtain ⟨action, _, _, callback⟩ := reader_single_body_callback recorder st out data env ctx index opcode
    before after (by simpa only [global_simps] using And.intro block ⟨loop_, if_, end_, table⟩) accepted
  exact callback_bound initial outSize callback

private theorem bounded_head {data env ctx index st last}
    (run : Body.Completeness.BoundedExecution data env ctx index st last)
    (empty : last.core.vals.val = []) : st.core.vals.val.length ≤ 500 * data.length := by
  cases run with
  | nil => simp only [empty, List.length_nil, Nat.zero_le]
  | cons _ _ _ _ _ bound => exact bound

private theorem typed_operand_bound {data env ctx index st last before after}
    (run : TypedRun recorder data env ctx index st before after)
    (bounded : Body.Completeness.BoundedExecution data env ctx index st last)
    (finished : last.core.pos.val = data.length) (empty : last.core.vals.val = [])
    (initial : (observationDemand before).operands ≤ 500 * data.length) :
    (observationDemand after).operands ≤ 500 * data.length := by
  induction bounded generalizing before after with
  | nil st =>
    cases run with
    | done => exact initial
    | step typed pending start advance called rest =>
      have inside := pending.inbounds
      rw [start] at inside
      omega
  | cons st next last opcode pos bound nonempty read step suffix ih =>
    cases run with
    | done typed closed ended => exact False.elim (nonempty closed)
    | @step _ before cursor out middle after typed pending start advance called rest =>
      have inside : st.core.pos.val < data.length := by simpa only [start] using pending.inbounds
      obtain ⟨reply, read', cursor', rfl, advance'⟩ := WP.spec_imp_exists
        (reader.read_byte.spec data st.core.pos inside)
      have cursorEq : cursor' = cursor := by scalar_tac
      subst cursor'
      have eqs : opcode = data.val[st.core.pos.val] ∧ pos = cursor := by
        simpa using read.symm.trans read'
      have opEq : opcode = data.val[pending.start.val]'pending.inbounds := by
        simpa only [start] using eqs.1
      have posEq := eqs.2
      subst opcode pos
      obtain ⟨emptyVisitorState, erased⟩ := Body.Visitor.step_transfer recorder
        code.DefaultOpVisitor.Insts.ItascaCodeOpVisitor Visitor.empty_accepts
        data env ctx ctx rfl index _ {core := {st.core with pos := cursor}} out before () middle called
      cases emptyVisitorState
      have same := Representation.empty_dispatch_eq nonempty read step erased
      subst out
      have nextBound := step_operand_bound _ next data env ctx index _ before middle
        (500 * data.length) pending.opened.shape.core bound (bounded_head suffix empty) initial called
      exact ih rest finished empty nextBound

/-- Source validity supplies the reference execution, while source byte size
bounds all callback operand stacks. The chosen log is only an internal device
for composing the compiler callbacks' availability proofs. -/
theorem independentBodyDemand.byte_bound (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) (limits : CodeEntry.EnvironmentWithinLimits env)
    (size : data.length ≤ Itasca.limits.MAX_FUNCTION_BYTES.val)
    (valid : Body.Validated data env ctx.locals index) :
    (independentBodyDemand data env ctx index).operands ≤ 500 * data.length := by
  have accepted := independentBodyLog.of_valid data env ctx index limits size valid
  have typed := typed_body recorder data env ctx index [] _ accepted
  obtain ⟨last, bounded, _, finished, empty⟩ := Body.Completeness.bounded_execution
    data env ctx.locals ctx.results index limits size valid
  exact typed_operand_bound typed bounded finished empty (by simp only [observationDemand, Nat.zero_le])

end Itasca.Compiler
