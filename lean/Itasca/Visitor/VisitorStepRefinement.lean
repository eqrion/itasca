import Itasca.Support.Result
import Itasca.Visitor.OpDispatch
import Itasca.Visitor.VisitorTableRefinement
import Itasca.Visitor.VisitorLeafDispatch
import Itasca.Visitor.VisitorControlDispatch

open Aeneas Aeneas.Std



namespace Itasca

open VisitorTrace

/-- Branch-table refinement includes every internal label hook and its final hook. -/
theorem code.step_br_table.refines {V W : Type}
    (visitor : code.OpVisitor V) (replacement : code.OpVisitor W)
    (related : V → W → Prop) (hrefines : Refines visitor replacement related)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (v : V) (w : W) (hrelated : related v w)
    (res : core.result.Result Unit error.OpError) (st' : code.OpIterState) (v' : V)
    (h : code.step visitor st data env ctx code.OP_BR_TABLE v = .ok (res, st', v')) :
    ∃ w', code.step replacement st data env ctx code.OP_BR_TABLE w =
      .ok (res, st', w') ∧ related v' w' := by
  rw [code.step_br_table.dispatch] at h ⊢
  obtain ⟨⟨args, s, v1⟩, hr, hh⟩ := ResultFacts.bind_ok_inv _ _ _ h
  obtain ⟨w1, hw, hr1⟩ := code.read_br_table.refines visitor replacement related hrefines
    st data v w hrelated args s v1 hr
  rw [hw]
  simp only [bind_ok]
  exact CoreVisitor.run.refines (.ok (args, s)) visitor replacement related hrefines
    (fun st a => .op st (.br_table a.1 (Control.resultView a.2))) v1 w1 hr1 res st' v' hh

/-- Hook refinement preserves every ordinary result of the actual full dispatcher,
with identical validator state, including rejection and malformed instructions. -/
theorem code.step.refines {V W : Type}
    (visitor : code.OpVisitor V) (replacement : code.OpVisitor W)
    (related : V → W → Prop) (hrefines : Refines visitor replacement related)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (opcode : U8) (v : V) (w : W) (hrelated : related v w)
    (res : core.result.Result Unit error.OpError) (st' : code.OpIterState) (v' : V)
    (h : code.step visitor st data env ctx opcode v = .ok (res, st', v')) :
    ∃ w', code.step replacement st data env ctx opcode w =
      .ok (res, st', w') ∧ related v' w' := by
  cases hn : Numeric.opcodeMeaning opcode with
  | some operation =>
    obtain ⟨hook, hhook, _, _⟩ := NumericHook.of_meaning hn
    rw [dispatch_numeric visitor st data env ctx v opcode operation hook hn hhook] at h
    rw [dispatch_numeric replacement st data env ctx w opcode operation hook hn hhook]
    exact CoreVisitor.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
  | none =>
    cases hm : MemoryMeaning.opcodeMeaning opcode with
    | some operation =>
      obtain ⟨hook, hhook, _, _⟩ := MemoryHook.of_meaning hm
      rw [dispatch_memory visitor st data env ctx v opcode operation hook hm hhook] at h
      rw [dispatch_memory replacement st data env ctx w opcode operation hook hm hhook]
      exact CoreVisitor.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
    | none =>
      by_cases h_nop : opcode = code.OP_NOP
      · subst opcode
        rw [dispatch_nop visitor st data env ctx v] at h
        rw [dispatch_nop replacement st data env ctx w]
        exact CoreVisitor.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
      by_cases h_unreachable : opcode = code.OP_UNREACHABLE
      · subst opcode
        rw [dispatch_unreachable visitor st data env ctx v] at h
        rw [dispatch_unreachable replacement st data env ctx w]
        exact CoreVisitor.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
      by_cases h_i32_const : opcode = code.OP_I32_CONST
      · subst opcode
        rw [dispatch_i32_const visitor st data env ctx v] at h
        rw [dispatch_i32_const replacement st data env ctx w]
        exact CoreVisitor.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
      by_cases h_i64_const : opcode = code.OP_I64_CONST
      · subst opcode
        rw [dispatch_i64_const visitor st data env ctx v] at h
        rw [dispatch_i64_const replacement st data env ctx w]
        exact CoreVisitor.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
      by_cases h_f32_const : opcode = code.OP_F32_CONST
      · subst opcode
        rw [dispatch_f32_const visitor st data env ctx v] at h
        rw [dispatch_f32_const replacement st data env ctx w]
        exact CoreVisitor.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
      by_cases h_f64_const : opcode = code.OP_F64_CONST
      · subst opcode
        rw [dispatch_f64_const visitor st data env ctx v] at h
        rw [dispatch_f64_const replacement st data env ctx w]
        exact CoreVisitor.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
      by_cases h_drop : opcode = code.OP_DROP
      · subst opcode
        rw [dispatch_drop visitor st data env ctx v] at h
        rw [dispatch_drop replacement st data env ctx w]
        exact CoreVisitor.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
      by_cases h_select : opcode = code.OP_SELECT
      · subst opcode
        rw [dispatch_select visitor st data env ctx v] at h
        rw [dispatch_select replacement st data env ctx w]
        exact CoreVisitor.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
      by_cases h_block : opcode = code.OP_BLOCK
      · subst opcode
        rw [dispatch_block visitor st data env ctx v] at h
        rw [dispatch_block replacement st data env ctx w]
        exact CoreVisitor.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
      by_cases h_loop : opcode = code.OP_LOOP
      · subst opcode
        rw [dispatch_loop visitor st data env ctx v] at h
        rw [dispatch_loop replacement st data env ctx w]
        exact CoreVisitor.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
      by_cases h_if : opcode = code.OP_IF
      · subst opcode
        rw [dispatch_if visitor st data env ctx v] at h
        rw [dispatch_if replacement st data env ctx w]
        exact CoreVisitor.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
      by_cases h_else : opcode = code.OP_ELSE
      · subst opcode
        rw [dispatch_else visitor st data env ctx v] at h
        rw [dispatch_else replacement st data env ctx w]
        exact CoreVisitor.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
      by_cases h_end : opcode = code.OP_END
      · subst opcode
        rw [dispatch_end visitor st data env ctx v] at h
        rw [dispatch_end replacement st data env ctx w]
        exact CoreVisitor.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
      by_cases h_br : opcode = code.OP_BR
      · subst opcode
        rw [dispatch_br visitor st data env ctx v] at h
        rw [dispatch_br replacement st data env ctx w]
        exact CoreVisitor.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
      by_cases h_br_if : opcode = code.OP_BR_IF
      · subst opcode
        rw [dispatch_br_if visitor st data env ctx v] at h
        rw [dispatch_br_if replacement st data env ctx w]
        exact CoreVisitor.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
      by_cases h_br_table : opcode = code.OP_BR_TABLE
      · subst opcode
        exact code.step_br_table.refines visitor replacement related hrefines st data env ctx v w hrelated res st' v' h
      by_cases h_return : opcode = code.OP_RETURN
      · subst opcode
        rw [dispatch_return visitor st data env ctx v] at h
        rw [dispatch_return replacement st data env ctx w]
        exact CoreVisitor.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
      by_cases h_call : opcode = code.OP_CALL
      · subst opcode
        rw [dispatch_call visitor st data env ctx v] at h
        rw [dispatch_call replacement st data env ctx w]
        exact CoreVisitor.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
      by_cases h_call_indirect : opcode = code.OP_CALL_INDIRECT
      · subst opcode
        rw [dispatch_call_indirect visitor st data env ctx v] at h
        rw [dispatch_call_indirect replacement st data env ctx w]
        exact CoreVisitor.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
      by_cases h_local_get : opcode = code.OP_LOCAL_GET
      · subst opcode
        rw [dispatch_local_get visitor st data env ctx v] at h
        rw [dispatch_local_get replacement st data env ctx w]
        exact CoreVisitor.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
      by_cases h_local_set : opcode = code.OP_LOCAL_SET
      · subst opcode
        rw [dispatch_local_set visitor st data env ctx v] at h
        rw [dispatch_local_set replacement st data env ctx w]
        exact CoreVisitor.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
      by_cases h_local_tee : opcode = code.OP_LOCAL_TEE
      · subst opcode
        rw [dispatch_local_tee visitor st data env ctx v] at h
        rw [dispatch_local_tee replacement st data env ctx w]
        exact CoreVisitor.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
      by_cases h_global_get : opcode = code.OP_GLOBAL_GET
      · subst opcode
        rw [dispatch_global_get visitor st data env ctx v] at h
        rw [dispatch_global_get replacement st data env ctx w]
        exact CoreVisitor.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
      by_cases h_global_set : opcode = code.OP_GLOBAL_SET
      · subst opcode
        rw [dispatch_global_set visitor st data env ctx v] at h
        rw [dispatch_global_set replacement st data env ctx w]
        exact CoreVisitor.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
      by_cases h_memory_size : opcode = code.OP_MEMORY_SIZE
      · subst opcode
        rw [dispatch_memory_size visitor st data env ctx v] at h
        rw [dispatch_memory_size replacement st data env ctx w]
        exact CoreVisitor.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
      by_cases h_memory_grow : opcode = code.OP_MEMORY_GROW
      · subst opcode
        rw [dispatch_memory_grow visitor st data env ctx v] at h
        rw [dispatch_memory_grow replacement st data env ctx w]
        exact CoreVisitor.run.refines _ visitor replacement related hrefines _ v w hrelated res st' v' h
      have heqval (a b : U8) : a = b ↔ a.val = b.val :=
        ⟨fun h => congrArg UScalar.val h, UScalar.eq_of_val_eq⟩
      have hdispatch {W : Type} (hooks : code.OpVisitor W) (w : W) :
          code.step hooks st data env ctx opcode w = code.step_memory hooks st data env opcode w := by
        unfold code.step
        split <;> simp_all [global_simps, U8.ofNat, UScalar.ofNat, UScalar.ofNatCore]
      rw [hdispatch visitor v] at h
      rw [hdispatch replacement w]
      rw [OpDispatch.memory_fallback visitor st data env opcode v hm h_memory_size h_memory_grow,
        code.step_numeric.unrecognized visitor st opcode v hn] at h
      rw [OpDispatch.memory_fallback replacement st data env opcode w hm h_memory_size h_memory_grow,
        code.step_numeric.unrecognized replacement st opcode w hn]
      simp only [Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨w, rfl, hrelated⟩

/-- Instrumentation preserves validator success and every ordinary validation error. -/
theorem code.step.instrument_forward {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (opcode : U8) (v : V) (log : List Observation)
    (res : core.result.Result Unit error.OpError) (st' : code.OpIterState) (v' : V)
    (h : code.step visitor st data env ctx opcode v = .ok (res, st', v')) :
    ∃ added, code.step (instrument visitor) st data env ctx opcode (v, log) =
      .ok (res, st', (v', log ++ added)) := by
  obtain ⟨⟨w, log'⟩, hw, heq, added, hlog⟩ := code.step.refines visitor (instrument visitor)
    _ (instrument_refines visitor log) st data env ctx opcode v (v, log)
    ⟨rfl, [], by simp⟩ res st' v' h
  dsimp only at heq hlog
  subst w
  subst log'
  exact ⟨added, hw⟩

/-- Erasing the recording wrapper preserves errors as well as successful executions. -/
theorem code.step.instrument_backward {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (opcode : U8) (v : V) (log : List Observation)
    (res : core.result.Result Unit error.OpError) (st' : code.OpIterState) (v' : V)
    (log' : List Observation)
    (h : code.step (instrument visitor) st data env ctx opcode (v, log) =
      .ok (res, st', (v', log'))) :
    code.step visitor st data env ctx opcode v = .ok (res, st', v') := by
  obtain ⟨w, hw, heq⟩ := code.step.refines (instrument visitor) visitor
    _ (instrument_refines_back visitor) st data env ctx opcode (v, log) v rfl
    res st' (v', log') h
  simpa only [← heq] using hw

end Itasca
