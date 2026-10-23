import Itasca.Support.Result
import Itasca.Visitor.Dispatch
import Itasca.Visitor.Accepts
import Itasca.Visitor.StepErasure

/-!
# Lifting an accepted step to an accepting visitor

The converse of `Visitor/StepErasure`. `code.step.accepted_lift` shows that if `code.step` accepts
with `code.EmptyOpVisitor`, it also accepts, at the same validator state, with any visitor
satisfying `FullVisitor.Accepts`. The `br_table` label loop is lifted in
`code.read_table_labels_loop.accepted_lift`. Covers the Wasm 1.0 step `code.step`.
-/

open Aeneas Aeneas.Std

namespace Itasca.CoreVisitor

/-- An accepted `CoreVisitor.run` can be replayed with any hook that accepts the reader output. -/
theorem run.accepted_lift {A V W : Type}
    (read : Result (core.result.Result A error.OpError × code.OpIterState))
    (hook : V → code.OpIterState → A → Result (core.result.Result Unit error.VisitError × V))
    (replacement : W → code.OpIterState → A → Result (core.result.Result Unit error.VisitError × W))
    (v : V) (w : W) (st' : code.OpIterState) (v' : V)
    (h : run read hook v = .ok (.Ok (), st', v'))
    (haccept : ∀ a, ∃ w', replacement w st' a = .ok (.Ok (), w')) :
    ∃ w', run read replacement w = .ok (.Ok (), st', w') := by
  obtain ⟨a, hr, _⟩ := run.accepted read hook v st' v' h
  obtain ⟨w', hw⟩ := haccept a
  exact ⟨w', by simp [run, hr, hw, code.visit, core.result.Result.Insts.CoreOpsTry.branch]⟩

end Itasca.CoreVisitor

namespace Itasca

end Itasca

namespace Itasca

end Itasca

namespace Itasca

/-- `code.step_numeric` accepts with any accepting visitor whenever it does with the empty visitor,
at the same state. -/
theorem code.step_numeric.accepted_lift {V : Type} (visitor : code.OpVisitor V)
    (haccept : FullVisitor.Accepts visitor)
    (st st' : code.OpIterState) (opcode : U8) (v : V)
    (h : code.step_numeric code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor st opcode () =
      .ok (.Ok (), st', ())) :
    ∃ v', code.step_numeric visitor st opcode v = .ok (.Ok (), st', v') := by
  cases hm : Numeric.opcodeMeaning opcode with
  | none => simp [code.step_numeric.unrecognized _ st opcode () hm] at h
  | some op =>
    rw [code.step_numeric.dispatch _ st opcode op () hm] at h
    rw [code.step_numeric.dispatch visitor st opcode op v hm]
    exact CoreVisitor.run.accepted_lift _ _ _ () v st' () h
      (fun _ => haccept.visit_numeric v st' opcode)

set_option maxHeartbeats 1000000 in
/-- If `code.step` accepts with the empty visitor, it accepts at the same state with any visitor
whose hooks all accept. The resulting visitor state is unconstrained. -/
theorem code.step.accepted_lift {V : Type} (visitor : code.OpVisitor V)
    (haccept : FullVisitor.Accepts visitor)
    (st st' : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (opcode : U8) (v : V)
    (h : code.step code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor st data env ctx opcode () =
      .ok (.Ok (), st', ())) :
    ∃ v', code.step visitor st data env ctx opcode v = .ok (.Ok (), st', v') := by
  cases hm : MemoryMeaning.opcodeMeaning opcode with
  | some op =>
    rw [code.step_memory.dispatch _ st data env ctx () opcode op hm] at h
    rw [code.step_memory.dispatch visitor st data env ctx v opcode op hm]
    exact CoreVisitor.run.accepted_lift _ _ _ () v st' () h
      (fun arg => haccept.visit_memory v st' opcode arg)
  | none =>
    by_cases h_nop : opcode = code.OP_NOP
    · subst opcode
      rw [OpDispatch.dispatch_nop _ st data env ctx ()] at h
      rw [OpDispatch.dispatch_nop visitor st data env ctx v]
      exact CoreVisitor.run.accepted_lift _ _ _ () v st' () h
        (fun _ => haccept.on_nop v st')
    by_cases h_unreachable : opcode = code.OP_UNREACHABLE
    · subst opcode
      rw [OpDispatch.dispatch_unreachable _ st data env ctx ()] at h
      rw [OpDispatch.dispatch_unreachable visitor st data env ctx v]
      exact CoreVisitor.run.accepted_lift _ _ _ () v st' () h
        (fun _ => haccept.on_unreachable v st')
    by_cases h_i32_const : opcode = code.OP_I32_CONST
    · subst opcode
      rw [OpDispatch.dispatch_i32_const _ st data env ctx ()] at h
      rw [OpDispatch.dispatch_i32_const visitor st data env ctx v]
      exact CoreVisitor.run.accepted_lift _ _ _ () v st' () h
        (fun a => haccept.on_i32_const v st' a)
    by_cases h_i64_const : opcode = code.OP_I64_CONST
    · subst opcode
      rw [OpDispatch.dispatch_i64_const _ st data env ctx ()] at h
      rw [OpDispatch.dispatch_i64_const visitor st data env ctx v]
      exact CoreVisitor.run.accepted_lift _ _ _ () v st' () h
        (fun a => haccept.on_i64_const v st' a)
    by_cases h_f32_const : opcode = code.OP_F32_CONST
    · subst opcode
      rw [OpDispatch.dispatch_f32_const _ st data env ctx ()] at h
      rw [OpDispatch.dispatch_f32_const visitor st data env ctx v]
      exact CoreVisitor.run.accepted_lift _ _ _ () v st' () h
        (fun a => haccept.on_f32_const v st' a)
    by_cases h_f64_const : opcode = code.OP_F64_CONST
    · subst opcode
      rw [OpDispatch.dispatch_f64_const _ st data env ctx ()] at h
      rw [OpDispatch.dispatch_f64_const visitor st data env ctx v]
      exact CoreVisitor.run.accepted_lift _ _ _ () v st' () h
        (fun a => haccept.on_f64_const v st' a)
    by_cases h_drop : opcode = code.OP_DROP
    · subst opcode
      rw [OpDispatch.dispatch_drop _ st data env ctx ()] at h
      rw [OpDispatch.dispatch_drop visitor st data env ctx v]
      exact CoreVisitor.run.accepted_lift _ _ _ () v st' () h
        (fun a => haccept.on_drop v st' a)
    by_cases h_select : opcode = code.OP_SELECT
    · subst opcode
      rw [code.step_select.dispatch _ st data env ctx ()] at h
      rw [code.step_select.dispatch visitor st data env ctx v]
      exact CoreVisitor.run.accepted_lift _ _ _ () v st' () h
        (fun a => haccept.on_select v st' a)
    by_cases h_local_get : opcode = code.OP_LOCAL_GET
    · subst opcode
      rw [code.step_local_get.dispatch _ st data env ctx ()] at h
      rw [code.step_local_get.dispatch visitor st data env ctx v]
      exact CoreVisitor.run.accepted_lift _ _ _ () v st' () h
        (fun a => haccept.on_local_get v st' a)
    by_cases h_local_set : opcode = code.OP_LOCAL_SET
    · subst opcode
      rw [code.step_local_set.dispatch _ st data env ctx ()] at h
      rw [code.step_local_set.dispatch visitor st data env ctx v]
      exact CoreVisitor.run.accepted_lift _ _ _ () v st' () h
        (fun a => haccept.on_local_set v st' a)
    by_cases h_local_tee : opcode = code.OP_LOCAL_TEE
    · subst opcode
      rw [code.step_local_tee.dispatch _ st data env ctx ()] at h
      rw [code.step_local_tee.dispatch visitor st data env ctx v]
      exact CoreVisitor.run.accepted_lift _ _ _ () v st' () h
        (fun a => haccept.on_local_tee v st' a)
    by_cases h_global_get : opcode = code.OP_GLOBAL_GET
    · subst opcode
      rw [code.step_global_get.dispatch _ st data env ctx ()] at h
      rw [code.step_global_get.dispatch visitor st data env ctx v]
      exact CoreVisitor.run.accepted_lift _ _ _ () v st' () h
        (fun a => haccept.on_global_get v st' a)
    by_cases h_global_set : opcode = code.OP_GLOBAL_SET
    · subst opcode
      rw [code.step_global_set.dispatch _ st data env ctx ()] at h
      rw [code.step_global_set.dispatch visitor st data env ctx v]
      exact CoreVisitor.run.accepted_lift _ _ _ () v st' () h
        (fun a => haccept.on_global_set v st' a)
    by_cases h_memory_size : opcode = code.OP_MEMORY_SIZE
    · subst opcode
      rw [code.step_memory_size.dispatch _ st data env ctx ()] at h
      rw [code.step_memory_size.dispatch visitor st data env ctx v]
      exact CoreVisitor.run.accepted_lift _ _ _ () v st' () h
        (fun _ => haccept.on_memory_size v st')
    by_cases h_memory_grow : opcode = code.OP_MEMORY_GROW
    · subst opcode
      rw [code.step_memory_grow.dispatch _ st data env ctx ()] at h
      rw [code.step_memory_grow.dispatch visitor st data env ctx v]
      exact CoreVisitor.run.accepted_lift _ _ _ () v st' () h
        (fun _ => haccept.on_memory_grow v st')
    have heqval (a b : U8) : a = b ↔ a.val = b.val :=
      ⟨fun h => congrArg UScalar.val h, UScalar.eq_of_val_eq⟩
    have hdispatch {W : Type} (hooks : code.OpVisitor W) (w : W) :
        code.step hooks st data env ctx opcode w = code.step_memory hooks st data env opcode w := by
      unfold code.step
      split <;> simp_all [global_simps, U8.ofNat, UScalar.ofNat, UScalar.ofNatCore]
    rw [hdispatch _ ()] at h
    rw [hdispatch visitor v]
    rw [OpDispatch.memory_fallback _ st data env opcode () hm h_memory_size h_memory_grow] at h
    rw [OpDispatch.memory_fallback visitor st data env opcode v hm h_memory_size h_memory_grow]
    exact code.step_numeric.accepted_lift visitor haccept st st' opcode v h

end Itasca
