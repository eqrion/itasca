import Itasca.Support.Result
import Itasca.Visitor.Dispatch
import Itasca.Visitor.BrTableRefinement
import Itasca.Visitor.EventDispatch

/-!
# Refinement of an instruction step

`code.step.refines` lifts a `VisitorTrace.Refines` relation between two visitors to the whole
extracted `code.step`. `code.step.instrument_forward` and `code.step.instrument_backward` specialise
it to the recording wrapper `instrument`, so a step can be run with or without recording and
return the same result and validator state. Covers the Wasm 1.0 step `code.step`.
-/

open Aeneas Aeneas.Std

namespace Itasca

open VisitorTrace

/-- A refinement of hooks lifts to `code.step` for every opcode. Every normal return, including
rejections and malformed instructions, is reproduced with the same result and validator state. -/
theorem code.step.refines {V W : Type}
    (visitor : code.OpVisitor V) (replacement : code.OpVisitor W)
    (related : V → W → Prop) (hrefines : Refines visitor replacement related)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
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

end Itasca
