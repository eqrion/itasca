import Itasca.Support.Result
import Itasca.Visitor.Dispatch
import Itasca.Visitor.Erasure
import Itasca.Visitor.BrTableErasure
import Itasca.Handler.NumericDispatch
import Itasca.Handler.Select
import Itasca.Handler.EnvDispatch

/-!
# Erasing the visitor from an accepted step

`code.step.accepted_erase` shows that if `code.step` accepts an instruction with any visitor, it
accepts it with `code.EmptyOpVisitor` and reaches the same validator state. The proof dispatches
on the opcode using `Visitor/Dispatch`, and handles `br_table` and its nested label hooks through
`Visitor/BrTableErasure`. Covers the Wasm 1.0 step `code.step`.
-/

open Aeneas Aeneas.Std

namespace Itasca.VisitorErasure

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- The empty visitor accepts every numeric opcode. -/
theorem visit_numeric_empty (st : code.OpIterState) (opcode : U8) :
    code.visit_numeric code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor () st opcode =
      .ok (.Ok (), ()) := by
  rcases opcode with ⟨⟨n, hn⟩⟩
  change n < 256 at hn
  interval_cases n <;> with_unfolding_all rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- The empty visitor accepts every load and store opcode. -/
theorem visit_memory_empty (st : code.OpIterState) (opcode : U8) (arg : code.MemArg) :
    code.visit_memory code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor () st opcode arg =
      .ok (.Ok (), ()) := by
  rcases opcode with ⟨⟨n, hn⟩⟩
  change n < 256 at hn
  interval_cases n <;> with_unfolding_all rfl


end Itasca.VisitorErasure

namespace Itasca

/-- An accepted `code.step_numeric` run also succeeds, at the same state, with the empty visitor. -/
theorem code.step_numeric.accepted_erase {V : Type} (visitor : code.OpVisitor V)
    (st st' : code.OpIterState) (opcode : U8) (v v' : V)
    (h : code.step_numeric visitor st opcode v = .ok (.Ok (), st', v')) :
    code.step_numeric code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor st opcode () =
      .ok (.Ok (), st', ()) := by
  cases hm : Numeric.opcodeMeaning opcode with
  | none => simp [code.step_numeric.unrecognized visitor st opcode v hm] at h
  | some op =>
    rw [code.step_numeric.dispatch visitor st opcode op v hm] at h
    rw [code.step_numeric.dispatch _ st opcode op () hm]
    exact CoreVisitor.run.accepted_transfer _ _ _ v () () st' v' h
      (fun _ => VisitorErasure.visit_numeric_empty st' opcode)

/-- An accepted `br_table` step succeeds with the empty visitor, given that its label reader does.
The final `on_br_table` hook is erased here. -/
theorem code.step_br_table.accepted_erase_of_read {V : Type} (visitor : code.OpVisitor V)
    (st st' : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v v' : V)
    (hread : ∀ args s w, code.read_br_table visitor st data v = .ok (.Ok args, s, w) →
      code.read_br_table code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor st data () =
        .ok (.Ok args, s, ()))
    (h : code.step visitor st data env ctx code.OP_BR_TABLE v = .ok (.Ok (), st', v')) :
    code.step code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor st data env ctx code.OP_BR_TABLE () =
      .ok (.Ok (), st', ()) := by
  simp [global_simps] at h
  obtain ⟨⟨res, s, w⟩, hr, hnext⟩ := ResultFacts.bind_ok_inv _ _ _ h
  cases res with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at hnext
  | Ok args =>
    obtain ⟨depth, bt⟩ := args
    simp [core.result.Result.Insts.CoreOpsTry.branch] at hnext
    obtain ⟨⟨vis, w'⟩, hv, hout⟩ := ResultFacts.bind_ok_inv _ _ _ hnext
    cases vis with
    | Err e => simp [code.visit, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at hout
    | Ok u =>
      simp [code.visit] at hout
      obtain ⟨rfl, rfl⟩ := hout
      have he := hread (depth, bt) s w hr
      simp [global_simps, he, code.visit, code.OpVisitor.on_br_table.default,
        core.result.Result.Insts.CoreOpsTry.branch]

set_option maxHeartbeats 1000000 in
/-- An accepted step of any instruction succeeds with the empty visitor, given that the label
reader of `br_table` does. Only `br_table` calls hooks inside its reader. -/
theorem code.step.accepted_erase_of_br_table {V : Type} (visitor : code.OpVisitor V)
    (st st' : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (opcode : U8) (v v' : V)
    (hread : ∀ args s w, code.read_br_table visitor st data v = .ok (.Ok args, s, w) →
      code.read_br_table code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor st data () =
        .ok (.Ok args, s, ()))
    (h : code.step visitor st data env ctx opcode v = .ok (.Ok (), st', v')) :
    code.step code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor st data env ctx opcode () =
      .ok (.Ok (), st', ()) := by
  cases hm : MemoryMeaning.opcodeMeaning opcode with
  | some op =>
    rw [code.step_memory.dispatch visitor st data env ctx v opcode op hm] at h
    rw [code.step_memory.dispatch _ st data env ctx () opcode op hm]
    exact CoreVisitor.run.accepted_transfer _ _ _ v () () st' v' h
      (fun _ => VisitorErasure.visit_memory_empty st' opcode _)
  | none =>
    by_cases h_nop : opcode = code.OP_NOP
    · subst opcode
      rw [OpDispatch.dispatch_nop visitor st data env ctx v] at h
      rw [OpDispatch.dispatch_nop _ st data env ctx ()]
      exact CoreVisitor.run.accepted_transfer _ _ _ v () () st' v' h (fun _ => rfl)
    by_cases h_unreachable : opcode = code.OP_UNREACHABLE
    · subst opcode
      rw [OpDispatch.dispatch_unreachable visitor st data env ctx v] at h
      rw [OpDispatch.dispatch_unreachable _ st data env ctx ()]
      exact CoreVisitor.run.accepted_transfer _ _ _ v () () st' v' h (fun _ => rfl)
    by_cases h_i32_const : opcode = code.OP_I32_CONST
    · subst opcode
      rw [OpDispatch.dispatch_i32_const visitor st data env ctx v] at h
      rw [OpDispatch.dispatch_i32_const _ st data env ctx ()]
      exact CoreVisitor.run.accepted_transfer _ _ _ v () () st' v' h (fun _ => rfl)
    by_cases h_i64_const : opcode = code.OP_I64_CONST
    · subst opcode
      rw [OpDispatch.dispatch_i64_const visitor st data env ctx v] at h
      rw [OpDispatch.dispatch_i64_const _ st data env ctx ()]
      exact CoreVisitor.run.accepted_transfer _ _ _ v () () st' v' h (fun _ => rfl)
    by_cases h_f32_const : opcode = code.OP_F32_CONST
    · subst opcode
      rw [OpDispatch.dispatch_f32_const visitor st data env ctx v] at h
      rw [OpDispatch.dispatch_f32_const _ st data env ctx ()]
      exact CoreVisitor.run.accepted_transfer _ _ _ v () () st' v' h (fun _ => rfl)
    by_cases h_f64_const : opcode = code.OP_F64_CONST
    · subst opcode
      rw [OpDispatch.dispatch_f64_const visitor st data env ctx v] at h
      rw [OpDispatch.dispatch_f64_const _ st data env ctx ()]
      exact CoreVisitor.run.accepted_transfer _ _ _ v () () st' v' h (fun _ => rfl)
    by_cases h_drop : opcode = code.OP_DROP
    · subst opcode
      rw [OpDispatch.dispatch_drop visitor st data env ctx v] at h
      rw [OpDispatch.dispatch_drop _ st data env ctx ()]
      exact CoreVisitor.run.accepted_transfer _ _ _ v () () st' v' h (fun _ => rfl)
    by_cases h_select : opcode = code.OP_SELECT
    · subst opcode
      rw [code.step_select.dispatch visitor st data env ctx v] at h
      rw [code.step_select.dispatch _ st data env ctx ()]
      exact CoreVisitor.run.accepted_transfer _ _ _ v () () st' v' h (fun _ => rfl)
    by_cases h_block : opcode = code.OP_BLOCK
    · subst opcode
      rw [OpDispatch.dispatch_block visitor st data env ctx v] at h
      rw [OpDispatch.dispatch_block _ st data env ctx ()]
      exact CoreVisitor.run.accepted_transfer _ _ _ v () () st' v' h (fun _ => rfl)
    by_cases h_loop : opcode = code.OP_LOOP
    · subst opcode
      rw [OpDispatch.dispatch_loop visitor st data env ctx v] at h
      rw [OpDispatch.dispatch_loop _ st data env ctx ()]
      exact CoreVisitor.run.accepted_transfer _ _ _ v () () st' v' h (fun _ => rfl)
    by_cases h_if : opcode = code.OP_IF
    · subst opcode
      rw [OpDispatch.dispatch_if visitor st data env ctx v] at h
      rw [OpDispatch.dispatch_if _ st data env ctx ()]
      exact CoreVisitor.run.accepted_transfer _ _ _ v () () st' v' h (fun _ => rfl)
    by_cases h_else : opcode = code.OP_ELSE
    · subst opcode
      rw [OpDispatch.dispatch_else visitor st data env ctx v] at h
      rw [OpDispatch.dispatch_else _ st data env ctx ()]
      exact CoreVisitor.run.accepted_transfer _ _ _ v () () st' v' h (fun _ => rfl)
    by_cases h_end : opcode = code.OP_END
    · subst opcode
      rw [OpDispatch.dispatch_end visitor st data env ctx v] at h
      rw [OpDispatch.dispatch_end _ st data env ctx ()]
      exact CoreVisitor.run.accepted_transfer _ _ _ v () () st' v' h (fun _ => rfl)
    by_cases h_br : opcode = code.OP_BR
    · subst opcode
      rw [OpDispatch.dispatch_br visitor st data env ctx v] at h
      rw [OpDispatch.dispatch_br _ st data env ctx ()]
      exact CoreVisitor.run.accepted_transfer _ _ _ v () () st' v' h (fun _ => rfl)
    by_cases h_br_if : opcode = code.OP_BR_IF
    · subst opcode
      rw [OpDispatch.dispatch_br_if visitor st data env ctx v] at h
      rw [OpDispatch.dispatch_br_if _ st data env ctx ()]
      exact CoreVisitor.run.accepted_transfer _ _ _ v () () st' v' h (fun _ => rfl)
    by_cases h_br_table : opcode = code.OP_BR_TABLE
    · subst opcode
      exact code.step_br_table.accepted_erase_of_read visitor st st' data env ctx v v' hread h
    by_cases h_return : opcode = code.OP_RETURN
    · subst opcode
      rw [OpDispatch.dispatch_return visitor st data env ctx v] at h
      rw [OpDispatch.dispatch_return _ st data env ctx ()]
      exact CoreVisitor.run.accepted_transfer _ _ _ v () () st' v' h (fun _ => rfl)
    by_cases h_call : opcode = code.OP_CALL
    · subst opcode
      rw [code.step_call.dispatch visitor st data env ctx v] at h
      rw [code.step_call.dispatch _ st data env ctx ()]
      exact CoreVisitor.run.accepted_transfer _ _ _ v () () st' v' h (fun _ => rfl)
    by_cases h_call_indirect : opcode = code.OP_CALL_INDIRECT
    · subst opcode
      rw [code.step_call_indirect.dispatch visitor st data env ctx v] at h
      rw [code.step_call_indirect.dispatch _ st data env ctx ()]
      exact CoreVisitor.run.accepted_transfer _ _ _ v () () st' v' h (fun _ => rfl)
    by_cases h_local_get : opcode = code.OP_LOCAL_GET
    · subst opcode
      rw [code.step_local_get.dispatch visitor st data env ctx v] at h
      rw [code.step_local_get.dispatch _ st data env ctx ()]
      exact CoreVisitor.run.accepted_transfer _ _ _ v () () st' v' h (fun _ => rfl)
    by_cases h_local_set : opcode = code.OP_LOCAL_SET
    · subst opcode
      rw [code.step_local_set.dispatch visitor st data env ctx v] at h
      rw [code.step_local_set.dispatch _ st data env ctx ()]
      exact CoreVisitor.run.accepted_transfer _ _ _ v () () st' v' h (fun _ => rfl)
    by_cases h_local_tee : opcode = code.OP_LOCAL_TEE
    · subst opcode
      rw [code.step_local_tee.dispatch visitor st data env ctx v] at h
      rw [code.step_local_tee.dispatch _ st data env ctx ()]
      exact CoreVisitor.run.accepted_transfer _ _ _ v () () st' v' h (fun _ => rfl)
    by_cases h_global_get : opcode = code.OP_GLOBAL_GET
    · subst opcode
      rw [code.step_global_get.dispatch visitor st data env ctx v] at h
      rw [code.step_global_get.dispatch _ st data env ctx ()]
      exact CoreVisitor.run.accepted_transfer _ _ _ v () () st' v' h (fun _ => rfl)
    by_cases h_global_set : opcode = code.OP_GLOBAL_SET
    · subst opcode
      rw [code.step_global_set.dispatch visitor st data env ctx v] at h
      rw [code.step_global_set.dispatch _ st data env ctx ()]
      exact CoreVisitor.run.accepted_transfer _ _ _ v () () st' v' h (fun _ => rfl)
    by_cases h_memory_size : opcode = code.OP_MEMORY_SIZE
    · subst opcode
      rw [code.step_memory_size.dispatch visitor st data env ctx v] at h
      rw [code.step_memory_size.dispatch _ st data env ctx ()]
      exact CoreVisitor.run.accepted_transfer _ _ _ v () () st' v' h (fun _ => rfl)
    by_cases h_memory_grow : opcode = code.OP_MEMORY_GROW
    · subst opcode
      rw [code.step_memory_grow.dispatch visitor st data env ctx v] at h
      rw [code.step_memory_grow.dispatch _ st data env ctx ()]
      exact CoreVisitor.run.accepted_transfer _ _ _ v () () st' v' h (fun _ => rfl)
    have heqval (a b : U8) : a = b ↔ a.val = b.val :=
      ⟨fun h => congrArg UScalar.val h, UScalar.eq_of_val_eq⟩
    have hdispatch {W : Type} (hooks : code.OpVisitor W) (w : W) :
        code.step hooks st data env ctx opcode w = code.step_memory hooks st data env opcode w := by
      unfold code.step
      split <;> simp_all [global_simps, U8.ofNat, UScalar.ofNat, UScalar.ofNatCore]
    rw [hdispatch visitor v] at h
    rw [hdispatch _ ()]
    rw [OpDispatch.memory_fallback visitor st data env opcode v hm h_memory_size h_memory_grow] at h
    rw [OpDispatch.memory_fallback _ st data env opcode () hm h_memory_size h_memory_grow]
    exact code.step_numeric.accepted_erase visitor st st' opcode v v' h

/-- An accepted `code.step` run also succeeds, at the same state, with the empty visitor. -/
theorem code.step.accepted_erase {V : Type} (visitor : code.OpVisitor V)
    (st st' : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (opcode : U8) (v v' : V)
    (h : code.step visitor st data env ctx opcode v = .ok (.Ok (), st', v')) :
    code.step code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor st data env ctx opcode () =
      .ok (.Ok (), st', ()) :=
  code.step.accepted_erase_of_br_table visitor st st' data env ctx opcode v v'
    (fun args s w hr => code.read_br_table.accepted_erasure visitor st data v args s w hr) h

end Itasca
