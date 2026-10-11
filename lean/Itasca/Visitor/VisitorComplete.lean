import Itasca.Support.Result
import Itasca.Visitor.OpDispatch
import Itasca.Visitor.FullVisitorAccept
import Itasca.Visitor.VisitorStepErasure
import Itasca.Body.WasmExecution

open Aeneas Aeneas.Std

namespace Itasca.CoreVisitor

/-- A successful handler can be replayed through any accepting replacement hook. -/
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

/-- Each accepting label callback can change visitor state without changing
branch-table decoding, its merged target, or the resulting validator state. -/
theorem code.read_table_labels_loop.accepted_lift {V : Type} (visitor : code.OpVisitor V)
    (haccept : FullVisitor.Accepts visitor)
    (st : code.OpIterState) (data : Slice U8) (count : U32) (v : V)
    (expect : Option code.BlockType) (i : U32) (hi : i.val ≤ count.val)
    (result : Option code.BlockType) (st' : code.OpIterState)
    (h : code.read_table_labels_loop code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      st data count () expect i = .ok (.Ok result, st', ())) :
    ∃ v', code.read_table_labels_loop visitor st data count v expect i = .ok (.Ok result, st', v') := by
  generalize hn : count.val - i.val = n
  induction n using Nat.strong_induction_on generalizing st v expect i with
  | h n ih =>
    unfold code.read_table_labels_loop at h ⊢
    unfold loop at h ⊢
    simp only [code.read_table_labels_loop.body] at h ⊢
    by_cases heq : i = count
    · simp [heq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨v, by simp [heq]⟩
    · simp only [heq, ↓reduceIte] at h ⊢
      obtain ⟨⟨res, s⟩, hr, _, _, _⟩ := WP.spec_imp_exists (code.read_label.spec st data)
      rw [hr] at h ⊢
      cases res with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
      | Ok pair =>
        obtain ⟨depth, target⟩ := pair
        obtain ⟨v1, hv⟩ := haccept.on_br_table_label v s depth
        obtain ⟨bt, hbt, _⟩ := WP.spec_imp_exists (code.branch_target_bt.spec target)
        obtain ⟨merged, hm, _⟩ := WP.spec_imp_exists (code.merge_target.spec expect bt)
        cases merged with
        | Err e =>
          simp [code.OpVisitor.on_br_table_label.default, code.visit, hbt, hm,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at h
        | Ok common =>
          have hlt : i.val < count.val := by
            have hne : i.val ≠ count.val := fun he => heq (UScalar.eq_of_val_eq he)
            omega
          obtain ⟨j, hj, hjval⟩ := WP.spec_imp_exists
            (UScalar.add_spec (x := i) (y := 1#u32) (by scalar_tac))
          simp [code.OpVisitor.on_br_table_label.default, code.visit, hbt, hm, hj,
            core.result.Result.Insts.CoreOpsTry.branch] at h
          have htail : code.read_table_labels_loop code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
              s data count () (some common) j = .ok (.Ok result, st', ()) := by
            simpa [code.read_table_labels_loop, code.read_table_labels_loop.body,
              code.OpVisitor.on_br_table_label.default, code.visit,
              core.result.Result.Insts.CoreOpsTry.branch] using h
          obtain ⟨v2, hrec⟩ := ih (count.val - j.val) (by scalar_tac) s v1 (some common) j
            (by scalar_tac) htail rfl
          refine ⟨v2, ?_⟩
          simp [hv, code.visit, hbt, hm, hj, core.result.Result.Insts.CoreOpsTry.branch]
          simpa [code.read_table_labels_loop, code.read_table_labels_loop.body, code.visit,
            core.result.Result.Insts.CoreOpsTry.branch] using hrec

theorem code.read_table_labels.accepted_lift {V : Type} (visitor : code.OpVisitor V)
    (haccept : FullVisitor.Accepts visitor)
    (st : code.OpIterState) (data : Slice U8) (count : U32) (v : V)
    (result : Option code.BlockType) (st' : code.OpIterState)
    (h : code.read_table_labels code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      st data count () = .ok (.Ok result, st', ())) :
    ∃ v', code.read_table_labels visitor st data count v = .ok (.Ok result, st', v') :=
  code.read_table_labels_loop.accepted_lift visitor haccept st data count v none 0#u32
    (by scalar_tac) result st' h

end Itasca

namespace Itasca

/-- Internal branch-table callbacks preserve every successful validator result. -/
theorem code.read_br_table.accepted_lift {V : Type} (visitor : code.OpVisitor V)
    (haccept : FullVisitor.Accepts visitor)
    (st : code.OpIterState) (data : Slice U8) (v : V)
    (result : U32 × code.BlockType) (st' : code.OpIterState)
    (h : code.read_br_table code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      st data () = .ok (.Ok result, st', ())) :
    ∃ v', code.read_br_table visitor st data v = .ok (.Ok result, st', v') := by
  unfold code.read_br_table at h ⊢
  obtain ⟨countResult, hc, hout⟩ := ResultFacts.bind_ok_inv _ _ _ h
  rw [hc]
  cases countResult with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at hout
  | Ok pair =>
    obtain ⟨count, next⟩ := pair
    simp [core.result.Result.Insts.CoreOpsTry.branch] at hout ⊢
    obtain ⟨⟨labels, s1, _⟩, hl, hout⟩ := ResultFacts.bind_ok_inv _ _ _ hout
    cases labels with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at hout
    | Ok expect =>
      obtain ⟨v1, hlift⟩ := code.read_table_labels.accepted_lift visitor haccept
        {st with pos := next} data count v expect s1 hl
      rw [hlift]
      refine ⟨v1, ?_⟩
      simp at hout ⊢
      obtain ⟨⟨label, s2⟩, hd, hout⟩ := ResultFacts.bind_ok_inv _ _ _ hout
      rw [hd]
      cases label with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at hout
      | Ok pair =>
        obtain ⟨default, target⟩ := pair
        simp at hout ⊢
        obtain ⟨bt, hb, hout⟩ := ResultFacts.bind_ok_inv _ _ _ hout
        rw [hb]
        simp only [bind_ok]
        obtain ⟨merged, hm, hout⟩ := ResultFacts.bind_ok_inv _ _ _ hout
        rw [hm]
        cases merged with
        | Err e =>
          simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at hout
        | Ok common =>
          simp at hout ⊢
          obtain ⟨⟨selector, s3⟩, hs, hout⟩ := ResultFacts.bind_ok_inv _ _ _ hout
          rw [hs]
          cases selector with
          | Err e =>
            simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at hout
          | Ok t =>
            simp at hout ⊢
            obtain ⟨types, ht, hout⟩ := ResultFacts.bind_ok_inv _ _ _ hout
            rw [ht]
            simp only [bind_ok]
            obtain ⟨⟨operands, s4⟩, hp, hout⟩ := ResultFacts.bind_ok_inv _ _ _ hout
            rw [hp]
            cases operands with
            | Err e =>
              simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at hout
            | Ok u =>
              simp at hout ⊢
              obtain ⟨s5, hu, hout⟩ := ResultFacts.bind_ok_inv _ _ _ hout
              rw [hu]
              simp only [bind_ok]
              simp at hout
              obtain ⟨rfl, rfl⟩ := hout
              rfl

end Itasca



namespace Itasca

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

/-- The table's internal accepting label hooks precede its final accepting hook. -/
theorem code.step_br_table.accepted_lift {V : Type} (visitor : code.OpVisitor V)
    (haccept : FullVisitor.Accepts visitor)
    (st st' : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (v : V)
    (h : code.step code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor st data env ctx code.OP_BR_TABLE () =
      .ok (.Ok (), st', ())) :
    ∃ v', code.step visitor st data env ctx code.OP_BR_TABLE v = .ok (.Ok (), st', v') := by
  rw [code.step_br_table.dispatch] at h
  obtain ⟨⟨res, s, w⟩, hr, hnext⟩ := ResultFacts.bind_ok_inv _ _ _ h
  cases w
  dsimp only at hnext
  obtain ⟨args, hhandler, _⟩ := CoreVisitor.run.accepted (.ok (res, s))
    (fun v s a => code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor.on_br_table v s a.1 (Control.resultView a.2))
    () st' () hnext
  have heq : res = .Ok args ∧ s = st' := by simpa using hhandler
  obtain ⟨hres, hs⟩ := heq
  subst res
  subst s
  obtain ⟨v1, hlift⟩ := code.read_br_table.accepted_lift visitor haccept st data v args st' hr
  obtain ⟨v2, hv⟩ := haccept.on_br_table v1 st' args.1 (Control.resultView args.2)
  refine ⟨v2, ?_⟩
  rw [code.step_br_table.dispatch]
  simp [hlift, CoreVisitor.run, hv, code.visit, core.result.Result.Insts.CoreOpsTry.branch]

set_option maxHeartbeats 1000000 in
/-- Successful validation transfers to any visitor whose hooks always accept,
with precisely the same validator state and an unconstrained new visitor state. -/
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
    by_cases h_block : opcode = code.OP_BLOCK
    · subst opcode
      rw [OpDispatch.dispatch_block _ st data env ctx ()] at h
      rw [OpDispatch.dispatch_block visitor st data env ctx v]
      exact CoreVisitor.run.accepted_lift _ _ _ () v st' () h
        (fun a => haccept.on_block v st' (Control.signature a))
    by_cases h_loop : opcode = code.OP_LOOP
    · subst opcode
      rw [OpDispatch.dispatch_loop _ st data env ctx ()] at h
      rw [OpDispatch.dispatch_loop visitor st data env ctx v]
      exact CoreVisitor.run.accepted_lift _ _ _ () v st' () h
        (fun a => haccept.on_loop v st' (Control.signature a))
    by_cases h_if : opcode = code.OP_IF
    · subst opcode
      rw [OpDispatch.dispatch_if _ st data env ctx ()] at h
      rw [OpDispatch.dispatch_if visitor st data env ctx v]
      exact CoreVisitor.run.accepted_lift _ _ _ () v st' () h
        (fun a => haccept.on_if v st' (Control.signature a))
    by_cases h_else : opcode = code.OP_ELSE
    · subst opcode
      rw [OpDispatch.dispatch_else _ st data env ctx ()] at h
      rw [OpDispatch.dispatch_else visitor st data env ctx v]
      exact CoreVisitor.run.accepted_lift _ _ _ () v st' () h
        (fun a => haccept.on_else v st' (Control.signature a))
    by_cases h_end : opcode = code.OP_END
    · subst opcode
      rw [OpDispatch.dispatch_end _ st data env ctx ()] at h
      rw [OpDispatch.dispatch_end visitor st data env ctx v]
      exact CoreVisitor.run.accepted_lift _ _ _ () v st' () h
        (fun a => haccept.on_end v st' a.1 (Control.signature a.2))
    by_cases h_br : opcode = code.OP_BR
    · subst opcode
      rw [OpDispatch.dispatch_br _ st data env ctx ()] at h
      rw [OpDispatch.dispatch_br visitor st data env ctx v]
      exact CoreVisitor.run.accepted_lift _ _ _ () v st' () h
        (fun a => haccept.on_br v st' a.1 (Control.resultView a.2))
    by_cases h_br_if : opcode = code.OP_BR_IF
    · subst opcode
      rw [OpDispatch.dispatch_br_if _ st data env ctx ()] at h
      rw [OpDispatch.dispatch_br_if visitor st data env ctx v]
      exact CoreVisitor.run.accepted_lift _ _ _ () v st' () h
        (fun a => haccept.on_br_if v st' a.1 (Control.resultView a.2))
    by_cases h_br_table : opcode = code.OP_BR_TABLE
    · subst opcode
      exact code.step_br_table.accepted_lift visitor haccept st st' data env ctx v h
    by_cases h_return : opcode = code.OP_RETURN
    · subst opcode
      rw [OpDispatch.dispatch_return _ st data env ctx ()] at h
      rw [OpDispatch.dispatch_return visitor st data env ctx v]
      exact CoreVisitor.run.accepted_lift _ _ _ () v st' () h
        (fun _ => haccept.on_return v st')
    by_cases h_call : opcode = code.OP_CALL
    · subst opcode
      rw [code.step_call.dispatch _ st data env ctx ()] at h
      rw [code.step_call.dispatch visitor st data env ctx v]
      exact CoreVisitor.run.accepted_lift _ _ _ () v st' () h
        (fun a => haccept.on_call v st' a)
    by_cases h_call_indirect : opcode = code.OP_CALL_INDIRECT
    · subst opcode
      rw [code.step_call_indirect.dispatch _ st data env ctx ()] at h
      rw [code.step_call_indirect.dispatch visitor st data env ctx v]
      exact CoreVisitor.run.accepted_lift _ _ _ () v st' () h
        (fun a => haccept.on_call_indirect v st' a 0#u32)
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
