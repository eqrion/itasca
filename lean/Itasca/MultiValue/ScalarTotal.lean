import Itasca.MultiValue.ScalarReaders
import Itasca.Body.AllNumeric
import Itasca.Body.WasmStepScalar
import Itasca.Visitor.OpDispatch

open Aeneas Aeneas.Std

namespace Itasca.MultiValue

/-- Opcodes whose control effects are handled by the multi-value dispatcher. -/
def controlOpcodes : List Nat := [2, 3, 4, 5, 11, 12, 13, 14, 15, 16, 17]

private theorem run_total {A V : Type}
    (read : Result (core.result.Result A error.OpError × code.OpIterState))
    (hook : V → code.OpIterState → A → Result (core.result.Result Unit error.VisitError × V))
    (v : V) (Q : code.OpIterState → Prop)
    (hr : read ⦃ r => Q r.2 ⦄)
    (hh : ∀ s a, ∃ res v', hook v s a = .ok (res, v')) :
    CoreVisitor.run read hook v ⦃ r => Q r.2.1 ⦄ := by
  have hr' : read ⦃ r => Q r.2 ∧ ∀ a, r.1 = .Ok a → True ⦄ := by
    apply WP.spec_mono hr
    intro r h
    exact ⟨h, by simp⟩
  apply WP.spec_mono (CoreVisitor.run.spec read hook v Q (fun _ _ => True) hr' hh)
  intro r h
  exact h.1

private theorem run_scalar {A V : Type} (st : code.OpIterState)
    (read : Result (core.result.Result A error.OpError × code.OpIterState))
    (hook : V → code.OpIterState → A → Result (core.result.Result Unit error.VisitError × V))
    (v : V)
    (hr : read ⦃ r => Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧ st.pos.val ≤ r.2.pos.val ⦄)
    (hh : ∀ s a, ∃ res v', hook v s a = .ok (res, v')) :
    CoreVisitor.run read hook v ⦃ r => Control.Shape r.2.1 ∧
      r.2.1.ctrls.val.length = st.ctrls.val.length ∧ st.pos.val ≤ r.2.1.pos.val ⦄ := by
  apply run_total read hook v (fun s => Control.Shape s ∧
    s.ctrls.val.length = st.ctrls.val.length ∧ st.pos.val ≤ s.pos.val)
  · apply WP.spec_mono hr
    rintro r ⟨hs, hc, hp⟩
    exact ⟨hs, by simp [hc], hp⟩
  · exact hh

private theorem memory_meaning_exists (opcode : U8)
    (hlo : 0x28 ≤ opcode.val) (hhi : opcode.val ≤ 0x3E) :
    ∃ operation, MemoryMeaning.opcodeMeaning opcode = some operation := by
  rcases opcode with ⟨⟨n, hn⟩⟩
  change 40 ≤ n at hlo
  change n ≤ 62 at hhi
  interval_cases n <;> exact ⟨_, rfl⟩

/-- The shared scalar dispatcher is total for arbitrary structurally bounded
multi-value frames. It preserves control depth and never moves the cursor back. -/
theorem scalar_total {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (opcode : U8) (v : V) (hs : Control.Shape st)
    (hsize : st.vals.val.length < Usize.max)
    (hscalar : opcode.val ∉ controlOpcodes) (hvisitor : FullVisitor.Total visitor) :
    code.step visitor st data env ctx opcode v ⦃ r => Control.Shape r.2.1 ∧
      r.2.1.ctrls.val.length = st.ctrls.val.length ∧ st.pos.val ≤ r.2.1.pos.val ⦄ := by
  by_cases hhigh : 0x45 ≤ opcode.val
  · rw [code.step.numeric_dispatch visitor st data env ctx opcode v hhigh]
    apply WP.spec_mono (code.step_numeric.total visitor st opcode v hs hsize hvisitor)
    rintro r ⟨hs', hc, hp, _⟩
    exact ⟨hs', by simp [hc], by simp [hp]⟩
  by_cases hmemory : 0x28 ≤ opcode.val ∧ opcode.val ≤ 0x3E
  · obtain ⟨operation, hm⟩ := memory_meaning_exists opcode hmemory.1 hmemory.2
    rw [code.step_memory.dispatch visitor st data env ctx v opcode operation hm]
    apply run_scalar st
    · split
      · exact ScalarReaders.store st data env operation.ty operation.naturalAlign hs hsize
      · exact ScalarReaders.load st data env operation.ty operation.naturalAlign hs hsize
    · exact fun s _ => hvisitor.visit_memory v s opcode _
  by_cases h_nop : opcode = code.OP_NOP
  · subst opcode
    apply WP.spec_mono (code.step_nop.total visitor st data env ctx v hvisitor.toCore)
    intro r hr
    simp [hr, hs]
  by_cases h_unreachable : opcode = code.OP_UNREACHABLE
  · subst opcode
    rw [OpDispatch.dispatch_unreachable]
    apply run_total _ _ v (fun s => Control.Shape s ∧
      s.ctrls.val.length = st.ctrls.val.length ∧ st.pos.val ≤ s.pos.val)
    · unfold code.read_unreachable
      step*
    · exact fun s _ => hvisitor.on_unreachable v s
  by_cases h_i32_const : opcode = code.OP_I32_CONST
  · subst opcode
    rw [OpDispatch.dispatch_i32_const]
    exact run_scalar st _ _ v (ScalarReaders.i32_const st data hs hsize)
      (fun s a => hvisitor.on_i32_const v s a)
  by_cases h_i64_const : opcode = code.OP_I64_CONST
  · subst opcode
    rw [OpDispatch.dispatch_i64_const]
    exact run_scalar st _ _ v (ScalarReaders.i64_const st data hs hsize)
      (fun s a => hvisitor.on_i64_const v s a)
  by_cases h_f32_const : opcode = code.OP_F32_CONST
  · subst opcode
    rw [OpDispatch.dispatch_f32_const]
    exact run_scalar st _ _ v (ScalarReaders.f32_const st data hs hsize)
      (fun s a => hvisitor.on_f32_const v s a)
  by_cases h_f64_const : opcode = code.OP_F64_CONST
  · subst opcode
    rw [OpDispatch.dispatch_f64_const]
    exact run_scalar st _ _ v (ScalarReaders.f64_const st data hs hsize)
      (fun s a => hvisitor.on_f64_const v s a)
  by_cases h_drop : opcode = code.OP_DROP
  · subst opcode
    rw [OpDispatch.dispatch_drop]
    exact run_scalar st _ _ v (ScalarReaders.drop st  hs hsize)
      (fun s a => hvisitor.on_drop v s a)
  by_cases h_select : opcode = code.OP_SELECT
  · subst opcode
    rw [code.step_select.dispatch]
    exact run_scalar st _ _ v (ScalarReaders.select st  hs hsize)
      (fun s a => hvisitor.on_select v s a)
  by_cases h_local_get : opcode = code.OP_LOCAL_GET
  · subst opcode
    rw [code.step_local_get.dispatch]
    exact run_scalar st _ _ v (ScalarReaders.local_get st data ctx hs hsize)
      (fun s a => hvisitor.on_local_get v s a)
  by_cases h_local_set : opcode = code.OP_LOCAL_SET
  · subst opcode
    rw [code.step_local_set.dispatch]
    exact run_scalar st _ _ v (ScalarReaders.local_set st data ctx hs hsize)
      (fun s a => hvisitor.on_local_set v s a)
  by_cases h_local_tee : opcode = code.OP_LOCAL_TEE
  · subst opcode
    rw [code.step_local_tee.dispatch]
    exact run_scalar st _ _ v (ScalarReaders.local_tee st data ctx hs hsize)
      (fun s a => hvisitor.on_local_tee v s a)
  by_cases h_global_get : opcode = code.OP_GLOBAL_GET
  · subst opcode
    rw [code.step_global_get.dispatch]
    exact run_scalar st _ _ v (ScalarReaders.global_get st data env hs hsize)
      (fun s a => hvisitor.on_global_get v s a)
  by_cases h_global_set : opcode = code.OP_GLOBAL_SET
  · subst opcode
    rw [code.step_global_set.dispatch]
    exact run_scalar st _ _ v (ScalarReaders.global_set st data env hs hsize)
      (fun s a => hvisitor.on_global_set v s a)
  by_cases h_memory_size : opcode = code.OP_MEMORY_SIZE
  · subst opcode
    rw [code.step_memory_size.dispatch]
    exact run_scalar st _ _ v (ScalarReaders.memory_size st data env hs hsize)
      (fun s _ => hvisitor.on_memory_size v s)
  by_cases h_memory_grow : opcode = code.OP_MEMORY_GROW
  · subst opcode
    rw [code.step_memory_grow.dispatch]
    exact run_scalar st _ _ v (ScalarReaders.memory_grow st data env hs hsize)
      (fun s _ => hvisitor.on_memory_grow v s)
  have hreserved : (0x06 ≤ opcode.val ∧ opcode.val ≤ 0x0A) ∨
      (0x12 ≤ opcode.val ∧ opcode.val ≤ 0x19) ∨
      (0x1C ≤ opcode.val ∧ opcode.val ≤ 0x1F) ∨
      (0x25 ≤ opcode.val ∧ opcode.val ≤ 0x27) := by
    simp only [controlOpcodes, List.mem_cons, not_or] at hscalar
    simp only [global_simps] at *
    scalar_tac
  rw [code.step.reserved visitor st data env ctx opcode v hreserved]
  simp [hs]

end Itasca.MultiValue
