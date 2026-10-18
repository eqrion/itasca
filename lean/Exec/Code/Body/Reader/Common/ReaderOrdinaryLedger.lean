import Exec.Code.Body.Reader.Common.ReaderOpcodePartition
import Exec.Code.Body.Reader.Common.ReaderAuxiliaryGrowth
import Exec.Code.Body.Reader.Common.ReaderOrdinaryFixups
import Exec.Code.Body.Reader.Common.ReaderOrdinaryFixupsWasm1
import Exec.Code.Body.Reader.Common.ReaderExtraFixups
import Exec.Code.Body.Reader.Common.ReaderExtraFixupsWasm1
import Exec.Code.Body.Reader.Common.ReaderExtendedFixups
import Exec.Code.Body.Reader.Common.ReaderOpcodeClassification
import Exec.Code.Body.Reader.Common.ReaderMiscAccepted
import Exec.Code.Body.Reader.Simd.ReaderSimdEventDispatch
import Exec.Code.Body.Lowering.Float.FloatWasm1Exclusion
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Successful ordinary readers charge auxiliary entries and retain the
per-frame branch-fixup allocation budget. -/
structure ReaderAllocationLedger {A} (before after : runtime.compiler.FunctionCompiler A) : Prop where
  auxiliary : AuxiliaryGrowth before after
  fixups : FixupBudget before.frames.val before.function.code.val.length →
    FixupBudget after.frames.val after.function.code.val.length

theorem ReaderAllocationLedger.bounded {A} {before after : runtime.compiler.FunctionCompiler A}
    (ledger : ReaderAllocationLedger before after)
    (indirect : before.function.indirect.val.length ≤ before.function.code.val.length)
    (simd : before.function.simd.val.length ≤ before.function.code.val.length)
    (pool : before.function.v128_pool.val.length ≤ before.function.code.val.length)
    (fixups : FixupBudget before.frames.val before.function.code.val.length) :
    after.function.indirect.val.length ≤ after.function.code.val.length ∧
    after.function.simd.val.length ≤ after.function.code.val.length ∧
    after.function.v128_pool.val.length ≤ after.function.code.val.length ∧
    FixupBudget after.frames.val after.function.code.val.length := by
  obtain ⟨i,s,p⟩ := ledger.auxiliary.bounded indirect simd pool
  exact ⟨i,s,p,ledger.fixups fixups⟩

private theorem ordinary_of_slice {opcode : U8} (slice : SliceOpcode opcode)
    (excluded : opcode.val ∉ [2,3,4,5,11,12,13,14,15]) : opcode ∈ readerOrdinaryOpcodes := by
  rcases slice.partition with ordinary | scope | else_ | end_
  · exact ordinary
  · simp only [ScopeOpcode,List.mem_cons,List.not_mem_nil,or_false] at scope excluded
    tauto
  · simp [else_] at excluded
  · simp [end_] at excluded

/-- Every accepted ordinary Wasm 2 profile step preserves the allocation ledger.
Recognition is derived from this actual step, including decoded prefix bytes. -/
theorem reader_ordinary_ledger_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (contextLocals : ctx.locals = locals) (opcode : U8)
    (excluded : opcode.val ∉ [2,3,4,5,11,12,13,14,15])
    (byte : data.val[p.start.val]'p.inbounds = opcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 opcode before = .ok (.Ok (),out,after)) :
    ReaderAllocationLedger before after := by
  have known := reader_accepted_opcode_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx index opcode before after accepted
  rcases known with cumulative | simd | table | select
  · rcases cumulative with floatCore | stateful | indirect
    · rcases floatCore with core | float | misc
      · rcases core with slice | extra
        · have ordinary := ordinary_of_slice slice excluded
          exact ⟨reader_ordinary_auxiliary_growth_wasm2 p ops law before after out ctx contextLocals opcode ordinary byte accepted,
            reader_ordinary_fixup_budget_wasm2 p ops law before after out ctx contextLocals opcode ordinary byte accepted⟩
        · exact ⟨reader_core_extra_auxiliary_growth_wasm2 p ops law before after out ctx contextLocals opcode extra byte accepted,
            reader_core_extra_fixup_budget_wasm2 p ops law before after out ctx contextLocals opcode extra byte accepted⟩
      · obtain ⟨op,base,equal⟩ := float_base_opcode_of_mem float
        rw [←equal] at byte accepted
        exact ⟨reader_float_base_auxiliary_growth_wasm2 p ops law before after out ctx contextLocals op base byte accepted,
          reader_float_base_fixup_budget_wasm2 p ops law before after out ctx contextLocals op base byte accepted⟩
      · rw [misc] at byte accepted
        obtain ⟨sub,next,decoded,choice⟩ := reader_misc_accepted
          (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx index before after accepted
        rcases choice with ⟨op,extension,equal⟩ | bulk
        · exact ⟨reader_saturating_auxiliary_growth_wasm2 p ops law before after out ctx op extension sub next equal decoded byte accepted,
            reader_saturating_fixup_budget_wasm2 p ops law before after out ctx op extension sub next equal decoded byte accepted⟩
        · exact ⟨reader_stateful_bulk_auxiliary_growth_wasm2 p ops law before after out ctx sub next bulk byte decoded accepted,
            reader_stateful_bulk_fixup_budget_wasm2 p ops law before after out ctx sub next bulk byte decoded accepted⟩
    · exact ⟨reader_stateful_base_auxiliary_growth_wasm2 p ops law before after out ctx opcode stateful byte accepted,
        reader_stateful_base_fixup_budget_wasm2 p ops law before after out ctx opcode stateful byte accepted⟩
    · rw [indirect] at byte accepted
      exact ⟨reader_indirect_call_auxiliary_growth_wasm2 p ops law before after out ctx byte accepted,
        reader_indirect_call_fixup_budget_wasm2 p ops law before after out ctx byte accepted⟩
  · rw [simd] at byte accepted
    obtain ⟨event⟩ := reader_simd_event_wasm2 p ops before after out ctx
      (EnvTranslation.context env ⟨locals,p.ft.results⟩) rfl byte accepted
    exact ⟨event.auxiliary_growth law,event.fixup_budget law⟩
  · simp [table] at excluded
  · rw [select] at byte accepted
    exact ⟨reader_typed_select_auxiliary_growth_wasm2 p ops law before after out ctx byte accepted,
      reader_typed_select_fixup_budget_wasm2 p ops law before after out ctx byte accepted⟩

/-- The Wasm 1 step has the same ledger, including direct and indirect calls. -/
theorem reader_ordinary_ledger_wasm1 {data env ctx bodyBt st}
    (p : Wasm1.Pending data env ctx bodyBt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (opcode : U8) (excluded : opcode.val ∉ [2,3,4,5,11,12,13,14,15])
    (byte : data.val[p.start.val]'p.inbounds = opcode)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx opcode before = .ok (.Ok (),out,after)) :
    ReaderAllocationLedger before after := by
  have known := reader_accepted_opcode_wasm1
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx opcode before after accepted
  rcases known with floatCore | memory | indirect | table
  · rcases floatCore with core | float | misc
    · rcases core with slice | extra
      · have ordinary := ordinary_of_slice slice excluded
        exact ⟨reader_ordinary_auxiliary_growth_wasm1 p ops law before after out opcode ordinary byte accepted,
          reader_ordinary_fixup_budget_wasm1 p ops law before after out opcode ordinary byte accepted⟩
      · exact ⟨reader_core_extra_auxiliary_growth_wasm1 p ops law before after out opcode extra byte accepted,
          reader_core_extra_fixup_budget_wasm1 p ops law before after out opcode extra byte accepted⟩
    · obtain ⟨op,base,equal⟩ := float_base_opcode_of_mem float
      rw [←equal] at byte accepted
      exact ⟨reader_float_base_auxiliary_growth_wasm1 p ops law before after out op base byte accepted,
        reader_float_base_fixup_budget_wasm1 p ops law before after out op base byte accepted⟩
    · rw [misc] at accepted
      exact False.elim (float_saturating_wasm1_impossible
        (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after st out data env ctx accepted)
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at memory
    rcases memory with size | grow
    · have equal : opcode = 63#u8 := UScalar.eq_of_val_eq size
      rw [equal] at accepted
      exact ⟨reader_memory_size_auxiliary_growth_wasm1 ops law before after st out data env ctx accepted,
        reader_memory_size_fixup_budget_wasm1 ops law before after st out data env ctx accepted⟩
    · have equal : opcode = 64#u8 := UScalar.eq_of_val_eq grow
      rw [equal] at accepted
      exact ⟨reader_memory_grow_auxiliary_growth_wasm1 ops law before after st out data env ctx accepted,
        reader_memory_grow_fixup_budget_wasm1 ops law before after st out data env ctx accepted⟩
  · rw [indirect] at byte accepted
    exact ⟨reader_indirect_call_auxiliary_growth_wasm1 p ops law before after out byte accepted,
      reader_indirect_call_fixup_budget_wasm1 p ops law before after out byte accepted⟩
  · simp [table] at excluded

/-- Lift the Wasm 1 ledger through actual profile dispatch, retaining its exact
returned compiler without a separate reader-success premise. -/
theorem reader_profile_ordinary_ledger_wasm1 {data env ctx bodyBt st}
    (p : Wasm1.Pending data env ctx bodyBt st.core) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (index : U32)
    (opcode : U8) (excluded : opcode.val ∉ [2,3,4,5,11,12,13,14,15])
    (byte : data.val[p.start.val]'p.inbounds = opcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm1 opcode before = .ok (.Ok (),out,after)) :
    ReaderAllocationLedger before after := by
  unfold code.step_profile at accepted
  obtain ⟨⟨reply,state,changed⟩,run,rest⟩ := ResultFacts.bind_ok_inv _ _ _ accepted
  simp only [Std.uncurry,Result.ok.injEq,Prod.mk.injEq] at rest
  obtain ⟨replyEq,states,changedEq⟩ := rest
  rw [replyEq,changedEq] at run
  exact reader_ordinary_ledger_wasm1 p ops law before after state opcode excluded byte run
end Exec.Code
