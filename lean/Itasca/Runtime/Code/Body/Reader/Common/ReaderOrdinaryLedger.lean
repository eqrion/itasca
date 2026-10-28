import Itasca.Runtime.Code.Body.Reader.Common.ReaderCompilerOrdinary
import Itasca.Runtime.Code.Body.Reader.Control.ReaderCompilerScopes
import Itasca.Runtime.Code.Body.Reader.Common.ReaderAuxiliaryGrowth
import Itasca.Runtime.Code.Body.Reader.Common.ReaderOrdinaryEffects
import Itasca.Runtime.Code.Body.Reader.Common.ReaderExtendedFixups
import Itasca.Runtime.Code.Body.Reader.Common.ReaderOpcodeClassification
import Itasca.Runtime.Code.Body.Reader.Common.ReaderMiscAccepted
import Itasca.Runtime.Code.Body.Reader.Simd.ReaderSimdEventDispatch
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Successful ordinary readers charge auxiliary entries and retain the
per-frame branch-fixup allocation budget. -/
structure ReaderAllocationLedger {A} (before after : runtime.compiler.FunctionCompiler A) : Prop where
  auxiliary : AuxiliaryGrowth before after
  fixups : FixupBudget before.frames.val before.function.code.val.length →
    FixupBudget after.frames.val after.function.code.val.length

theorem OrdinaryEffects.ledger {A} {before after : runtime.compiler.FunctionCompiler A}
    {state : code.OpIterState} (effects : OrdinaryEffects before after state) : ReaderAllocationLedger before after :=
  ⟨effects.auxiliary_growth, effects.fixups⟩

private theorem scope_excluded {opcode : U8} (scope : ScopeOpcode opcode)
    (excluded : opcode.val ∉ [2,3,4,5,11,12,13,14,15]) : False := by
  simp only [ScopeOpcode,List.mem_cons,List.not_mem_nil,or_false] at scope excluded
  omega

/-- Every accepted ordinary Wasm 2 profile step preserves the allocation ledger.
Recognition is derived from this actual step, including decoded prefix bytes. -/
theorem reader_ordinary_ledger_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (opcode : U8) (excluded : opcode.val ∉ [2,3,4,5,11,12,13,14,15])
    (byte : data.val[p.start.val]'p.inbounds = opcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 opcode before = .ok (.Ok (),out,after)) :
    ReaderAllocationLedger before after := by
  have known := reader_accepted_opcode_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx index opcode before after accepted
  rcases known with ordinary | scope | isElse | isEnd | extra | float | memory | indirect | table |
    stateful | misc | simd | select
  · exact (reader_ordinary_effects_wasm2 p ops law before after out ctx opcode ordinary byte accepted).ledger
  · exact (scope_excluded scope excluded).elim
  · simp [isElse] at excluded
  · simp [isEnd] at excluded
  · exact (reader_scalar_effects_wasm2 ops law before after st out data env ctx index opcode extra accepted).ledger
  · obtain ⟨op,base,equal⟩ := float_base_opcode_of_mem float
    rw [←equal] at byte accepted
    exact (reader_float_base_effects_wasm2 ops law before after st out data env ctx index op base accepted).ledger
  · have stateful := stateful_opcode_values (.inl memory)
    exact ⟨reader_stateful_base_auxiliary_growth_wasm2 p ops law before after out ctx opcode stateful byte accepted,
      reader_stateful_base_fixup_budget_wasm2 p ops law before after out ctx opcode stateful byte accepted⟩
  · rw [indirect] at byte accepted
    exact ⟨reader_indirect_call_auxiliary_growth_wasm2 p ops law before after out ctx byte accepted,
      reader_indirect_call_fixup_budget_wasm2 p ops law before after out ctx byte accepted⟩
  · simp [table] at excluded
  · have stateful := stateful_opcode_values (.inr stateful)
    exact ⟨reader_stateful_base_auxiliary_growth_wasm2 p ops law before after out ctx opcode stateful byte accepted,
      reader_stateful_base_fixup_budget_wasm2 p ops law before after out ctx opcode stateful byte accepted⟩
  · rw [misc] at byte accepted
    obtain ⟨sub,next,decoded,choice⟩ := reader_misc_accepted
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx index before after accepted
    rcases choice with ⟨op,extension,equal⟩ | bulk
    · exact (reader_saturating_effects_wasm2 p ops law before after out ctx op extension sub next equal decoded byte accepted).ledger
    · exact ⟨reader_stateful_bulk_auxiliary_growth_wasm2 p ops law before after out ctx sub next bulk byte decoded accepted,
        reader_stateful_bulk_fixup_budget_wasm2 p ops law before after out ctx sub next bulk byte decoded accepted⟩
  · rw [simd] at byte accepted
    obtain ⟨event⟩ := reader_simd_event_wasm2 p ops before after out ctx
      (EnvTranslation.context env ⟨locals,p.ft.results⟩) rfl byte accepted
    exact ⟨event.auxiliary_growth law,event.fixup_budget law⟩
  · rw [select] at byte accepted
    exact ⟨reader_typed_select_auxiliary_growth_wasm2 p ops law before after out ctx byte accepted,
      reader_typed_select_fixup_budget_wasm2 p ops law before after out ctx byte accepted⟩

end Itasca.Runtime.Code
