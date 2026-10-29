import Itasca.Runtime.Compiler.Local.Capacity.AuxiliaryGrowth
import Itasca.Runtime.Compiler.Local.Capacity.StatefulAuxiliaryGrowth
import Itasca.Runtime.Compiler.Local.Capacity.SimdAuxiliaryGrowth
import Itasca.Runtime.Compiler.Body.Reader.Replay.OrdinaryEffects
import Itasca.Runtime.Compiler.Body.Reader.Stateful.ExtendedCodeMonotone
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulEffects
import Itasca.Runtime.Compiler.Local.Relations.Calls.IndirectCallMetadata
import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.FixupPreservation
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerTerminalMetadata
import Itasca.Runtime.Compiler.Local.Callbacks.CodeGrowth.CompilerCodeMonotoneStateful
import Itasca.Runtime.Compiler.Local.Callbacks.Simd.CompilerCodeMonotoneSimd
import Itasca.Runtime.Compiler.Local.Callbacks.CodeGrowth.CompilerCodeMonotoneScalar
import Itasca.Runtime.Compiler.Body.Reader.Stateful.StatefulBase
import Itasca.Runtime.Compiler.Body.Reader.Stateful.StatefulBulkDispatch
import Itasca.Runtime.Compiler.Body.Reader.Calls.Instructions
import Itasca.Runtime.Compiler.Body.Reader.References.TypedSelect
import Itasca.Runtime.Compiler.Body.Reader.Simd.SimdEvent
import Itasca.Runtime.Compiler.Local.Relations.Syntax.ReaderOpcode
import Itasca.Runtime.Compiler.Local.Lowering.Integer.NumericEncoding
import Itasca.Runtime.Compiler.Body.Callbacks.Prefix.CompilerPrefix
import Itasca.Runtime.Compiler.Body.Reader.Scalar.SignEmissions
import Itasca.Runtime.Compiler.Body.Reader.Replay.Span
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerDeadMetadata
import Itasca.Runtime.Compiler.Local.Source.SourceCursor
import Itasca.Runtime.Compiler.Local.Relations.Operations.DeadCode
import Itasca.Runtime.Compiler.Body.Reader.Replay.ProfileAgreement
import Itasca.Runtime.Compiler.Local.Relations.Stacks.KnownPopStack
import Itasca.Runtime.Compiler.Local.Relations.Stacks.KnownNumericStack
import Itasca.Runtime.Compiler.Body.Reader.Scalar.SignExtension
import Itasca.Runtime.Compiler.Body.Reader.Control.Boundary
import Itasca.Runtime.Compiler.Body.Reader.Control.ScopeFronts
import Itasca.Runtime.Compiler.Body.Reader.Control.ReachabilitySteps
import Itasca.Runtime.Compiler.Body.Reader.Scalar.NumericEmissions
import Itasca.Runtime.Compiler.Body.Reader.Scalar.IntegerFacts
import Itasca.Runtime.Compiler.Body.Reader.Scalar.Emissions
import Itasca.Runtime.Compiler.Body.Reader.Scalar.Empty
import Itasca.Runtime.Compiler.Local.Lowering.Literal.LiteralSources
import Itasca.Runtime.Compiler.Local.Source.SourceLengthsTactic
import Itasca.Runtime.Compiler.Local.Lowering.Integer.LoweringArithmetic
import Itasca.Runtime.Compiler.Local.Lowering.Local.LoweringLocal
import Itasca.Runtime.Compiler.Local.Lowering.Literal.LiteralCursor
import Itasca.Runtime.Compiler.Local.Source.SourceCursorTactic
import Itasca.Runtime.Compiler.Body.Source.TypedLowering
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerLiteralMetadata
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerMetadataTactic
import Itasca.Runtime.Compiler.Body.Reader.Local.LocalEmissions
import Itasca.Runtime.Compiler.Body.Reader.Local.LocalEffects
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalPrefix
import Itasca.Runtime.Compiler.Body.Reader.Calls.CallLowering
import Itasca.Support.EnvTranslation
import Itasca.Runtime.Compiler.Body.Reader.Calls.CallEffects
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CallbackSources
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CallbackCursor
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerOrdinaryResults
import Itasca.Runtime.Compiler.Local.Capacity.EmissionGrowth
import Itasca.Runtime.Compiler.Body.Reader.Scalar.Unreachable
import Itasca.Runtime.Compiler.Local.Lowering.Control.LoweringReturn
import Itasca.Runtime.Compiler.Local.Relations.Control.KnownControlStack
import Itasca.Runtime.Compiler.Body.Reader.Control.ReturnStack
import Itasca.Runtime.Compiler.Body.Reader.Control.RootFrame
import Itasca.Runtime.Compiler.Body.Reader.Control.ControlBoundary
import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.FramePlanPop
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ElseFrames
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.ScopeCallbackEnter
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlEntrySuccess
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerEnterMetadata
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlCursor
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlSources
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlObservedLayout
import Itasca.Runtime.Compiler.Body.Callbacks.Calls.ScopeCallbackInputs
import Itasca.Runtime.Compiler.Body.Reader.Control.Reachability
import Itasca.Runtime.Compiler.Body.Reader.Control.FrontTransitions
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalDormant
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.ScopeCallbackDead
import Itasca.Runtime.Compiler.Body.Reader.Control.EnterWasm2
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.ScopeCallbackIf
import Itasca.Runtime.Compiler.Body.Reader.Control.BranchLayout
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalConditional
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ElseEvidence
import Itasca.Runtime.Compiler.Local.Relations.Calls.BranchSuccessCallbacks
import Itasca.Runtime.Compiler.Local.Relations.Control.BranchSuccessControls
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CompilerCallbackMetadata
import Itasca.Runtime.Compiler.Body.Reader.Replay.Post
import Itasca.Runtime.Compiler.Local.Source.SourceStacks
import Itasca.Runtime.Compiler.Body.Reader.Control.BranchWasm2
import Itasca.Runtime.Compiler.Body.Relations.Control.BranchIfLayout
import Itasca.Runtime.Compiler.Local.Relations.Control.BranchReachable
import Itasca.Runtime.Compiler.Local.Relations.Calls.BranchSuccessConditionalCallbacks
import Itasca.Runtime.Compiler.Body.Reader.Replay.OpcodeClassification
import Itasca.Runtime.Compiler.Body.Reader.Replay.BulkAndSaturatingAcceptance
import Itasca.Runtime.Compiler.Body.Reader.Simd.Dispatch

/-!
Allocation accounting for ordinary reader steps. Auxiliary-table growth and fixup budgets establish the ReaderAllocationLedger used by reached-body resource proofs.
-/

/-! ## Reader Auxiliary Growth -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

theorem reader_stateful_base_auxiliary_growth_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (opcode : U8)
    (member : opcode.val ∈ [37,38,63,64,208,209,210])
    (byte : data.val[p.start.val]'p.inbounds = opcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 opcode before = .ok (.Ok (),out,after)) :
    AuxiliaryGrowth before after := by
  obtain ⟨op,a,b,arguments,callback,_⟩ := reader_stateful_base_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx opcode member byte accepted
  rw [stateful_callback_lower ops before out.core op a b arguments] at callback
  exact compiler_stateful_auxiliary_growth ops law before after out.core op a b callback

theorem reader_stateful_bulk_auxiliary_growth_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (subopcode : U32) (next : Usize)
    (member : subopcode.val ∈ [8,9,10,11,12,13,14,15,16,17])
    (byte : data.val[p.start.val]'p.inbounds = 252#u8)
    (decoded : Leb128.Decoded data st.core.pos subopcode next)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 252#u8 before = .ok (.Ok (),out,after)) :
    AuxiliaryGrowth before after := by
  obtain ⟨op,a,b,arguments,callback,_⟩ := reader_stateful_bulk_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx subopcode next member byte decoded accepted
  rw [stateful_callback_lower ops before out.core op a b arguments] at callback
  exact compiler_stateful_auxiliary_growth ops law before after out.core op a b callback

theorem reader_indirect_call_auxiliary_growth_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 17#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 17#u8 before = .ok (.Ok (),out,after)) :
    AuxiliaryGrowth before after := by
  obtain ⟨idx,table,values,callback,rest⟩ := reader_indirect_call_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  exact compiler_indirect_auxiliary_growth ops law before after out.core idx table callback

theorem SimdReaderEvent.auxiliary_growth {A : Type} {ops : runtime.platform.Alloc A}
    {data env locals index st p before after out C}
    (event : @SimdReaderEvent A ops data env locals index st p before after out C)
    (law : Platform.AllocCorrect ops) : AuxiliaryGrowth before after := by
  have bound := event.meaning.opcode_bound
  have number := event.number
  obtain ⟨mono,simd,pool,indirect,_⟩ := compiler_lower_simd_auxiliary_growth ops law before after out
    event.opcode event.a event.b event.bits (by omega) (by omega) event.callback
  unfold AuxiliaryGrowth
  have same := congrArg (fun xs => xs.val.length) indirect
  omega

theorem reader_typed_select_auxiliary_growth_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 28#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 28#u8 before = .ok (.Ok (),out,after)) :
    AuxiliaryGrowth before after := by
  obtain ⟨ty,position,callback,rest⟩ := reader_typed_select_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  exact .of_tables (compiler_core_tables ops law before after out.core (.select true) callback)
    (compiler_core_code_mono ops law before after out.core (.select true) callback)
end Itasca.Runtime.Code

end

/-! ## Reader Extended Fixups -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Actual scalar/reference callbacks preserve previously emitted code slots. -/
theorem reader_stateful_base_fixup_budget_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (opcode : U8)
    (member : opcode.val ∈ [37,38,63,64,208,209,210])
    (byte : data.val[p.start.val]'p.inbounds = opcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 opcode before = .ok (.Ok (),out,after)) :
    FixupBudget before.frames.val before.function.code.val.length →
    FixupBudget after.frames.val after.function.code.val.length := by
  intro budget
  obtain ⟨op,a,b,arguments,callback,_⟩ := reader_stateful_base_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx opcode member byte accepted
  rw [stateful_callback_lower ops before out.core op a b arguments] at callback
  exact budget.ordinary (compiler_stateful_ordinary_result ops law before after out.core op a b (.Ok ()) callback)
    (compiler_stateful_code_mono ops law before after out.core op a b (.Ok ()) callback)

theorem reader_stateful_bulk_fixup_budget_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (subopcode : U32) (next : Usize)
    (member : subopcode.val ∈ [8,9,10,11,12,13,14,15,16,17])
    (byte : data.val[p.start.val]'p.inbounds = 252#u8)
    (decoded : Leb128.Decoded data st.core.pos subopcode next)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 252#u8 before = .ok (.Ok (),out,after)) :
    FixupBudget before.frames.val before.function.code.val.length →
    FixupBudget after.frames.val after.function.code.val.length := by
  intro budget
  obtain ⟨op,a,b,arguments,callback,_⟩ := reader_stateful_bulk_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx subopcode next member byte decoded accepted
  rw [stateful_callback_lower ops before out.core op a b arguments] at callback
  exact budget.ordinary (compiler_stateful_ordinary_result ops law before after out.core op a b (.Ok ()) callback)
    (compiler_stateful_code_mono ops law before after out.core op a b (.Ok ()) callback)

theorem reader_indirect_call_fixup_budget_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 17#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 17#u8 before = .ok (.Ok (),out,after)) :
    FixupBudget before.frames.val before.function.code.val.length →
    FixupBudget after.frames.val after.function.code.val.length := by
  intro budget
  obtain ⟨idx,table,values,callback,rest⟩ := reader_indirect_call_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  exact budget.ordinary (compiler_indirect_call_ordinary_result ops law before after out.core idx table (.Ok ()) callback)
    (compiler_indirect_call_code_mono ops law before after out.core idx table (.Ok ()) callback)

theorem reader_typed_select_fixup_budget_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 28#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 28#u8 before = .ok (.Ok (),out,after)) :
    FixupBudget before.frames.val before.function.code.val.length →
    FixupBudget after.frames.val after.function.code.val.length := by
  intro budget
  obtain ⟨ty,position,callback,rest⟩ := reader_typed_select_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  exact budget.ordinary (compiler_core_ordinary_result ops law before after out.core (.select true) (.Ok ()) callback)
    (compiler_core_code_mono ops law before after out.core (.select true) callback)

theorem SimdReaderEvent.fixup_budget {A : Type} {ops : runtime.platform.Alloc A}
    {data env locals index st p before after out C}
    (event : @SimdReaderEvent A ops data env locals index st p before after out C)
    (law : Platform.AllocCorrect ops) : FixupBudget before.frames.val before.function.code.val.length →
    FixupBudget after.frames.val after.function.code.val.length := by
  intro budget
  have bound := event.meaning.opcode_bound
  have number := event.number
  exact budget.ordinary
    (compiler_lower_simd_effects ops law before after out event.opcode event.a event.b event.bits
      (by omega) (by omega) event.callback).1
    (compiler_lower_simd_code_mono ops law before after out event.opcode event.a event.b event.bits
      (by omega) (by omega) event.callback)

end Itasca.Runtime.Code

end

/-! ## Reader Ordinary Ledger -/

section

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

end
