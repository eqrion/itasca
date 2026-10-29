import Itasca.Runtime.Compiler.Body.Reader.Control.ControlEffects
import Itasca.Runtime.Compiler.Body.Capacity.CapacityFoldWasm2
import Itasca.Runtime.Compiler.Body.Reader.Stateful.ExtendedFullCapacity
import Itasca.Runtime.Compiler.Body.Reader.Replay.OrdinaryEffects
import Itasca.Runtime.Compiler.Body.Reader.Simd.Dispatch
import Itasca.Runtime.Compiler.Local.Relations.Syntax.ReaderOpcode
import Itasca.Runtime.Compiler.Local.Relations.Syntax.BulkAndSaturatingEncoding
import Itasca.Runtime.Compiler.Body.Reader.Control.BranchTableCapacity
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CallbackSafety
import Itasca.Runtime.Compiler.Body.Relations.Entry.EntryCompilerInitial
import Itasca.Runtime.Compiler.Local.Callbacks.Function.Finish
import Itasca.Runtime.Compiler.Body.Capacity.FunctionCapacity

/-!
Executable function capacity from reader-step accounting through the typed body fold and entry witness. The final certificate bounds compiled slots by independently validated source demand.
-/

/-! ## Executable Capacity Fold Wasm2 -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- A successful reader step in a fully encoded body retains the exact local
layout and bounds slot growth by the canonical post-step operand stack. -/
theorem reader_executable_capacity_wasm2 {data env ctx index st source}
    (p : Wasm2.Pending data env .Wasm2 ctx.locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (encoded : Wasm2.BodyEncoding data source)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (data.val[p.start.val]'p.inbounds) before = .ok (.Ok (),out,after)) :
    CapacityStep before after out.core := by
  have allowed := encoded.next_reader_opcode p.consumed p.inbounds
  rcases allowed with ordinary | scope | isElse | isEnd | extra | floatBase | memory | indirect | table |
    stateful | prefixed | simd | select
  · exact (reader_ordinary_effects_wasm2 p ops law before after out ctx _ ordinary rfl accepted).capacity
  · exact (reader_control_effects_wasm2 ops law before after st out data env ctx index _ (.inl scope) accepted).capacity
  · exact (reader_control_effects_wasm2 ops law before after st out data env ctx index _ (.inr (.inl isElse)) accepted).capacity
  · exact (reader_control_effects_wasm2 ops law before after st out data env ctx index _ (.inr (.inr isEnd)) accepted).capacity
  · exact (reader_scalar_effects_wasm2 ops law before after st out data env ctx index _ extra accepted).capacity
  · obtain ⟨op,base,equal⟩ := float_base_opcode_of_mem floatBase
    rw [←equal] at accepted
    exact (reader_float_base_effects_wasm2 ops law before after st out data env ctx index op base accepted).capacity
  · exact reader_stateful_base_full_capacity_wasm2 p ops law before after out ctx _
      (stateful_opcode_values (.inl memory)) rfl accepted
  · rw [indirect] at accepted
    exact reader_indirect_call_full_capacity_wasm2 p ops law before after out ctx indirect accepted
  · rw [table] at accepted
    exact reader_table_capacity_wasm2 ops law before after st out data env ctx index accepted
  · exact reader_stateful_base_full_capacity_wasm2 p ops law before after out ctx _
      (stateful_opcode_values (.inr stateful)) rfl accepted
  · obtain ⟨sub,next,decoded,choice⟩ := encoded.next_misc p.consumed p.inbounds st.core.pos p.pos prefixed
    rw [prefixed] at accepted
    rcases choice with ⟨op,extension,subEq⟩ | bulk
    · exact (reader_saturating_effects_wasm2 p ops law before after out ctx op extension sub next subEq decoded
        prefixed accepted).capacity
    · exact reader_stateful_bulk_full_capacity_wasm2 p ops law before after out ctx sub next bulk prefixed decoded accepted
  · rw [simd] at accepted
    obtain ⟨event⟩ := reader_simd_event_wasm2 p ops before after out ctx
      (EnvTranslation.context env ctx) rfl simd accepted
    exact event.capacity_step law
  · rw [select] at accepted
    exact reader_typed_select_full_capacity_wasm2 p ops law before after out ctx select accepted

theorem TypedRunWasm2.executable_capacity_bound {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {data env ctx index st before after source}
    (run : TypedRunWasm2 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      data env ctx index st before after)
    (encoded : Wasm2.BodyEncoding data source) :
    ∃ samples, ValidatedStacksWasm2 data env ctx index st samples ∧
      after.function.local_slots = before.function.local_slots ∧
      after.function.slot_count.val ≤ max before.function.slot_count.val
        (before.function.local_slots.val + maximumStackWords samples) := by
  induction run with
  | done typed closed finished =>
    exact ⟨_, .done typed closed finished, rfl, Nat.le_max_left _ _⟩
  | @step st before next out middle after typed pending start advance called rest ih =>
    obtain ⟨samples, trace, localEq, upper⟩ := ih
    have capacity := reader_executable_capacity_wasm2 pending ops law before middle out encoded called
    obtain ⟨reply, erased⟩ := Wasm2.Visitor.step_transfer
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor FullVisitor.empty_accepts
      data env ctx ctx rfl index .Wasm2 _ {core := {st.core with pos := next}} out before () middle called
    cases reply
    refine ⟨st.core.vals.val :: samples, .step typed pending start advance erased trace,
      localEq.trans capacity.1, ?_⟩
    have observed := trace.head_width
    have stepBound := capacity.2
    rw [observedHeight_stackWords] at stepBound
    rw [capacity.1] at upper
    change after.function.slot_count.val ≤ max before.function.slot_count.val
      (before.function.local_slots.val + max (stackWords st.core.vals.val) (maximumStackWords samples))
    omega
end Itasca.Runtime.Code

end

/-! ## Executable Entry Capacity -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Actual body validation bounds the compiled frame storage by source locals
and the maximum word width of a source-only validation trace. -/
theorem witness_compiler_executable_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    {initial final : runtime.compiler.FunctionCompiler A} {data env index start finish profile}
    (w : CodeEntry.Witness (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      data env index start finish initial final profile)
    (facts : CompilerEntryFacts w.startedState env w.ctx w.typeIdx w.ft w.body)
    {source : List instr} (encoded : Profile.BodyEncoding profile w.body source)
    (compiled : runtime.bytecode.CompiledFunction) (budget : runtime.compiler.Budget A)
    (finished : runtime.compiler.FunctionCompiler.finish ops final (.Ok ()) = .ok (.Ok compiled, budget)) :
    ∃ samples, ValidatedStacksWasm2 w.body env w.ctx w.typeIdx (Wasm2.initial w.typeIdx) samples ∧
      compiled.slot_count.val ≤
        slots (w.ft.params.val.map Translate.valueType ++ (ModuleLocals.declared w.groups).map Translate.valueType) +
          maximumStackWords samples := by
  have run := witness_typed_steps w
  have width : w.startedState.function.local_slots.val =
      slots (w.ft.params.val.map Translate.valueType ++ (ModuleLocals.declared w.groups).map Translate.valueType) := by
    simpa only [compilerLocals, facts.locals, w.context_locals, List.map_append] using facts.localLayout.slots
  have same := (compiler_finish_accepted ops final (.Ok ()) compiled budget finished).2.1
  subst compiled
  obtain ⟨samples, trace, locals, bound⟩ := run.executable_capacity_bound ops law encoded.to_wasm2
  refine ⟨samples, trace, ?_⟩
  rw [facts.capacity, width] at bound
  exact bound.trans (max_le (Nat.le_add_right _ _) (Nat.le_refl _))

/-- The static capacity certificate needs no assumed compiler bound: initial
local layout and capacity follow from actual construction and function start. -/
theorem witness_compile_executable_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    {signatures : Slice runtime.compiler.Signature} {functionSlots : Slice U32}
    {budget : runtime.compiler.Budget A} {batchStart : Usize}
    {initial final : runtime.compiler.FunctionCompiler A} {data env index start finish profile}
    (w : CodeEntry.Witness (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      data env index start finish initial final profile)
    (signatureTable : SignatureSequence signatures.val env.types.val)
    (functionTable : functionSlots.val.map (fun word => word.val) =
      env.func_types.val.map (fun ft => slots (ft.params.val.map Translate.valueType)))
    (endFits : batchStart.val + finish.val ≤ Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart = .ok initial)
    {source : List instr} (encoded : Profile.BodyEncoding profile w.body source)
    (compiled : runtime.bytecode.CompiledFunction) (finalBudget : runtime.compiler.Budget A)
    (finished : runtime.compiler.FunctionCompiler.finish ops final (.Ok ()) = .ok (.Ok compiled, finalBudget)) :
    ∃ samples, ValidatedStacksWasm2 w.body env w.ctx w.typeIdx (Wasm2.initial w.typeIdx) samples ∧
      compiled.slot_count.val ≤
        slots (w.ft.params.val.map Translate.valueType ++ (ModuleLocals.declared w.groups).map Translate.valueType) +
          maximumStackWords samples := by
  have facts := (witness_compiler_start ops law w signatureTable functionTable endFits created).1
  exact witness_compiler_executable_capacity ops law w facts encoded compiled finalBudget finished
end Itasca.Runtime.Code

end

/-! ## Executable Function Capacity -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca
theorem witness_executable_function_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    {signatures : Slice runtime.compiler.Signature} {functionSlots : Slice U32}
    {budget : runtime.compiler.Budget A} {batchStart : Usize}
    {initial final : runtime.compiler.FunctionCompiler A} {data env index start finish profile}
    (w : CodeEntry.Witness (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      data env index start finish initial final profile)
    (signatureTable : SignatureSequence signatures.val env.types.val)
    (functionTable : functionSlots.val.map (fun word => word.val) =
      env.func_types.val.map (fun ft => slots (ft.params.val.map Translate.valueType)))
    (endFits : batchStart.val + finish.val ≤ Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart = .ok initial)
    {source : List instr} (encoded : Profile.BodyEncoding profile w.body source)
    (compiled : runtime.bytecode.CompiledFunction) (finalBudget : runtime.compiler.Budget A)
    (finished : runtime.compiler.FunctionCompiler.finish ops final (.Ok ()) = .ok (.Ok compiled, finalBudget)) :
    FunctionCapacity profile env w.typeIdx
      (.FUNC (.mk_uN w.typeIdx.val)
        ((ModuleLocals.declared w.groups).map Translate.valueType |>.map local.LOCAL) source) compiled := by
  obtain ⟨samples, trace, bound⟩ := witness_compile_executable_capacity ops law w signatureTable functionTable
    endFits created encoded compiled finalBudget finished
  refine ⟨_, ⟨w.ft, ModuleLocals.declared w.groups, w.body, w.ctx, source, samples,
    ?_, ?_, w.context_locals, w.context_results, encoded, trace, rfl⟩, ?_⟩
  · simp only [List.getElem?_eq_getElem w.type_lt, w.function_type]
  · simp only [List.map_map]
  · simpa only [List.map_append] using bound

end Itasca.Runtime.Code

end
