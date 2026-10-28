import Itasca.Runtime.Code.Body.Capacity.ExecutableCapacityFoldWasm2
import Itasca.Runtime.Code.Body.Relations.Common.EntryCompilerInitial
import Itasca.Runtime.Code.Local.Callbacks.Common.Finish
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
