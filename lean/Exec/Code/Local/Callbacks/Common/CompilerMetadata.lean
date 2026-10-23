import Exec.Code.Local.Callbacks.Common.ObserveFrame
import Exec.Code.Local.Callbacks.Common.ObserveMeasures
import Exec.Code.Local.Callbacks.Common.Finish
import Exec.Code.Local.Callbacks.Common.Fixups
namespace Exec.Code
open Aeneas Aeneas.Std
open Itasca.ResultFacts

/-- Source and local-layout metadata fixed after the function-start callback.
Instruction emission and control-flow patching may change work buffers only. -/
def compilerMetadata {A : Type} (compiler : runtime.compiler.FunctionCompiler A) :=
  (compiler.signatures, compiler.func_param_slots, compiler.batch_start,
    compiler.function.type_index, compiler.function.locals, compiler.function.param_slots,
    compiler.function.local_slots, compiler.function.body_start, compiler.function.body_end,
    compiler.local_offsets)

structure CompilerStable {A : Type} (before after : runtime.compiler.FunctionCompiler A) : Prop where
  metadata : compilerMetadata after = compilerMetadata before
  capacity : before.function.slot_count.val ≤ after.function.slot_count.val

theorem CompilerStable.refl {A : Type} (compiler : runtime.compiler.FunctionCompiler A) :
    CompilerStable compiler compiler := ⟨rfl, Nat.le_refl _⟩

theorem CompilerStable.trans {A : Type} {before middle after : runtime.compiler.FunctionCompiler A}
    (first : CompilerStable before middle) (second : CompilerStable middle after) :
    CompilerStable before after := ⟨second.metadata.trans first.metadata, first.capacity.trans second.capacity⟩

theorem CompilerStable.fields {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (stable : CompilerStable before after) :
    after.signatures = before.signatures ∧ after.func_param_slots = before.func_param_slots ∧
    after.batch_start = before.batch_start ∧ after.function.type_index = before.function.type_index ∧
    after.function.locals = before.function.locals ∧ after.function.param_slots = before.function.param_slots ∧
    after.function.local_slots = before.function.local_slots ∧ after.function.body_start = before.function.body_start ∧
    after.function.body_end = before.function.body_end ∧ after.local_offsets = before.local_offsets := by
  simpa only [compilerMetadata, Prod.mk.injEq] using stable.metadata

theorem Emitted.stable {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {instruction} (emitted : Emitted before after instruction) : CompilerStable before after := by
  obtain ⟨budget, code, sources, rfl, _, _⟩ := emitted
  exact ⟨rfl, Nat.le_refl _⟩

/-- A successful observation preserves fixed metadata and only increases the
slot capacity. Its allocation decisions and current validator operands vary freely. -/
theorem compiler_observe_stable {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (accepted : runtime.compiler.FunctionCompiler.observe ops before state = .ok (.Ok (), after)) :
    CompilerStable before after := by
  have frame := compiler_observe_frame ops law before state
  rw [accepted, WP.spec_ok] at frame
  have measures := compiler_observe_measures ops law before state
  rw [accepted, WP.spec_ok] at measures
  constructor
  · simpa only [ObserveFrame, compilerMetadata] using congrArg compilerMetadata frame
  · rw [(measures rfl).2]
    split
    · exact Nat.le_max_left _ _
    · exact Nat.le_refl _

end Exec.Code
