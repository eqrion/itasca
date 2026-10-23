import Exec.Code.Local.Callbacks.Common.CompilerMetadata
namespace Exec.Code
open Aeneas Aeneas.Std
open Itasca.ResultFacts

/-- Ordinary instructions leave the frame stack and its control-map entries fixed. -/
def compilerOrdinaryMetadata {A : Type} (compiler : runtime.compiler.FunctionCompiler A) :=
  (compilerMetadata compiler, compiler.frames, compiler.function.controls)

structure CompilerOrdinaryStable {A : Type} (before after : runtime.compiler.FunctionCompiler A) : Prop where
  metadata : compilerOrdinaryMetadata after = compilerOrdinaryMetadata before
  capacity : before.function.slot_count.val ≤ after.function.slot_count.val

theorem CompilerOrdinaryStable.refl {A : Type} (compiler : runtime.compiler.FunctionCompiler A) :
    CompilerOrdinaryStable compiler compiler := ⟨rfl, Nat.le_refl _⟩

theorem CompilerOrdinaryStable.trans {A : Type} {before middle after : runtime.compiler.FunctionCompiler A}
    (first : CompilerOrdinaryStable before middle) (second : CompilerOrdinaryStable middle after) :
    CompilerOrdinaryStable before after := ⟨second.metadata.trans first.metadata, first.capacity.trans second.capacity⟩

theorem CompilerOrdinaryStable.stable {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (stable : CompilerOrdinaryStable before after) : CompilerStable before after :=
  ⟨congrArg Prod.fst stable.metadata, stable.capacity⟩

theorem CompilerOrdinaryStable.frames {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (stable : CompilerOrdinaryStable before after) : after.frames = before.frames :=
  congrArg (fun metadata => metadata.2.1) stable.metadata

theorem CompilerOrdinaryStable.controls {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (stable : CompilerOrdinaryStable before after) : after.function.controls = before.function.controls :=
  congrArg (fun metadata => metadata.2.2) stable.metadata

theorem Emitted.ordinary_stable {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {instruction} (emitted : Emitted before after instruction) : CompilerOrdinaryStable before after := by
  obtain ⟨budget, code, sources, rfl, _, _⟩ := emitted
  exact ⟨rfl, Nat.le_refl _⟩

/-- A successful observation preserves fixed metadata and only increases the
slot capacity. Its allocation decisions and current validator operands vary freely. -/
theorem compiler_observe_ordinary_stable {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (accepted : runtime.compiler.FunctionCompiler.observe ops before state = .ok (.Ok (), after)) :
    CompilerOrdinaryStable before after := by
  have frame := compiler_observe_frame ops law before state
  rw [accepted, WP.spec_ok] at frame
  have measures := compiler_observe_measures ops law before state
  rw [accepted, WP.spec_ok] at measures
  constructor
  · simpa only [ObserveFrame, compilerOrdinaryMetadata, compilerMetadata] using congrArg compilerOrdinaryMetadata frame
  · rw [(measures rfl).2]
    split
    · exact Nat.le_max_left _ _
    · exact Nat.le_refl _

end Exec.Code
