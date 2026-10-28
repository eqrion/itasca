import Exec.Code.Local.Source.SourceBudget
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- One control map is allocated for function entry and at most one for each
consumed source byte. Every physical frame refers to an allocated map. -/
structure SourceControlBudget {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (position : Nat) : Prop where
  maps : compiler.function.controls.val.length ≤ position + 1
  frames : compiler.frames.val.length ≤ compiler.function.controls.val.length

theorem SourceControlBudget.initial {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    (maps : compiler.function.controls.val.length = 1)
    (frames : compiler.frames.val.length = 1) : SourceControlBudget compiler 0 := by
  constructor <;> omega

theorem SourceControlBudget.transport {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {position : Nat} (budget : SourceControlBudget before position)
    (maps : after.function.controls.val.length = before.function.controls.val.length)
    (frames : after.frames.val.length ≤ before.frames.val.length) : SourceControlBudget after position := by
  constructor
  · rw [maps]; exact budget.maps
  · rw [maps]; exact frames.trans budget.frames

theorem SourceControlBudget.advance {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    {start finish : Nat} (budget : SourceControlBudget compiler start)
    (consumed : start ≤ finish) : SourceControlBudget compiler finish := by
  exact ⟨budget.maps.trans (by omega), budget.frames⟩

/-- Entering a structured instruction consumes an opcode byte before adding
its map and frame. Dormant scopes use the same accounting. -/
theorem SourceControlBudget.enter {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {start finish : Nat} (budget : SourceControlBudget before start)
    (maps : after.function.controls.val.length = before.function.controls.val.length + 1)
    (frames : after.frames.val.length = before.frames.val.length + 1)
    (consumed : start < finish) : SourceControlBudget after finish := by
  constructor
  · have bound := budget.maps; omega
  · have bound := budget.frames; omega

theorem SourceControlBudget.capacities {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    {position : Nat} (budget : SourceControlBudget compiler position)
    (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val) :
    compiler.function.controls.val.length < Usize.max ∧ compiler.frames.val.length < Usize.max := by
  have bound := budget.maps
  have nested := budget.frames
  have wordBound : U32.max ≤ Usize.max := by scalar_tac
  norm_num [limits.MAX_MODULE_BYTES, U32.max_eq] at sourceBound wordBound
  omega
end Itasca.Runtime.Code
