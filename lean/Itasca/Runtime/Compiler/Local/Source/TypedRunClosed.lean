import Itasca.Runtime.Compiler.Local.Relations.Function.EntryTypedSteps
import Itasca.Runtime.Compiler.Local.Capacity.EmissionGrowth
import Itasca.Runtime.Compiler.Local.Source.TypedStepsWasm2

/-!
Sections, each formerly its own module: SourceBudget, SourceControlBudget, TypedRunClosed.
-/

/-! ## SourceBudget -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- The source byte budget pays for at most three emitted instructions per byte.
Branch-table depths are charged when their complete instruction is lowered. -/
def SourceCodeBudget {A : Type} (compiler : runtime.compiler.FunctionCompiler A) (position : Nat) : Prop :=
  compiler.function.code.val.length ≤ 3 * position

theorem SourceCodeBudget.initial {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    (empty : compiler.function.code.val = []) : SourceCodeBudget compiler 0 := by
  simp [SourceCodeBudget, empty]

/-- One ordinary or structured opcode pays for up to three emitted instructions. -/
theorem SourceCodeBudget.advance {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {start finish : Nat} (budget : SourceCodeBudget before start)
    (growth : after.function.code.val.length ≤ before.function.code.val.length + 3)
    (consumed : start < finish) : SourceCodeBudget after finish := by
  unfold SourceCodeBudget at *
  omega

/-- The table count and default-depth bytes cover the table instruction itself;
each target depth pays for its at-most-two-instruction branch stub. -/
theorem SourceCodeBudget.table {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {start finish targets : Nat} (budget : SourceCodeBudget before start)
    (growth : after.function.code.val.length ≤ before.function.code.val.length + 1 + 2 * targets)
    (consumed : start + targets + 1 ≤ finish) : SourceCodeBudget after finish := by
  unfold SourceCodeBudget at *
  omega

/-- The existing module byte cap leaves room for all emitted instruction PCs. -/
theorem SourceCodeBudget.fetch_bound {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    {position : Nat} (budget : SourceCodeBudget compiler position)
    (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val) :
    compiler.function.code.val.length < U32.max := by
  unfold SourceCodeBudget at budget
  norm_num [limits.MAX_MODULE_BYTES, U32.max_eq] at *
  omega

/-- The same source budget discharges the extracted vector append capacity. -/
theorem SourceCodeBudget.code_capacity {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    {position : Nat} (budget : SourceCodeBudget compiler position)
    (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val) :
    compiler.function.code.val.length < Usize.max := by
  have fetchBound := budget.fetch_bound sourceBound
  have wordBound : U32.max ≤ Usize.max := by scalar_tac
  omega
end Itasca.Runtime.Compiler

end

/-! ## SourceControlBudget -/

section

namespace Itasca.Runtime.Compiler
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
end Itasca.Runtime.Compiler

end

/-! ## TypedRunClosed -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem TypedRunWasm2.closed {V : Type} {visitor : code.OpVisitor V}
    {data env ctx index st before after}
    (run : TypedRunWasm2 visitor data env ctx index st before after)
    (closed : st.blocks.val = []) : after = before ∧ st.core.pos = Slice.len data := by
  cases run with
  | done typed empty finished => exact ⟨rfl, finished⟩
  | step typed pending start advance called rest =>
    obtain ⟨_, _, _, _, _, _, _, blocks, _⟩ := pending.opened
    simp only [code.BodyState.blocks] at closed blocks
    rw [closed] at blocks
    simp at blocks
end Itasca.Runtime.Compiler

end
