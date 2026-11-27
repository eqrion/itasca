import Itasca.Runtime.Compiler.Local.Relations.Function.EntryTypedSteps
import Itasca.Runtime.Compiler.Local.Capacity.EmissionGrowth
import Itasca.Runtime.Compiler.Local.Source.TypedSteps

/-!
Proofs for Runtime / Compiler / Local / Source.

This module collects SourceStacks, TypedRunClosed.
Each section documents its contracts and consumers.
-/

/-! ## SourceStacks -/

section

/-!
# Concrete source operand stacks

Reachable compiler prefixes retain concrete validator operands. This invariant comes from actual reader steps; source typing alone does not establish the concrete stack representation.
-/
namespace Itasca.Compiler
open Aeneas Aeneas.Std
open Itasca

/-- A reachable compiler prefix retains concrete validator operands. This is
an invariant of actual steps, not a consequence of source typing alone. -/
def ConcreteStack (values : List code.StackType) : Prop :=
  ∀ value ∈ values, value ≠ .Bot

theorem concrete_stack_iff (values : List code.StackType) :
    ConcreteStack values ↔ ∃ types : List Itasca.wasm_types.ValueType, values = types.map code.StackType.Val := by
  induction values with
  | nil => simp [ConcreteStack]
  | cons value rest ih =>
    cases value with
    | Bot =>
      simp only [ConcreteStack, List.mem_cons, forall_eq_or_imp, ne_eq, not_true_eq_false, false_and, false_iff, not_exists]
      intro types
      cases types <;> simp
    | Val ty =>
      constructor
      · intro concrete
        obtain ⟨types, rfl⟩ := ih.mp (fun v member => concrete v (by simp [member]))
        exact ⟨ty :: types, rfl⟩
      · rintro ⟨types, equality⟩
        intro v member eq
        subst v
        rw [equality] at member
        simp at member

theorem concrete_stack_append {left right : List code.StackType} :
    ConcreteStack (left ++ right) ↔ ConcreteStack left ∧ ConcreteStack right := by
  simp [ConcreteStack, or_imp, forall_and]

theorem spine_values {env root parents C outer form inputs}
    (spine : Body.Frames.Spine env root parents C outer form inputs) :
    outer = parents.flatMap Body.Frames.Saved.vals := by
  induction spine with
  | root => rfl
  | push parents C outer parent child ins spine header base resume notBody ih =>
    simp [List.flatMap_append, ih]

end Itasca.Compiler

end

/-! ## TypedRunClosed -/

section

/-! ## SourceBudget -/

section

namespace Itasca.Compiler
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
end Itasca.Compiler

end

/-! ## SourceControlBudget -/

section

namespace Itasca.Compiler
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
end Itasca.Compiler

end

/-! ## TypedRunClosed -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem TypedRun.closed {V : Type} {visitor : code.OpVisitor V}
    {data env ctx index st before after}
    (run : TypedRun visitor data env ctx index st before after)
    (closed : st.blocks.val = []) : after = before ∧ st.core.pos = Slice.len data := by
  cases run with
  | done typed empty finished => exact ⟨rfl, finished⟩
  | step typed pending start advance called rest =>
    obtain ⟨_, _, _, _, _, _, _, blocks, _⟩ := pending.opened
    simp only [code.BodyState.blocks] at closed blocks
    rw [closed] at blocks
    simp at blocks
end Itasca.Compiler

end

end
