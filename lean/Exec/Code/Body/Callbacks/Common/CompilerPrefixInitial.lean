import Exec.Code.Body.Callbacks.Common.CompilerPrefix
import Exec.Code.Local.Callbacks.Control.ScopeFrameStart
import Exec.Code.Local.Source.SourceEntry
namespace Exec.Code
open Aeneas Aeneas.Std

/-- The root scope starts with an empty concrete operand stack and a live
empty source prefix. All budgets and alignment are physical compiler facts. -/
theorem CompilerPrefix.initial {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (frames : ScopeFrameStack locals compiler [] (SourceScope.initial returns))
    (retained : UniversalPrefix compiler types functions returns locals [] (SourceScope.initial returns) [])
    (arms : UniversalElse compiler types functions returns locals [] (SourceScope.initial returns))
    (sources : SourceAligned compiler) (codeBudget : SourceCodeBudget compiler 0)
    (controlBudget : SourceControlBudget compiler 0) (cursor : compiler.next_source.val = 0)
    (reachable : compiler.reachable = true) :
    CompilerPrefix compiler compiler types functions returns locals [] (SourceScope.initial returns) [] 0 := by
  refine ⟨.refl _, frames, .root _ rfl, frames.dormant_initial rfl, ScopeConditions.initial, ?_, .live reachable rfl retained, arms, sources, codeBudget, controlBudget, ?_⟩
  · simp [ConcreteStack]
  · omega

/-- Reader positions may advance over local declarations before the first
opcode; increasing the accounted source position preserves every invariant. -/
theorem CompilerPrefix.advance_position {A : Type} {initial compiler : runtime.compiler.FunctionCompiler A}
    {types functions returns locals parents current raw start finish}
    (invariant : CompilerPrefix initial compiler types functions returns locals parents current raw start)
    (order : start ≤ finish) :
    CompilerPrefix initial compiler types functions returns locals parents current raw finish := by
  refine ⟨invariant.metadata, invariant.frames, invariant.entryChain, invariant.dormant, invariant.conditions, invariant.known, invariant.mode, invariant.arms,
    invariant.sources, ?_, invariant.controlBudget.advance order, invariant.cursor.trans order⟩
  exact invariant.codeBudget.trans (Nat.mul_le_mul_left 3 order)
end Exec.Code
