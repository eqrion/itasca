import Exec.Code.Body.Callbacks.Common.CompilerPrefix
import Exec.Code.Local.Callbacks.Control.ScopeFrameStart
import Exec.Code.Local.Source.SourceEntry
namespace Itasca.Runtime.Code
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

end Itasca.Runtime.Code
