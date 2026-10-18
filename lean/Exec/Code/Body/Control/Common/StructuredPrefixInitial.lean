import Exec.Code.Body.Control.Common.StructuredCompilerPrefix
import Exec.Code.Body.Callbacks.Common.CompilerPrefixInitial
namespace Exec.Code
open Aeneas Aeneas.Std
theorem StructuredUniversalPrefix.initial {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (emit : List valtype → instr → List Bytecode → List valtype → Prop)
    (types functions : List functype) (returns locals : List valtype)
    (frame : runtime.compiler.Frame)
    (code : compiler.function.code.val = []) (frames : compiler.frames.val = [frame])
    (noGuard : frame.if_pc = none) (noBranches : frame.fixups.val = [])
    (localTypes : compilerLocals compiler = locals) (layout : CompilerLayout compiler []) :
    StructuredUniversalPrefix emit compiler types functions returns locals [] (SourceScope.initial returns) [] := by
  refine ⟨localTypes, layout, ?_, ?_⟩
  · intro f member
    simp only [frames, List.mem_singleton] at member
    subst f
    exact ⟨by simp [ForwardSites, noBranches], by simp [noGuard]⟩
  · intro label labels groups plans shape parentShapes
    cases parentShapes
    refine ⟨.root _, ?_⟩
    simpa only [SourceScope.initial, SourceScope.input, List.nil_append, code, List.length_nil] using
      StructuredPrefix.empty emit types functions returns locals (resolvedCode compiler.function.code.val groups)
        [label] [] 0

/-- At function entry there are no completed ELSE arms, including in the
empty saved parent chain. -/
theorem StructuredUniversalElse.initial {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (emit : List valtype → instr → List Bytecode → List valtype → Prop)
    (types functions : List functype) (returns locals : List valtype) :
    StructuredUniversalElse emit compiler types functions returns locals [] (SourceScope.initial returns) := by
  intro label labels groups plans shape parentShapes
  cases parentShapes
  exact .cons _ label (by simp [StructuredElseEvidence, SourceScope.initial]) .nil

end Exec.Code

namespace Exec.Code
open Aeneas Aeneas.Std
theorem StructuredCompilerPrefix.initial {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (emit : List valtype → instr → List Bytecode → List valtype → Prop)
    (types functions : List functype) (returns locals : List valtype)
    (frames : ScopeFrameStack locals compiler [] (SourceScope.initial returns))
    (retained : StructuredUniversalPrefix emit compiler types functions returns locals [] (SourceScope.initial returns) [])
    (arms : StructuredUniversalElse emit compiler types functions returns locals [] (SourceScope.initial returns))
    (sources : SourceAligned compiler) (codeBudget : SourceCodeBudget compiler 0)
    (controlBudget : SourceControlBudget compiler 0) (cursor : compiler.next_source.val = 0)
    (reachable : compiler.reachable = true) :
    StructuredCompilerPrefix emit compiler compiler types functions returns locals [] (SourceScope.initial returns) [] 0 := by
  refine ⟨.refl _, frames, .root _ rfl, frames.dormant_initial rfl, ScopeConditions.initial, ?_, .live reachable rfl retained, arms, sources, codeBudget, controlBudget, ?_⟩
  · simp [ConcreteStack]
  · omega

/-- Reader positions may advance over local declarations before the first
opcode; increasing the accounted source position preserves every invariant. -/
theorem StructuredCompilerPrefix.advance_position {A : Type} {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw start finish}
    (invariant : StructuredCompilerPrefix emit initial compiler types functions returns locals parents current raw start)
    (order : start ≤ finish) :
    StructuredCompilerPrefix emit initial compiler types functions returns locals parents current raw finish := by
  refine ⟨invariant.metadata, invariant.frames, invariant.entryChain, invariant.dormant, invariant.conditions, invariant.known, invariant.mode, invariant.arms,
    invariant.sources, ?_, invariant.controlBudget.advance order, invariant.cursor.trans order⟩
  exact invariant.codeBudget.trans (Nat.mul_le_mul_left 3 order)
end Exec.Code
