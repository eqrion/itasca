import Exec.Code.Local.Callbacks.Control.ElseFrames
namespace Itasca.Runtime.Code
open Aeneas.Std

/-- The root source cursor before the first body instruction. -/
def SourceScope.initial (results : List valtype) : SourceScope :=
  ⟨.body, [], [], results, [], 0, 0, true⟩

/-- An empty emitted function starts the universally planned prefix without
choosing any future exit target or branch liveness. -/
theorem UniversalPrefix.initial {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (frame : runtime.compiler.Frame)
    (code : compiler.function.code.val = []) (frames : compiler.frames.val = [frame])
    (noGuard : frame.if_pc = none) (noBranches : frame.fixups.val = [])
    (localTypes : compilerLocals compiler = locals) (layout : CompilerLayout compiler []) :
    UniversalPrefix compiler types functions returns locals [] (SourceScope.initial returns) [] := by
  refine ⟨localTypes, layout, ?_, ?_⟩
  · intro f member
    simp only [frames, List.mem_singleton] at member
    subst f
    exact ⟨by simp [ForwardSites, noBranches], by simp [noGuard]⟩
  · intro label labels groups plans shape parentShapes
    cases parentShapes
    refine ⟨.root _, ?_⟩
    simpa only [SourceScope.initial, SourceScope.input, List.nil_append, code, List.length_nil] using
      CodePrefix.empty types functions returns locals (resolvedCode compiler.function.code.val groups)
        [label] [] 0

/-- At function entry there are no completed ELSE arms, including in the
empty saved parent chain. -/
theorem UniversalElse.initial {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype) :
    UniversalElse compiler types functions returns locals [] (SourceScope.initial returns) := by
  intro label labels groups plans shape parentShapes
  cases parentShapes
  exact .cons _ label (ElseEvidence.fresh rfl) .nil

end Itasca.Runtime.Code
