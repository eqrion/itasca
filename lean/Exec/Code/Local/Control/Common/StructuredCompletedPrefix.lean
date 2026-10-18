import Exec.Code.Local.Control.Common.StructuredUniversalTerminal
import Exec.Code.Local.Control.Common.StructuredPrefixClose
namespace Exec.Code
open Aeneas.Std

/-- A completed current arm, still quantified over every admissible future
outer target. Its normal-exit flag is the actual compiler reachability bit. -/
structure StructuredCompletedPrefix (emit : List valtype → instr → List Bytecode → List valtype → Prop) {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope) (normal : Bool) : Prop where
  sites : ∀ frame ∈ compiler.frames.val, FrameSites compiler.function.code.val frame
  prefixes : ∀ label labels groups,
    FramePlans compiler.function.code.val.length locals compiler.frames.val (label :: labels) groups →
    ScopeLabel current label → List.Forall₂ ScopeLabel parents.reverse labels →
    label.normalExit = compiler.function.code.val.length → label.normalLive = normal →
    StructuredParentPrefixes emit types functions returns locals (resolvedCode compiler.function.code.val groups)
      parents labels current ∧
    StructuredCode emit types functions returns locals (resolvedCode compiler.function.code.val groups)
      (label :: labels) current.input current.source current.bodyPc compiler.function.code.val.length
      (current.front ++ current.results)

theorem StructuredUniversalPrefix.completed {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current}
    (invariant : StructuredUniversalPrefix emit compiler types functions returns locals parents current
      (current.front ++ current.results)) :
    StructuredCompletedPrefix emit compiler types functions returns locals parents current true := by
  refine ⟨invariant.sites, ?_⟩
  intro label labels groups plans shape parentShapes endpoint normal
  obtain ⟨saved, body⟩ := invariant.prefixes label labels groups plans shape parentShapes
  exact ⟨saved, body.finish (by simp [resolvedCode_length]) (NormalLive.cons normal)⟩

theorem StructuredUniversalTerminal.completed {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current}
    (invariant : StructuredUniversalTerminal emit compiler types functions returns locals parents current) :
    StructuredCompletedPrefix emit compiler types functions returns locals parents current false := by
  refine ⟨invariant.sites, ?_⟩
  intro label labels groups plans shape parentShapes endpoint normal
  obtain ⟨saved, body⟩ := invariant.prefixes label labels groups plans shape parentShapes
  exact ⟨saved, body.finish _ _ (Nat.le_refl _) (by simp [resolvedCode_length])⟩

end Exec.Code
