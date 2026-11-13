import Itasca.Runtime.Compiler.Local.Callbacks.Control.ElseFrames
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalPrefix
import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.FixupBudget
import Itasca.Runtime.Compiler.Local.Relations.Prefix.PrefixZipper
import Itasca.Runtime.Compiler.Local.Relations.Prefix.ResolvedGuards

/-!
Sections, each formerly its own module: UniversalInitial, UniversalTerminal, UniversalDormant.
-/

/-! ## UniversalInitial -/

section

/-!
The root source cursor before the first body instruction.

Main declarations: `SourceScope.initial`. A direct consumer is `Compiler.Body.Reader.Control.ScopeFronts`.
-/

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end

/-! ## UniversalTerminal -/

section

/-!
Terminal source instructions whose bytecode has no pending label fixup.

Main declarations: `TerminalEmission` and `UniversalTerminal`. A direct consumer is `Compiler.Local.Control.Control.UniversalBranch`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas.Std

/-- Terminal source instructions whose bytecode has no pending label fixup. -/
inductive TerminalEmission (locals returns : List valtype) : List valtype → instr → Bytecode → Prop where
  | unreachable (stack) : TerminalEmission locals returns stack .UNREACHABLE .Unreachable
  | return_ (front) (source count : U32)
      (position : source.val = slots locals + slots front) (width : count.val = slots returns) :
      TerminalEmission locals returns (front ++ returns) .RETURN (.Return source count)

/-- Dead source prefixes retain their parent chain but do not assert a live
operand layout. Source suffixes are admitted only through a checked terminal
instruction already retained in the prefix. -/
structure UniversalTerminal {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope) : Prop where
  localsEq : compilerLocals compiler = locals
  sites : ∀ frame ∈ compiler.frames.val, FrameSites compiler.function.code.val frame
  prefixes : ∀ label labels groups,
    FramePlans compiler.function.code.val.length locals compiler.frames.val (label :: labels) groups →
    ScopeLabel current label → List.Forall₂ ScopeLabel parents.reverse labels →
    ParentPrefixes types functions returns locals (resolvedCode compiler.function.code.val groups)
      parents labels current ∧
    DeadCodePrefix types functions returns locals (resolvedCode compiler.function.code.val groups)
      (label :: labels) current.input current.source current.bodyPc compiler.function.code.val.length

end Itasca.Runtime.Compiler

end

/-! ## UniversalDormant -/

section

/-!
An unentered source subtree emits no executable body. Its enclosing terminal prefix remains retained; no code relation is asserted for the child.

Main declarations: `UniversalDormant`. A direct consumer is `Compiler.Local.Control.Table.StructuredUniversalDormant`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas.Std

/-- An unentered source subtree emits no executable body. Its enclosing
terminal prefix remains retained; no code relation is asserted for the child. -/
structure UniversalDormant {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope) : Prop where
  unentered : current.entered = false
  localsEq : compilerLocals compiler = locals
  sites : ∀ frame ∈ compiler.frames.val, FrameSites compiler.function.code.val frame
  prefixes : ∀ label labels groups,
    FramePlans compiler.function.code.val.length locals compiler.frames.val (label :: labels) groups →
    ScopeLabel current label → List.Forall₂ ScopeLabel parents.reverse labels →
    ParentPrefixes types functions returns locals (resolvedCode compiler.function.code.val groups)
      parents labels current

end Itasca.Runtime.Compiler

end
