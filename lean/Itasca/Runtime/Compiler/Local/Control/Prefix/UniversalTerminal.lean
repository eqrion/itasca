import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalPrefix

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
