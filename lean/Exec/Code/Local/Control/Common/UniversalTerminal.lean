import Exec.Code.Local.Control.Common.UniversalPrefix
namespace Exec.Code
open Aeneas.Std

/-- Terminal source instructions whose bytecode has no pending label fixup. -/
inductive TerminalEmission (locals returns : List valtype) : List valtype → instr → Bytecode → Prop where
  | unreachable (stack) : TerminalEmission locals returns stack .UNREACHABLE .Unreachable
  | return_ (front) (source count : U32)
      (position : source.val = slots locals + slots front) (width : count.val = slots returns) :
      TerminalEmission locals returns (front ++ returns) .RETURN (.Return source count)

theorem TerminalEmission.prefix {locals returns stack instruction emitted}
    (emission : TerminalEmission locals returns stack instruction emitted)
    {types functions code labels pc} (fetched : code[pc]? = some emitted) :
    DeadCodePrefix types functions returns locals code labels stack [instruction] pc (pc + 1) := by
  cases emission with
  | unreachable => exact .unreachable fetched
  | return_ front source count position width => exact .return_ position width fetched

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

/-- Exact emission of UNREACHABLE or RETURN changes a live prefix into a
terminal one for every future control completion. -/
theorem UniversalPrefix.terminate {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals parents current stack instruction emitted}
    (invariant : UniversalPrefix before types functions returns locals parents current stack)
    (emission : TerminalEmission locals returns stack instruction emitted)
    (codeEq : after.function.code.val = before.function.code.val ++ [emitted])
    (framesEq : after.frames = before.frames) (localsEq : compilerLocals after = locals) :
    UniversalTerminal after types functions returns locals parents (current.advance instruction) := by
  have lengthOrder : before.function.code.val.length ≤ after.function.code.val.length := by simp [codeEq]
  refine ⟨localsEq, ?_, ?_⟩
  · intro frame member
    rw [framesEq] at member
    simpa only [codeEq] using (invariant.sites frame member).extend [emitted]
  · intro label labels groups plans shape parentShapes
    have oldPlans : FramePlans before.function.code.val.length locals before.frames.val (label :: labels) groups := by
      rw [← framesEq]
      exact plans.before lengthOrder
    have oldShape : ScopeLabel current label :=
      ⟨shape.front, by simpa [SourceScope.advance, SourceScope.branchTypes] using shape.branchTypes, shape.results⟩
    have old := invariant.resolved oldPlans oldShape parentShapes
    have saved := (invariant.prefixes label labels groups oldPlans oldShape parentShapes).1
    have resolved := resolvedCode_append_code before.function.code.val [emitted] groups old.inside
    refine ⟨?_, ?_⟩
    · simpa only [codeEq, resolved] using (saved.extend [emitted]).advance_current instruction
    · have fetched : (resolvedCode before.function.code.val groups ++ [emitted])[before.function.code.val.length]? = some emitted := by simp [← resolvedCode_length before.function.code.val groups]
      have terminal := (old.code.extend [emitted]).terminal (emission.prefix fetched)
      simpa only [codeEq, resolved, List.length_append, List.length_singleton, SourceScope.advance, SourceScope.input] using terminal

/-- An omitted ordinary instruction in an unreachable source suffix extends
only the source prefix. This consumes exact unchanged-code/frame equations. -/
theorem UniversalTerminal.skip {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals parents current}
    (invariant : UniversalTerminal before types functions returns locals parents current)
    (instruction : instr)
    (codeEq : after.function.code.val = before.function.code.val)
    (framesEq : after.frames = before.frames) (localsEq : compilerLocals after = locals) :
    UniversalTerminal after types functions returns locals parents (current.advance instruction) := by
  refine ⟨localsEq, ?_, ?_⟩
  · simpa only [codeEq, framesEq] using invariant.sites
  · intro label labels groups plans shape parentShapes
    have oldPlans : FramePlans before.function.code.val.length locals before.frames.val (label :: labels) groups := by
      simpa only [codeEq, framesEq] using plans
    have oldShape : ScopeLabel current label :=
      ⟨shape.front, by simpa [SourceScope.advance, SourceScope.branchTypes] using shape.branchTypes, shape.results⟩
    obtain ⟨saved, terminal⟩ := invariant.prefixes label labels groups oldPlans oldShape parentShapes
    exact ⟨by simpa only [codeEq] using saved.advance_current instruction,
      by simpa only [codeEq, SourceScope.advance, SourceScope.input] using terminal.skip_source [instruction]⟩

end Exec.Code
