import Itasca.Runtime.Compiler.Local.Control.Structured.Prefixes
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalDormant
import Itasca.Runtime.Compiler.Local.Callbacks.Control.EntryAndElseFrames
import Itasca.Runtime.Compiler.Local.Relations.Prefix.SuspendedPrefix
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CallbackRetention
import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.FixupBudget
import Itasca.Runtime.Compiler.Local.Relations.Prefix.ResolvedGuards
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalRoot
import Itasca.Runtime.Compiler.Local.Relations.Prefix.PrefixZipper
import Itasca.Runtime.Compiler.Local.Relations.Prefix.ConsumedPrefix
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalPrefix
import Itasca.Runtime.Compiler.Local.Lowering.Emission.LoweringEmpty
import Itasca.Runtime.Compiler.Local.Definitions
import Itasca.Runtime.Compiler.Local.Callbacks.Function.FunctionStartContracts
import Itasca.Runtime.Compiler.Local.Relations.Function.RootLabel
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlCoordinates
import Itasca.Runtime.Compiler.Local.Control.StructuredElseResolvedAppend
import Itasca.Runtime.Compiler.Local.Control.CodeSegmentsAndPositions
import Itasca.Runtime.Compiler.Local.Relations.Layout.LayoutProofs
import Itasca.Support.Translation

/-!
Proofs for Runtime / Compiler / Local / Control / Structured.

This module collects NestedScopes, CloseIfAndBlocks, Function.
Each section documents its contracts and consumers.
-/

/-! ## NestedScopes -/

section

open Itasca.Representation

/-!
# Nested Scopes

Live and dormant nested scopes preserve structured compiler prefixes and their matching control boundaries.
-/

/-! ## StructuredUniversalDormant -/

section

namespace Itasca.Compiler
open Aeneas.Std

/-- An unentered source subtree emits no executable body. Its enclosing
terminal prefix remains retained; no code relation is asserted for the child. -/
structure StructuredUniversalDormant (jumpTables : List Aeneas.Std.U32) (emit : List valtype → instr → List Bytecode → List valtype → Prop) {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope) : Prop where
  unentered : current.entered = false
  localsEq : compilerLocals compiler = locals
  sites : ∀ frame ∈ compiler.frames.val, FrameSites compiler.function.code.val frame
  prefixes : ∀ label labels groups,
    FramePlans compiler.function.code.val.length locals compiler.frames.val (label :: labels) groups →
    ScopeLabel current label → List.Forall₂ ScopeLabel parents.reverse labels →
    StructuredParentPrefixes (jumpTables := jumpTables) emit types functions returns locals (resolvedCode compiler.function.code.val groups)
      parents labels current

theorem StructuredUniversalDormant.skip {jumpTables : List Aeneas.Std.U32} {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current}
    (invariant : StructuredUniversalDormant (jumpTables := jumpTables) emit before types functions returns locals parents current)
    (instruction : instr) (codeEq : after.function.code = before.function.code)
    (framesEq : after.frames = before.frames) (localsEq : compilerLocals after = locals) :
    StructuredUniversalDormant (jumpTables := jumpTables) emit after types functions returns locals parents (current.advance instruction) := by
  refine ⟨invariant.unentered, localsEq, ?_, ?_⟩
  · simpa only [codeEq, framesEq] using invariant.sites
  · intro label labels groups plans shape parentShapes
    have oldPlans : FramePlans before.function.code.val.length locals before.frames.val (label :: labels) groups := by
      simpa only [codeEq, framesEq] using plans
    have oldShape : ScopeLabel current label :=
      ⟨shape.front, by simpa [SourceScope.advance, SourceScope.branchTypes] using shape.branchTypes, shape.results⟩
    simpa only [codeEq] using (invariant.prefixes label labels groups oldPlans oldShape parentShapes).advance_current instruction

/-- A terminal entered scope can open an unentered child. Its dead prefix is
suspended before the child, with no manufactured body relation. -/
theorem StructuredUniversalTerminal.open_dormant {jumpTables : List Aeneas.Std.U32} {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current}
    (invariant : StructuredUniversalTerminal (jumpTables := jumpTables) emit before types functions returns locals parents current)
    (child : SourceScope) (frame : runtime.compiler.Frame)
    (codeEq : after.function.code = before.function.code)
    (framesEq : after.frames.val = before.frames.val ++ [frame])
    (noGuard : frame.if_pc = none) (noBranches : frame.fixups.val = [])
    (localsEq : compilerLocals after = locals)
    (parentEntered : current.entered = true) (childEntered : child.entered = false)
    (entry : child.entry = before.function.code.val.length) :
    StructuredUniversalDormant (jumpTables := jumpTables) emit after types functions returns locals (parents ++ [current]) child := by
  refine ⟨childEntered, localsEq, ?_, ?_⟩
  · intro f member
    rw [framesEq] at member
    rcases List.mem_append.mp member with old | fresh
    · simpa only [codeEq] using invariant.sites f old
    · simp only [List.mem_singleton] at fresh
      subst f
      exact ⟨by simp [ForwardSites, noBranches], by simp [noGuard]⟩
  · intro label labels groups plans shape parentShapes
    rw [framesEq] at plans
    obtain ⟨top, outer, pending, target, labelsEq, groupsEq, priorPlans, future⟩ := plans.pop
    simp only [List.cons.injEq] at labelsEq
    obtain ⟨rfl, rfl⟩ := labelsEq
    have simplified : groups = ⟨[], label.target⟩ :: pending := by
      simpa [frameGroups, noGuard, noBranches] using groupsEq
    rw [simplified]
    have resolve : resolvedCode after.function.code.val (⟨[], label.target⟩ :: pending) =
        resolvedCode before.function.code.val pending := by simp only [resolvedCode, patchCode, codeEq]
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append] at parentShapes
    cases parentShapes with
    | @cons _ parentLabel _ outerLabels parentShape parentShapes =>
      have oldPlans : FramePlans before.function.code.val.length locals before.frames.val
          (parentLabel :: outerLabels) pending := by simpa only [codeEq] using priorPlans
      obtain ⟨saved, prefixCode⟩ := invariant.prefixes parentLabel outerLabels pending oldPlans parentShape parentShapes
      have prior : StructuredDeadPrefix (jumpTables := jumpTables) emit types functions returns locals (resolvedCode before.function.code.val pending)
          (parentLabel :: outerLabels) current.input current.source current.bodyPc
          (resolvedCode before.function.code.val pending).length := by
        simpa only [resolved_code_length] using prefixCode
      rw [resolve]
      apply StructuredParentPrefixes.push saved parentLabel child parentShape
      · simp [entry, resolved_code_length]
      · unfold StructuredParentPrefix
        simp only [parentEntered, childEntered, ite_true, Bool.false_eq_true, ite_false]
        simpa only [entry, resolved_code_length] using prior.suspend

theorem StructuredUniversalDormant.open_dormant {jumpTables : List Aeneas.Std.U32} {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current}
    (invariant : StructuredUniversalDormant (jumpTables := jumpTables) emit before types functions returns locals parents current)
    (child : SourceScope) (frame : runtime.compiler.Frame)
    (codeEq : after.function.code = before.function.code)
    (framesEq : after.frames.val = before.frames.val ++ [frame])
    (noGuard : frame.if_pc = none) (noBranches : frame.fixups.val = [])
    (localsEq : compilerLocals after = locals)
    (childEntered : child.entered = false)
    (entry : child.entry = before.function.code.val.length) :
    StructuredUniversalDormant (jumpTables := jumpTables) emit after types functions returns locals (parents ++ [current]) child := by
  refine ⟨childEntered, localsEq, ?_, ?_⟩
  · intro f member
    rw [framesEq] at member
    rcases List.mem_append.mp member with old | fresh
    · simpa only [codeEq] using invariant.sites f old
    · simp only [List.mem_singleton] at fresh
      subst f
      exact ⟨by simp [ForwardSites, noBranches], by simp [noGuard]⟩
  · intro label labels groups plans shape parentShapes
    rw [framesEq] at plans
    obtain ⟨top, outer, pending, target, labelsEq, groupsEq, priorPlans, future⟩ := plans.pop
    simp only [List.cons.injEq] at labelsEq
    obtain ⟨rfl, rfl⟩ := labelsEq
    have simplified : groups = ⟨[], label.target⟩ :: pending := by
      simpa [frameGroups, noGuard, noBranches] using groupsEq
    rw [simplified]
    have resolve : resolvedCode after.function.code.val (⟨[], label.target⟩ :: pending) =
        resolvedCode before.function.code.val pending := by simp only [resolvedCode, patchCode, codeEq]
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append] at parentShapes
    cases parentShapes with
    | @cons _ parentLabel _ outerLabels parentShape parentShapes =>
      have oldPlans : FramePlans before.function.code.val.length locals before.frames.val
          (parentLabel :: outerLabels) pending := by simpa only [codeEq] using priorPlans
      have saved := invariant.prefixes parentLabel outerLabels pending oldPlans parentShape parentShapes
      rw [resolve]
      apply StructuredParentPrefixes.push saved parentLabel child parentShape
      · simp [entry, resolved_code_length]
      · simp [StructuredParentPrefix, invariant.unentered]

/-- Closing an unentered child restores the terminal prefix of its entered
parent. The child's discarded source is retained syntactically in that suffix. -/
theorem StructuredUniversalDormant.close_terminal {jumpTables : List Aeneas.Std.U32} {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents parent child}
    (invariant : StructuredUniversalDormant (jumpTables := jumpTables) emit before types functions returns locals (parents ++ [parent]) child)
    (frame : runtime.compiler.Frame) (label : LabelTarget) (guardTarget : U32)
    (frames : before.frames.val = after.frames.val ++ [frame])
    (future : FrameFuture before.function.code.val.length locals frame label guardTarget)
    (shape : ScopeLabel child label)
    (codeEq : after.function.code.val = resolvedCode before.function.code.val (frameGroups frame label guardTarget))
    (sites : ∀ f ∈ after.frames.val, FrameSites after.function.code.val f)
    (localsEq : compilerLocals after = locals) (parentEntered : parent.entered = true)
    (instruction : instr) :
    StructuredUniversalTerminal (jumpTables := jumpTables) emit after types functions returns locals parents (parent.advance instruction) := by
  refine ⟨localsEq, sites, ?_⟩
  intro parentLabel labels groups plans parentShape parentShapes
  have lengthEq : after.function.code.val.length = before.function.code.val.length := by
    simp [codeEq, resolved_code_length]
  have outer : FramePlans before.function.code.val.length locals after.frames.val (parentLabel :: labels) groups := by
    simpa only [lengthEq] using plans
  have oldParentShape : ScopeLabel parent parentLabel :=
    ⟨parentShape.front, by simpa [SourceScope.advance, SourceScope.branchTypes] using parentShape.branchTypes, parentShape.results⟩
  have allPlans := FramePlans.push outer frame label guardTarget future
  rw [← frames] at allPlans
  have allShapes : List.Forall₂ ScopeLabel (parents ++ [parent]).reverse (parentLabel :: labels) := by
    simpa using List.Forall₂.cons oldParentShape parentShapes
  have saved := invariant.prefixes label (parentLabel :: labels) _ allPlans shape allShapes
  obtain ⟨outerSaved, _, _, parentSaved⟩ := saved.pop
  have restored := parentSaved.close_unentered parentEntered invariant.unentered instruction
  refine ⟨?_, ?_⟩
  · rw [codeEq, ← resolved_code_append_groups]
    exact outerSaved.advance_current instruction
  · simpa only [codeEq, ← resolved_code_append_groups, resolved_code_length,
      SourceScope.advance, SourceScope.input] using restored

/-- If the parent was itself unentered, closing its child preserves that
mode without constructing an execution relation for either discarded body. -/
theorem StructuredUniversalDormant.close_dormant {jumpTables : List Aeneas.Std.U32} {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents parent child}
    (invariant : StructuredUniversalDormant (jumpTables := jumpTables) emit before types functions returns locals (parents ++ [parent]) child)
    (frame : runtime.compiler.Frame) (label : LabelTarget) (guardTarget : U32)
    (frames : before.frames.val = after.frames.val ++ [frame])
    (future : FrameFuture before.function.code.val.length locals frame label guardTarget)
    (shape : ScopeLabel child label)
    (codeEq : after.function.code.val = resolvedCode before.function.code.val (frameGroups frame label guardTarget))
    (sites : ∀ f ∈ after.frames.val, FrameSites after.function.code.val f)
    (localsEq : compilerLocals after = locals) (parentEntered : parent.entered = false)
    (instruction : instr) :
    StructuredUniversalDormant (jumpTables := jumpTables) emit after types functions returns locals parents (parent.advance instruction) := by
  refine ⟨parentEntered, localsEq, sites, ?_⟩
  intro parentLabel labels groups plans parentShape parentShapes
  have lengthEq : after.function.code.val.length = before.function.code.val.length := by
    simp [codeEq, resolved_code_length]
  have outer : FramePlans before.function.code.val.length locals after.frames.val (parentLabel :: labels) groups := by
    simpa only [lengthEq] using plans
  have oldParentShape : ScopeLabel parent parentLabel :=
    ⟨parentShape.front, by simpa [SourceScope.advance, SourceScope.branchTypes] using parentShape.branchTypes, parentShape.results⟩
  have allPlans := FramePlans.push outer frame label guardTarget future
  rw [← frames] at allPlans
  have allShapes : List.Forall₂ ScopeLabel (parents ++ [parent]).reverse (parentLabel :: labels) := by
    simpa using List.Forall₂.cons oldParentShape parentShapes
  have saved := invariant.prefixes label (parentLabel :: labels) _ allPlans shape allShapes
  obtain ⟨outerSaved, _, _, _⟩ := saved.pop
  rw [codeEq, ← resolved_code_append_groups]
  exact outerSaved.advance_current instruction

end Itasca.Compiler

end

/-! ## StructuredUniversalBranchTable -/

section

namespace Itasca.Compiler
open Aeneas.Std

/-- Ordered target fragments close one source BR_TABLE. The retained plans and
resolved-code append are syntactic facts produced by the actual table callback. -/
theorem StructuredUniversalPrefix.branch_table
    {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {jumpTables : List U32} {emit types functions returns locals parents current stack}
    (depths : List labelidx) (fallback : labelidx)
    (invariant : StructuredUniversalPrefix jumpTables emit before types functions returns locals
      parents current (stack ++ [.I32]))
    (localsEq : compilerLocals after = locals)
    (sites : ∀ frame ∈ after.frames.val, FrameSites after.function.code.val frame)
    (gate : ∀ selector start len, emit (stack ++ [.I32]) (.BR_TABLE depths fallback)
      [.JumpTable selector start len] stack)
    (completion : ∀ label labels groups,
      FramePlans after.function.code.val.length locals after.frames.val (label :: labels) groups →
      ScopeLabel current label → List.Forall₂ ScopeLabel parents.reverse labels →
      ∃ previous selector start len suffix,
        FramePlans before.function.code.val.length locals before.frames.val (label :: labels) previous ∧
        resolvedCode after.function.code.val groups = resolvedCode before.function.code.val previous ++ suffix ∧
        BranchTableLayout jumpTables locals (label :: labels) stack (resolvedCode after.function.code.val groups)
          depths fallback before.function.code.val.length after.function.code.val.length selector start len ∧
        before.function.code.val.length + 1 ≤ after.function.code.val.length) :
    StructuredUniversalTerminal jumpTables emit after types functions returns locals parents
      (current.advance (.BR_TABLE depths fallback)) := by
  refine ⟨localsEq, sites, ?_⟩
  intro label labels groups plans shape parentShapes
  have oldShape : ScopeLabel current label :=
    ⟨shape.front, by simpa [SourceScope.advance, SourceScope.branchTypes] using shape.branchTypes, shape.results⟩
  obtain ⟨previous, selector, start, len, suffix, oldPlans, codeEq, table, header⟩ :=
    completion label labels groups plans oldShape parentShapes
  obtain ⟨saved, retained⟩ := invariant.prefixes label labels previous oldPlans oldShape parentShapes
  refine ⟨?_, ?_⟩
  · rw [codeEq]
    exact (saved.extend suffix).advance_current _
  · have prior : StructuredPrefix (jumpTables := jumpTables) emit types functions returns locals
        (resolvedCode after.function.code.val groups) (label :: labels) current.input current.source
        current.bodyPc before.function.code.val.length (stack ++ [.I32]) := by
      rw [codeEq]
      exact retained.extend suffix
    have terminal := StructuredDeadPrefix.branch_table (types := types) (functions := functions) (returns := returns) (gate selector start len) table header
    simpa only [SourceScope.advance, SourceScope.input] using prior.terminal terminal
end Itasca.Compiler

end

/-! ## StructuredPrefixClose -/

section

namespace Itasca.Compiler
open Aeneas.Std

theorem StructuredPrefix.finish {jumpTables : List Aeneas.Std.U32} {emit types functions returns locals code labels before source start cursor stack}
    (current : StructuredPrefix (jumpTables := jumpTables) emit types functions returns locals code labels before source start cursor stack)
    (bound : cursor ≤ code.length) (live : NormalLive labels) :
    StructuredCode emit types functions returns locals code jumpTables labels before source start cursor stack := by
  have closed := current [] [] cursor stack (.nil labels stack cursor (by simpa using bound) live)
  simpa using closed

theorem StructuredDeadPrefix.finish {jumpTables : List Aeneas.Std.U32} {emit types functions returns locals code labels before source start cursor}
    (current : StructuredDeadPrefix (jumpTables := jumpTables) emit types functions returns locals code labels before source start cursor)
    (next : Nat) (output : List valtype) (order : cursor ≤ next) (bound : next ≤ code.length) :
    StructuredCode emit types functions returns locals code jumpTables labels before source start next output := by
  have closed := current [] [] next output order (by simpa using bound)
  simpa using closed

end Itasca.Compiler

end

/-! ## StructuredCompletedPrefix -/

section

namespace Itasca.Compiler
open Aeneas.Std

/-- A completed current arm, still quantified over every admissible future
outer target. Its normal-exit flag is the actual compiler reachability bit. -/
structure StructuredCompletedPrefix (jumpTables : List Aeneas.Std.U32) (emit : List valtype → instr → List Bytecode → List valtype → Prop) {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope) (normal : Bool) : Prop where
  sites : ∀ frame ∈ compiler.frames.val, FrameSites compiler.function.code.val frame
  prefixes : ∀ label labels groups,
    FramePlans compiler.function.code.val.length locals compiler.frames.val (label :: labels) groups →
    ScopeLabel current label → List.Forall₂ ScopeLabel parents.reverse labels →
    label.normalExit = compiler.function.code.val.length → label.normalLive = normal →
    StructuredParentPrefixes (jumpTables := jumpTables) emit types functions returns locals (resolvedCode compiler.function.code.val groups)
      parents labels current ∧
    StructuredCode emit types functions returns locals (resolvedCode compiler.function.code.val groups) jumpTables
      (label :: labels) current.input current.source current.bodyPc compiler.function.code.val.length
      (current.front ++ current.results)

theorem StructuredUniversalPrefix.completed {jumpTables : List Aeneas.Std.U32} {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current}
    (invariant : StructuredUniversalPrefix (jumpTables := jumpTables) emit compiler types functions returns locals parents current
      (current.front ++ current.results)) :
    StructuredCompletedPrefix (jumpTables := jumpTables) emit compiler types functions returns locals parents current true := by
  refine ⟨invariant.sites, ?_⟩
  intro label labels groups plans shape parentShapes endpoint normal
  obtain ⟨saved, body⟩ := invariant.prefixes label labels groups plans shape parentShapes
  exact ⟨saved, body.finish (by simp [resolved_code_length]) (NormalLive.cons normal)⟩

theorem StructuredUniversalTerminal.completed {jumpTables : List Aeneas.Std.U32} {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current}
    (invariant : StructuredUniversalTerminal (jumpTables := jumpTables) emit compiler types functions returns locals parents current) :
    StructuredCompletedPrefix (jumpTables := jumpTables) emit compiler types functions returns locals parents current false := by
  refine ⟨invariant.sites, ?_⟩
  intro label labels groups plans shape parentShapes endpoint normal
  obtain ⟨saved, body⟩ := invariant.prefixes label labels groups plans shape parentShapes
  exact ⟨saved, body.finish _ _ (Nat.le_refl _) (by simp [resolved_code_length])⟩

end Itasca.Compiler

end

/-! ## StructuredParentPrefixChange -/

section

namespace Itasca.Compiler

open Aeneas.Std
theorem StructuredPrefix.suspend_after {jumpTables : List Aeneas.Std.U32} {emit types functions returns locals labels initial source start stack}
    {code : List Bytecode}
    (prior : StructuredPrefix (jumpTables := jumpTables) emit types functions returns locals code labels initial source start code.length stack)
    (emitted : List Bytecode) :
    StructuredSuspendedPrefix (jumpTables := jumpTables) emit types functions returns locals (code ++ emitted) labels initial source start code.length stack :=
  prior.suspend.extend emitted

/-- ELSE changes a child's source form and current instruction list while
leaving the suspended parent's entry hole and argument vector unchanged. -/
theorem StructuredParentPrefix.change_child {jumpTables : List Aeneas.Std.U32} {emit types functions returns locals code labels parent before after}
    (saved : StructuredParentPrefix (jumpTables := jumpTables) emit types functions returns locals code labels parent before)
    (entered : after.entered = before.entered) (entry : after.entry = before.entry)
    (arguments : after.arguments = before.arguments) :
    StructuredParentPrefix (jumpTables := jumpTables) emit types functions returns locals code labels parent after := by
  simpa only [StructuredParentPrefix, entered, entry, arguments] using saved

theorem StructuredParentPrefixes.change_current {jumpTables : List Aeneas.Std.U32} {emit types functions returns locals code parents labels before after}
    (saved : StructuredParentPrefixes (jumpTables := jumpTables) emit types functions returns locals code parents labels before)
    (entered : after.entered = before.entered) (entry : after.entry = before.entry)
    (arguments : after.arguments = before.arguments) :
    StructuredParentPrefixes (jumpTables := jumpTables) emit types functions returns locals code parents labels after := by
  induction saved with
  | root current => exact .root after
  | push prior label child shape bound held ih =>
    exact .push prior label after shape (by simpa only [entry] using bound)
      (held.change_child entered entry arguments)

end Itasca.Compiler

end

/-! ## StructuredElseSource -/

section

namespace Itasca.Compiler
open Aeneas.Std
theorem StructuredElseFrames.outer {jumpTables : List Aeneas.Std.U32} {emit types functions returns locals code scopes labels scope label}
    (frames : StructuredElseFrames (jumpTables := jumpTables) emit types functions returns locals code (scope :: scopes) (label :: labels)) :
    StructuredElseFrames (jumpTables := jumpTables) emit types functions returns locals code scopes labels := by
  cases frames with
  | cons _ _ _ outer => exact outer

theorem StructuredElseEvidence.begin_else {jumpTables : List Aeneas.Std.U32} {emit types functions returns locals outer bt yesExit normal}
    {code : List Bytecode} {scope : SourceScope} {label : LabelTarget} {condition noEntry : U32}
    (entered : scope.entered = true)
    (conditionSlot : condition.val = slots locals + slots scope.input)
    (guard : code[scope.entry]? = some (.JumpIfZero condition noEntry))
    (body : StructuredCode emit types functions returns locals code jumpTables
      (⟨scope.front, scope.results, scope.results, label.target, yesExit, [], [], normal, label.branchLive⟩ :: outer)
      scope.input scope.source (scope.entry + 1) yesExit (scope.front ++ scope.results))
    (skip : IfSkip code yesExit noEntry label.target normal) :
    StructuredElseEvidence (jumpTables := jumpTables) emit types functions returns locals code outer
      (scope.begin_else bt condition yesExit noEntry normal) label := by
  simp only [StructuredElseEvidence, SourceScope.begin_else, entered, ite_true]
  exact ⟨conditionSlot, guard, body, skip, trivial⟩

end Itasca.Compiler

end

/-! ## StructuredUniversalElse -/

section

namespace Itasca.Compiler
open Aeneas.Std

/-- ELSE freezes the completed arm under every future outer plan and starts
its sibling body. Both normal and terminal then arms use the same actual
patch/optional-skip transition. -/
theorem StructuredCompletedPrefix.begin_else {jumpTables : List Aeneas.Std.U32} {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents scope normal}
    (invariant : StructuredCompletedPrefix (jumpTables := jumpTables) emit before types functions returns locals parents scope normal)
    (completed : StructuredUniversalElse (jumpTables := jumpTables) emit before types functions returns locals parents scope)
    (prior : List runtime.compiler.Frame) (frame : runtime.compiler.Frame)
    (guard site : Usize) (condition old noEntry : U32) (fixups : alloc.vec.Vec Usize)
    (change : ElseTransition before after prior frame guard site condition old noEntry fixups normal)
    (bt : blocktype) (form : scope.form = .then_ bt condition)
    (entered : scope.entered = true) (entry : scope.entry = guard.val)
    (bodyStart : scope.bodyPc = scope.entry + 1)
    (conditionSlot : condition.val = slots locals + slots scope.input)
    (kind : frame.kind = .Then) (guardEq : frame.if_pc = some guard)
    (distinct : ∀ other ∈ prior, other.if_pc ≠ some guard)
    (localsEq : compilerLocals after = locals) (layout : CompilerLayout after scope.input) :
    StructuredUniversalPrefix (jumpTables := jumpTables) emit after types functions returns locals parents
      (scope.begin_else bt condition before.function.code.val.length noEntry normal) scope.input ∧
    StructuredUniversalElse (jumpTables := jumpTables) emit after types functions returns locals parents
      (scope.begin_else bt condition before.function.code.val.length noEntry normal) := by
  let next := scope.begin_else bt condition before.function.code.val.length noEntry normal
  have advance : ∀ label labels groups,
      FramePlans after.function.code.val.length locals after.frames.val (label :: labels) groups →
      ScopeLabel next label → List.Forall₂ ScopeLabel parents.reverse labels →
      StructuredParentPrefixes (jumpTables := jumpTables) emit types functions returns locals (resolvedCode after.function.code.val groups) parents labels next ∧
      StructuredPrefix (jumpTables := jumpTables) emit types functions returns locals (resolvedCode after.function.code.val groups)
        (label :: labels) next.input next.source next.bodyPc after.function.code.val.length scope.input ∧
      StructuredElseFrames (jumpTables := jumpTables) emit types functions returns locals (resolvedCode after.function.code.val groups)
        (next :: parents.reverse) (label :: labels) := by
    intro label labels groups plans shape parentShapes
    rw [change.afterFrames] at plans
    obtain ⟨found, outer, pending, ignored, sameLabels, grouped, outerPlans, future⟩ := plans.pop
    have same : found = label ∧ outer = labels := by simpa using sameLabels.symm
    obtain ⟨foundEq, outerEq⟩ := same
    subst found outer
    have groupsEq : groups = ⟨fixups.val, label.target⟩ :: pending := by
      simpa [frameGroups] using grouped
    rw [groupsEq]
    let oldLabel : LabelTarget := {label with normalExit := before.function.code.val.length, cont := [], after := [], normalLive := normal}
    have futureZero : FrameFuture after.function.code.val.length locals
        {frame with kind := .Else, if_pc := none, end_reachable := frame.end_reachable || normal, fixups} label 0#u32 :=
      {future with guardBound := by simp}
    have oldFuture : FrameFuture before.function.code.val.length locals frame oldLabel noEntry :=
      futureZero.before_else normal noEntry kind change.order (by rw [change.noPosition]; omega)
    have oldOuter := outerPlans.before change.order
    have oldPlans := FramePlans.push oldOuter frame oldLabel noEntry oldFuture
    rw [← change.beforeFrames] at oldPlans
    have oldPlans' : FramePlans before.function.code.val.length locals before.frames.val
        (oldLabel :: labels) (⟨[guard], noEntry⟩ :: ⟨frame.fixups.val, label.target⟩ :: pending) := by
      simpa [frameGroups, guardEq, oldLabel] using oldPlans
    have oldShape : ScopeLabel scope oldLabel := by
      have sameShape := shape.before_else form
      exact ⟨sameShape.front, sameShape.branchTypes, sameShape.results⟩
    obtain ⟨saved, body⟩ := invariant.prefixes oldLabel labels _ oldPlans' oldShape parentShapes rfl rfl
    have arms := completed oldLabel labels _ oldPlans' oldShape parentShapes
    have inside : FixupsInside (⟨frame.fixups.val, label.target⟩ :: pending) before.function.code.val.length := by
      intro group member atSite atMember
      exact oldPlans'.inside invariant.sites group (List.mem_cons_of_mem _ member) atSite atMember
    have resolved := change.resolved pending label.target inside
    let emitted : List Bytecode := if normal then [.Jump label.target] else []
    have guardFound : (resolvedCode before.function.code.val
        (⟨[guard], noEntry⟩ :: ⟨frame.fixups.val, label.target⟩ :: pending))[scope.entry]? =
        some (.JumpIfZero condition noEntry) := by
      rw [entry]
      have current := invariant.sites frame (by simp [change.beforeFrames])
      have outerAway := oldOuter.away_guard
        (fun f member => invariant.sites f (by rw [change.beforeFrames]; exact List.mem_append_left _ member))
        change.guardCode distinct
      exact resolved_code_guard _ [] _ guard condition old noEntry change.guardCode (by
        intro group member atSite atMember
        simp only [List.nil_append, List.mem_cons] at member
        rcases member with rfl | remaining
        · exact current.branches.not_guard change.guardCode atSite atMember
        · exact outerAway group remaining atSite atMember)
    have updatedBody : StructuredCode emit types functions returns locals
        (resolvedCode after.function.code.val (⟨fixups.val, label.target⟩ :: pending)) jumpTables
        (⟨scope.front, scope.results, scope.results, label.target, before.function.code.val.length,
          [], [], normal, label.branchLive⟩ :: labels)
        scope.input scope.source (scope.entry + 1) before.function.code.val.length (scope.front ++ scope.results) := by
      rw [resolved]
      have labelEq : oldLabel = ⟨scope.front, scope.results, scope.results, label.target,
          before.function.code.val.length, [], [], normal, label.branchLive⟩ := by
        have branchEq : oldLabel.branchTypes = scope.results := by
          simpa [SourceScope.branchTypes, form] using oldShape.branchTypes
        have frontEq : label.front = scope.front := oldShape.front
        have resultEq : label.resultTypes = scope.results := oldShape.results
        have branchEq' : label.branchTypes = scope.results := branchEq
        simp only [oldLabel, frontEq, resultEq, branchEq']
      simpa only [labelEq, bodyStart] using body.extend emitted
    have skip : IfSkip (resolvedCode after.function.code.val (⟨fixups.val, label.target⟩ :: pending))
        before.function.code.val.length noEntry label.target normal := by
      rw [resolved]
      exact .emitted ⟨resolvedCode before.function.code.val
        (⟨[guard], noEntry⟩ :: ⟨frame.fixups.val, label.target⟩ :: pending), [],
        by simp, resolved_code_length _ _, by
          cases normal <;> simpa using change.noPosition⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [resolved]
      exact (saved.extend emitted).change_current rfl rfl
        (scope.begin_else_arguments bt condition _ noEntry normal form)
    · simpa only [next, SourceScope.begin_else, SourceScope.input, change.length] using
        StructuredPrefix.empty emit types functions returns locals
          (resolvedCode after.function.code.val (⟨fixups.val, label.target⟩ :: pending))
          (label :: labels) scope.input noEntry.val
    · refine .cons next label ?_ ?_
      · apply StructuredElseEvidence.begin_else entered conditionSlot
        · rw [resolved]; exact fetch_extend guardFound emitted
        · exact updatedBody
        · exact skip
      · rw [resolved]
        exact arms.outer.extend emitted
  refine ⟨⟨localsEq, layout, change.sites invariant.sites, ?_⟩, ?_⟩
  · intro label labels groups plans shape parentShapes
    have outcome := advance label labels groups plans shape parentShapes
    exact ⟨outcome.1, outcome.2.1⟩
  · intro label labels groups plans shape parentShapes
    exact (advance label labels groups plans shape parentShapes).2.2

end Itasca.Compiler

end

/-! ## StructuredUniversalDormantElse -/

section

namespace Itasca.Compiler
open Aeneas.Std

/-- An omitted IF arm changes only the source cursor and frame kind at ELSE.
Its parents retain their prefixes, without assigning code to either omitted arm. -/
theorem StructuredUniversalDormant.begin_else {jumpTables : List Aeneas.Std.U32} {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents scope}
    (invariant : StructuredUniversalDormant (jumpTables := jumpTables) emit before types functions returns locals parents scope)
    (completed : StructuredUniversalElse (jumpTables := jumpTables) emit before types functions returns locals parents scope)
    (prior : List runtime.compiler.Frame) (frame : runtime.compiler.Frame)
    (beforeFrames : before.frames.val = prior ++ [frame])
    (afterFrames : after.frames.val = prior ++ [{frame with kind := .Else, if_pc := none}])
    (kind : frame.kind = .Then) (noGuard : frame.if_pc = none)
    (codeEq : after.function.code = before.function.code)
    (localsEq : compilerLocals after = locals)
    (bt : blocktype) (condition noEntry : U32) (yesExit : Nat) (normal : Bool)
    (form : scope.form = .then_ bt condition) :
    StructuredUniversalDormant (jumpTables := jumpTables) emit after types functions returns locals parents
      (scope.begin_else bt condition yesExit noEntry normal) ∧
    StructuredUniversalElse (jumpTables := jumpTables) emit after types functions returns locals parents
      (scope.begin_else bt condition yesExit noEntry normal) := by
  let next := scope.begin_else bt condition yesExit noEntry normal
  have previous : ∀ label labels groups,
      FramePlans after.function.code.val.length locals after.frames.val (label :: labels) groups →
      FramePlans before.function.code.val.length locals before.frames.val (label :: labels) groups := by
    intro label labels groups plans
    rw [afterFrames] at plans
    obtain ⟨top, outer, pending, target, sameLabels, grouped, outerPlans, future⟩ := plans.pop
    have same : top = label ∧ outer = labels := by simpa using sameLabels.symm
    obtain ⟨topEq, outerEq⟩ := same
    subst top outer
    have oldFuture : FrameFuture before.function.code.val.length locals frame label target := by
      refine ⟨future.height, future.results, ?_, ?_, ?_, ?_, ?_, future.marked, ?_, ?_⟩
      · simpa [kind] using future.branchWidth
      · simpa only [codeEq] using future.normalBound
      · intro _; simpa only [codeEq] using future.forwardBound (by simp)
      · simp [kind]
      · simp [kind]
      · simp [kind]
      · simp [noGuard]
    have oldOuter : FramePlans before.function.code.val.length locals prior labels pending := by
      simpa only [codeEq] using outerPlans
    have result := FramePlans.push oldOuter frame label target oldFuture
    rw [← beforeFrames] at result
    have groupsEq : groups = frameGroups frame label target ++ pending := by
      simpa [frameGroups, noGuard] using grouped
    simpa only [groupsEq] using result
  refine ⟨⟨invariant.unentered, localsEq, ?_, ?_⟩, ?_⟩
  · intro f member
    rw [afterFrames] at member
    rcases List.mem_append.mp member with old | fresh
    · simpa only [codeEq] using invariant.sites f (by rw [beforeFrames]; exact List.mem_append_left _ old)
    · simp only [List.mem_singleton] at fresh
      subst f
      have sites := invariant.sites frame (by simp [beforeFrames])
      exact ⟨by simpa only [codeEq] using sites.branches, by simp⟩
  · intro label labels groups plans shape parentShapes
    have oldShape := shape.before_else form
    have saved := invariant.prefixes label labels groups (previous label labels groups plans) oldShape parentShapes
    simpa only [codeEq] using saved.change_current (after := next) rfl rfl
      (scope.begin_else_arguments bt condition yesExit noEntry normal form)
  · intro label labels groups plans shape parentShapes
    have arms := completed label labels groups (previous label labels groups plans)
      (shape.before_else form) parentShapes
    refine .cons next label ?_ ?_
    · simp [StructuredElseEvidence, next, SourceScope.begin_else, invariant.unentered]
    · simpa only [codeEq] using arms.outer

end Itasca.Compiler

end

/-! ## StructuredElseFrames -/

section

namespace Itasca.Compiler
open Aeneas.Std
theorem StructuredElseEvidence.fresh {jumpTables : List Aeneas.Std.U32} {emit types functions returns locals code labels child label}
    (fresh : child.form.isElse = false) :
    StructuredElseEvidence (jumpTables := jumpTables) emit types functions returns locals code labels child label := by
  unfold StructuredElseEvidence
  split
  · cases form : child.form <;> simp_all [ScopeForm.isElse]
  · trivial

/-- Removing a completed physical frame removes only that frame's retained
arm. All enclosing completed arms survive the exact resolution schedule. -/
theorem StructuredUniversalElse.pop {jumpTables : List Aeneas.Std.U32} {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents parent child}
    (invariant : StructuredUniversalElse (jumpTables := jumpTables) emit before types functions returns locals (parents ++ [parent]) child)
    (frame : runtime.compiler.Frame) (label : LabelTarget) (guardTarget : U32)
    (frames : before.frames.val = after.frames.val ++ [frame])
    (future : FrameFuture before.function.code.val.length locals frame label guardTarget)
    (shape : ScopeLabel child label)
    (codeEq : after.function.code.val = resolvedCode before.function.code.val (frameGroups frame label guardTarget))
    (instruction : instr) :
    StructuredUniversalElse (jumpTables := jumpTables) emit after types functions returns locals parents (parent.advance instruction) := by
  intro parentLabel labels groups plans parentShape parentShapes
  have lengthEq : after.function.code.val.length = before.function.code.val.length := by
    simp [codeEq, resolved_code_length]
  have outer : FramePlans before.function.code.val.length locals after.frames.val (parentLabel :: labels) groups := by
    simpa only [lengthEq] using plans
  have oldParentShape : ScopeLabel parent parentLabel :=
    ⟨parentShape.front, by simpa [SourceScope.advance, SourceScope.branchTypes] using parentShape.branchTypes, parentShape.results⟩
  have allPlans := FramePlans.push outer frame label guardTarget future
  rw [← frames] at allPlans
  have allShapes : List.Forall₂ ScopeLabel (parents ++ [parent]).reverse (parentLabel :: labels) := by
    simpa using List.Forall₂.cons oldParentShape parentShapes
  have arms := invariant label (parentLabel :: labels) _ allPlans shape allShapes
  rw [codeEq, ← resolved_code_append_groups]
  have outerArms : StructuredElseFrames (jumpTables := jumpTables) emit types functions returns locals
      (resolvedCode before.function.code.val (frameGroups frame label guardTarget ++ groups))
      (parent :: parents.reverse) (parentLabel :: labels) := by
    simpa using arms.outer
  exact outerArms.advance instruction

/-- Opening a fresh non-ELSE scope preserves completed arms in the saved
parent chain. No completed arm is attributed to the new empty child. -/
theorem StructuredUniversalElse.open_plain {jumpTables : List Aeneas.Std.U32} {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current}
    (invariant : StructuredUniversalElse (jumpTables := jumpTables) emit before types functions returns locals parents current)
    (sites : ∀ frame ∈ before.frames.val, FrameSites before.function.code.val frame)
    (child : SourceScope) (frame : runtime.compiler.Frame) (emitted : List Bytecode)
    (fresh : child.form.isElse = false)
    (codeEq : after.function.code.val = before.function.code.val ++ emitted)
    (framesEq : after.frames.val = before.frames.val ++ [frame])
    (noGuard : frame.if_pc = none) (noBranches : frame.fixups.val = []) :
    StructuredUniversalElse (jumpTables := jumpTables) emit after types functions returns locals (parents ++ [current]) child := by
  intro label labels groups plans shape parentShapes
  have order : before.function.code.val.length ≤ after.function.code.val.length := by simp [codeEq]
  rw [framesEq] at plans
  obtain ⟨top, outer, pending, target, labelsEq, groupsEq, priorPlans, future⟩ := plans.pop
  simp only [List.cons.injEq] at labelsEq
  obtain ⟨rfl, rfl⟩ := labelsEq
  have simplified : groups = ⟨[], label.target⟩ :: pending := by
    simpa [frameGroups, noGuard, noBranches] using groupsEq
  rw [simplified]
  have resolve : resolvedCode after.function.code.val (⟨[], label.target⟩ :: pending) =
      resolvedCode before.function.code.val pending ++ emitted := by
    simp only [resolvedCode, patchCode, codeEq]
    exact resolved_code_append_code _ _ _ (priorPlans.inside sites)
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append] at parentShapes ⊢
  cases parentShapes with
  | @cons _ parentLabel _ outerLabels parentShape parentShapes =>
    have arms := invariant parentLabel outerLabels pending (priorPlans.before order) parentShape parentShapes
    rw [resolve]
    exact .cons child label (StructuredElseEvidence.fresh fresh) (arms.extend emitted)

/-- The fresh IF guard resolves only the new instruction, leaving every
completed parent arm as an exact prefix of the resolved code. -/
theorem StructuredUniversalElse.open_if {jumpTables : List Aeneas.Std.U32} {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current}
    (invariant : StructuredUniversalElse (jumpTables := jumpTables) emit before types functions returns locals parents current)
    (sites : ∀ frame ∈ before.frames.val, FrameSites before.function.code.val frame)
    (child : SourceScope) (frame : runtime.compiler.Frame) (condition : U32) (site : Usize)
    (fresh : child.form.isElse = false) (position : site.val = before.function.code.val.length)
    (codeEq : after.function.code.val = before.function.code.val ++ [.JumpIfZero condition core.num.U32.MAX])
    (framesEq : after.frames.val = before.frames.val ++ [frame])
    (guardEq : frame.if_pc = some site) (noBranches : frame.fixups.val = []) :
    StructuredUniversalElse (jumpTables := jumpTables) emit after types functions returns locals (parents ++ [current]) child := by
  intro label labels groups plans shape parentShapes
  have order : before.function.code.val.length ≤ after.function.code.val.length := by simp [codeEq]
  rw [framesEq] at plans
  obtain ⟨top, outer, pending, target, labelsEq, groupsEq, priorPlans, future⟩ := plans.pop
  simp only [List.cons.injEq] at labelsEq
  obtain ⟨rfl, rfl⟩ := labelsEq
  have simplified : groups = ⟨[site], target⟩ :: ⟨[], label.target⟩ :: pending := by
    simpa [frameGroups, guardEq, noBranches] using groupsEq
  rw [simplified]
  have resolve : resolvedCode after.function.code.val (⟨[site], target⟩ :: ⟨[], label.target⟩ :: pending) =
      resolvedCode before.function.code.val pending ++ [.JumpIfZero condition target] := by
    change resolvedCode after.function.code.val (⟨[site], target⟩ :: pending) = _
    rw [codeEq]
    exact resolved_code_open_guard _ _ condition core.num.U32.MAX target site position (priorPlans.inside sites)
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append] at parentShapes ⊢
  cases parentShapes with
  | @cons _ parentLabel _ outerLabels parentShape parentShapes =>
    have arms := invariant parentLabel outerLabels pending (priorPlans.before order) parentShape parentShapes
    rw [resolve]
    exact .cons child label (StructuredElseEvidence.fresh fresh) (arms.extend _)

end Itasca.Compiler

end

/-! ## StructuredPrefixControl -/

section

namespace Itasca.Compiler
open Aeneas.Std

/-- Closing a block fills its inner source-continuation metadata from the
surrounding prefix hole, retaining literal normal and branch exit coordinates. -/
theorem StructuredPrefix.block {jumpTables : List U32} {emit types functions returns locals code labels front params results body bt pc exit normalLive branchLive}
    (signature : BlockSignature types bt params results)
    (bodyCode : StructuredCode emit types functions returns locals code jumpTables
      (⟨front, results, results, exit, exit.val, [], [], normalLive, branchLive⟩ :: labels)
      (front ++ params) body pc exit.val (front ++ results)) :
    StructuredPrefix (jumpTables := jumpTables) emit types functions returns locals code labels (front ++ params) [.BLOCK bt body]
      pc exit.val (front ++ results) := by
  intro suffix tail next final rest
  have bodyCode := bodyCode.extend suffix
  have order := rest.pc_le_next
  apply StructuredCode.block (normalLive := normalLive) (branchLive := branchLive) signature ?_ (fun _ => rest) (fun _ => rest)
    ⟨bodyCode.pc_le_next.trans order, rest.next_le_length⟩
  apply bodyCode.relabel
  exact .cons ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (LabelsShape.refl _)

theorem StructuredDeadPrefix.block {jumpTables : List U32} {emit types functions returns locals code labels front params results body bt pc exit}
    (signature : BlockSignature types bt params results)
    (bodyCode : StructuredCode emit types functions returns locals code jumpTables
      (⟨front, results, results, exit, exit.val, [], [], false, false⟩ :: labels)
      (front ++ params) body pc exit.val (front ++ results)) :
    StructuredDeadPrefix (jumpTables := jumpTables) emit types functions returns locals code labels (front ++ params) [.BLOCK bt body]
      pc exit.val := by
  intro suffix tail next final order bound
  have bodyCode := bodyCode.extend suffix
  apply StructuredCode.block (normalExit := exit.val) (branchExit := exit) (normalLive := false) (branchLive := false) signature ?_ (by simp) (by simp) ⟨bodyCode.pc_le_next.trans order, bound⟩
  apply bodyCode.relabel
  exact .cons ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (LabelsShape.refl _)

theorem StructuredPrefix.loop {jumpTables : List U32} {emit types functions returns locals code labels front params results body bt entry exit normalLive}
    (signature : BlockSignature types bt params results)
    (head : code[entry.val]? = some .LoopHead)
    (bodyCode : StructuredCode emit types functions returns locals code jumpTables
      (⟨front, params, results, entry, exit, [.LOOP bt body], [], normalLive, true⟩ :: labels)
      (front ++ params) body (entry.val + 1) exit (front ++ results)) :
    StructuredPrefix (jumpTables := jumpTables) emit types functions returns locals code labels (front ++ params) [.LOOP bt body]
      entry.val exit (front ++ results) := by
  intro suffix tail next final rest
  have bodyCode := bodyCode.extend suffix
  have head := fetch_extend head suffix
  have bodyOrder := bodyCode.pc_le_next
  have order := rest.pc_le_next
  apply StructuredCode.loop (normalLive := normalLive) signature head ?_ (fun _ => rest) ⟨by omega, rest.next_le_length⟩
  apply bodyCode.relabel
  exact .cons ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (LabelsShape.refl _)

theorem StructuredDeadPrefix.loop {jumpTables : List U32} {emit types functions returns locals code labels front params results body bt entry exit}
    (signature : BlockSignature types bt params results)
    (head : code[entry.val]? = some .LoopHead)
    (bodyCode : StructuredCode emit types functions returns locals code jumpTables
      (⟨front, params, results, entry, exit, [.LOOP bt body], [], false, true⟩ :: labels)
      (front ++ params) body (entry.val + 1) exit (front ++ results)) :
    StructuredDeadPrefix (jumpTables := jumpTables) emit types functions returns locals code labels (front ++ params) [.LOOP bt body] entry.val exit := by
  intro suffix tail next final order bound
  have bodyCode := bodyCode.extend suffix
  have head := fetch_extend head suffix
  have bodyOrder := bodyCode.pc_le_next
  apply StructuredCode.loop (exit := exit) (normalLive := false) signature head ?_ (by simp) ⟨by omega, bound⟩
  apply bodyCode.relabel
  exact .cons ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (LabelsShape.refl _)

theorem StructuredPrefix.if_else {jumpTables : List U32} {emit types functions returns locals code labels front params results yes no bt pc yesExit noEntry exit cond yesNormal yesBranch noNormal noBranch}
    (signature : BlockSignature types bt params results)
    (condition : cond.val = slots locals + slots (front ++ params))
    (guard : code[pc]? = some (.JumpIfZero cond noEntry))
    (yesCode : StructuredCode emit types functions returns locals code jumpTables
      (⟨front, results, results, exit, yesExit, [], [], yesNormal, yesBranch⟩ :: labels)
      (front ++ params) yes (pc + 1) yesExit (front ++ results))
    (skip : IfSkip code yesExit noEntry exit yesNormal)
    (noCode : StructuredCode emit types functions returns locals code jumpTables
      (⟨front, results, results, exit, exit.val, [], [], noNormal, noBranch⟩ :: labels)
      (front ++ params) no noEntry.val exit.val (front ++ results)) :
    StructuredPrefix (jumpTables := jumpTables) emit types functions returns locals code labels (front ++ params ++ [.I32]) [.IFELSE bt yes no]
      pc exit.val (front ++ results) := by
  intro suffix tail next final rest
  have yesCode := yesCode.extend suffix
  have noCode := noCode.extend suffix
  have guard := fetch_extend guard suffix
  have skip := skip.extend suffix
  have yesOrder := yesCode.pc_le_next
  have skipOrder := skip.pc_le_next
  have noOrder := noCode.pc_le_next
  have order := rest.pc_le_next
  apply StructuredCode.ifElse (yesNormal := yesNormal) (yesBranch := yesBranch) (noNormal := noNormal) (noBranch := noBranch) signature condition guard ?_ skip ?_ (fun _ => rest)
    ⟨by omega, by omega, rest.next_le_length⟩
  · apply yesCode.relabel
    exact .cons ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (LabelsShape.refl _)
  · apply noCode.relabel
    exact .cons ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (LabelsShape.refl _)

end Itasca.Compiler

end

/-! ## StructuredPrefixElse -/

section

namespace Itasca.Compiler
open Aeneas.Std

theorem StructuredDeadPrefix.if_else_skip {jumpTables : List Aeneas.Std.U32} {emit types functions returns locals code labels front params results yes no bt pc yesExit noEntry exit cond}
    (signature : BlockSignature types bt params results)
    (condition : cond.val = slots locals + slots (front ++ params))
    (guard : code[pc]? = some (.JumpIfZero cond noEntry))
    (yesCode : StructuredCode emit types functions returns locals code jumpTables
      (⟨front, results, results, exit, yesExit, [], [], false, false⟩ :: labels)
      (front ++ params) yes (pc + 1) yesExit (front ++ results))
    (skip : IfSkip code yesExit noEntry exit false)
    (noCode : StructuredCode emit types functions returns locals code jumpTables
      (⟨front, results, results, exit, exit.val, [], [], false, false⟩ :: labels)
      (front ++ params) no noEntry.val exit.val (front ++ results)) :
    StructuredDeadPrefix (jumpTables := jumpTables) emit types functions returns locals code labels (front ++ params ++ [.I32]) [.IFELSE bt yes no]
      pc exit.val := by
  intro suffix tail next final order bound
  have yesCode := yesCode.extend suffix
  have noCode := noCode.extend suffix
  have guard := fetch_extend guard suffix
  have skip := skip.extend suffix
  have yesOrder := yesCode.pc_le_next
  have skipOrder := skip.pc_le_next
  have noOrder := noCode.pc_le_next
  apply StructuredCode.ifElse (yesExit := yesExit) (exit := exit) (yesNormal := false) (yesBranch := false) (noNormal := false) (noBranch := false) signature condition guard ?_ skip ?_ (by simp)
    ⟨by omega, by omega, bound⟩
  · apply yesCode.relabel
    exact .cons ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (LabelsShape.refl _)
  · apply noCode.relabel
    exact .cons ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (LabelsShape.refl _)

end Itasca.Compiler

end

/-! ## StructuredUniversalCloseDeadElse -/

section

namespace Itasca.Compiler
open Aeneas.Std

/-- END of an explicit ELSE obtains both arm relations from retained uniform
prefixes, resolves the shared exit, and retains a terminal outer source prefix. -/
theorem StructuredCompletedPrefix.close_else_dead {jumpTables : List Aeneas.Std.U32} {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents parent child}
    (invariant : StructuredCompletedPrefix (jumpTables := jumpTables) emit before types functions returns locals (parents ++ [parent]) child false)
    (completed : StructuredUniversalElse (jumpTables := jumpTables) emit before types functions returns locals (parents ++ [parent]) child)
    (frame : runtime.compiler.Frame) (target : U32) (bt : blocktype)
    (condition noEntry : U32) (yes : List instr) (yesExit : Nat) (yesNormal : Bool)
    (frames : before.frames.val = after.frames.val ++ [frame])
    (kind : frame.kind = .Else) (noGuard : frame.if_pc = none)
    (height : frame.height.val = slots locals + slots child.front)
    (width : frame.results.val = slots child.results)
    (position : target.val = before.function.code.val.length)
    (codeEq : after.function.code.val = patchCode before.function.code.val frame.fixups.val target)
    (localsEq : compilerLocals after = locals)
    (noBranches : frame.end_reachable = false) (yesDead : yesNormal = false)
    (form : child.form = .else_ bt condition yes yesExit noEntry yesNormal)
    (parentEntered : parent.entered = true) (childEntered : child.entered = true)
    (signature : BlockSignature types bt child.params child.results) :
    StructuredUniversalTerminal (jumpTables := jumpTables) emit after types functions returns locals parents
      (parent.advance (.IFELSE bt yes child.source)) ∧
    StructuredUniversalElse (jumpTables := jumpTables) emit after types functions returns locals parents
      (parent.advance (.IFELSE bt yes child.source)) := by
  have lengthEq : after.function.code.val.length = before.function.code.val.length := by
    simp [codeEq, patch_code_length]
  have advance : ∀ parentLabel labels groups,
      FramePlans after.function.code.val.length locals after.frames.val (parentLabel :: labels) groups →
      ScopeLabel (parent.advance (.IFELSE bt yes child.source)) parentLabel →
      List.Forall₂ ScopeLabel parents.reverse labels →
      StructuredParentPrefixes (jumpTables := jumpTables) emit types functions returns locals (resolvedCode after.function.code.val groups)
        parents labels (parent.advance (.IFELSE bt yes child.source)) ∧
      StructuredDeadPrefix (jumpTables := jumpTables) emit types functions returns locals (resolvedCode after.function.code.val groups)
        (parentLabel :: labels) parent.input (parent.source ++ [.IFELSE bt yes child.source])
        parent.bodyPc after.function.code.val.length ∧
      StructuredElseFrames (jumpTables := jumpTables) emit types functions returns locals (resolvedCode after.function.code.val groups)
        (parent.advance (.IFELSE bt yes child.source) :: parents.reverse) (parentLabel :: labels) := by
    intro parentLabel labels groups plans shape parentShapes
    have oldParentShape : ScopeLabel parent parentLabel :=
      ⟨shape.front, by simpa [SourceScope.advance, SourceScope.branchTypes] using shape.branchTypes, shape.results⟩
    let label : LabelTarget := ⟨child.front, child.results, child.results, target, target.val, [], [], false, frame.end_reachable⟩
    have future : FrameFuture before.function.code.val.length locals frame label 0#u32 := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro _; exact height
      · intro _; exact width
      · intro _; simpa [kind, label] using width
      · exact Nat.le_of_eq position.symm
      · intro _; exact Nat.le_of_eq position.symm
      · simp [kind]
      · simp [kind]
      · exact fun h => h
      · intros; rfl
      · simp [noGuard]
    have outer : FramePlans before.function.code.val.length locals after.frames.val (parentLabel :: labels) groups := by
      simpa only [lengthEq] using plans
    have allPlans := FramePlans.push outer frame label 0#u32 future
    rw [← frames] at allPlans
    have normalized : FramePlans before.function.code.val.length locals before.frames.val
        (label :: parentLabel :: labels) (⟨frame.fixups.val, target⟩ :: groups) := by
      simpa [frameGroups, noGuard, label] using allPlans
    have childShape : ScopeLabel child label := by
      refine ⟨rfl, ?_, rfl⟩
      simp [SourceScope.branchTypes, form, label]
    have allShapes : List.Forall₂ ScopeLabel (parents ++ [parent]).reverse (parentLabel :: labels) := by
      simpa using List.Forall₂.cons oldParentShape parentShapes
    obtain ⟨saved, noCode⟩ := invariant.prefixes label (parentLabel :: labels) _ normalized childShape allShapes position rfl
    have allArms := completed label (parentLabel :: labels) _ normalized childShape allShapes
    have yesEvidence : StructuredElseEvidence (jumpTables := jumpTables) emit types functions returns locals
        (resolvedCode before.function.code.val (⟨frame.fixups.val, target⟩ :: groups))
        (parentLabel :: labels) child label := by
      cases allArms with
      | cons _ _ evidence _ => exact evidence
    simp only [StructuredElseEvidence, childEntered, ite_true, form] at yesEvidence
    obtain ⟨conditionSlot, guardFound, yesCode, skip, noStart⟩ := yesEvidence
    obtain ⟨outerSaved, _, _, parentSaved⟩ := saved.pop
    have closed : StructuredDeadPrefix (jumpTables := jumpTables) emit types functions returns locals
        (resolvedCode before.function.code.val (⟨frame.fixups.val, target⟩ :: groups))
        (parentLabel :: labels) child.arguments [.IFELSE bt yes child.source] child.entry target.val := by
      have body : StructuredCode emit types functions returns locals
          (resolvedCode before.function.code.val (⟨frame.fixups.val, target⟩ :: groups)) jumpTables
          (label :: parentLabel :: labels) child.input child.source noEntry.val target.val
          (child.front ++ child.results) := by
        simpa only [noStart, position] using noCode
      have yesCode' := yesCode
      have body' := body
      simp only [label, noBranches, yesDead] at yesCode' body'
      have skip' : IfSkip (resolvedCode before.function.code.val (⟨frame.fixups.val, target⟩ :: groups)) yesExit noEntry target false := by simpa only [label, yesDead] using skip
      simpa [SourceScope.arguments, SourceScope.input, form] using
        StructuredDeadPrefix.if_else_skip signature conditionSlot guardFound yesCode' skip' body'
    have restored := parentSaved.resume_dead parentEntered childEntered closed
    have resolve : resolvedCode after.function.code.val groups =
        resolvedCode before.function.code.val (⟨frame.fixups.val, target⟩ :: groups) := by
      simp only [codeEq, resolvedCode]
    refine ⟨?_, ?_, ?_⟩
    · rw [resolve]
      exact outerSaved.advance_current (.IFELSE bt yes child.source)
    · simpa only [resolve, lengthEq, position] using restored
    · rw [resolve]
      have outerArms : StructuredElseFrames (jumpTables := jumpTables) emit types functions returns locals
          (resolvedCode before.function.code.val (⟨frame.fixups.val, target⟩ :: groups))
          (parent :: parents.reverse) (parentLabel :: labels) := by
        simpa using allArms.outer
      exact outerArms.advance (.IFELSE bt yes child.source)
  refine ⟨⟨localsEq, ?_, ?_⟩, ?_⟩
  · intro f member
    have original := invariant.sites f (by rw [frames]; exact List.mem_append_left _ member)
    simpa only [codeEq] using original.patch frame.fixups.val target
  · intro label labels groups plans shape parentShapes
    have outcome := advance label labels groups plans shape parentShapes
    exact ⟨outcome.1, outcome.2.1⟩
  · intro label labels groups plans shape parentShapes
    exact (advance label labels groups plans shape parentShapes).2.2

end Itasca.Compiler

end

end

/-! ## CloseIfAndBlocks -/

section

/-!
Proofs for Runtime / Compiler / Local / Control / Structured.

This module collects CloseIfAndBlocks, LoopAndCallPrefixes, CloseIf.
Each section documents its contracts and consumers.
-/

/-! ## CloseIfAndBlocks -/

section

open Itasca.Representation

/-!
# Close If And Blocks

ELSE closure and block prefixes preserve the structured compiler relation through their resolved exit coordinates.
-/

/-! ## StructuredUniversalCloseElse -/

section

namespace Itasca.Compiler
open Aeneas.Std

/-- END of an explicit ELSE obtains both arm relations from retained uniform
prefixes, resolves the shared exit, and resumes the suspended outer source. -/
theorem StructuredCompletedPrefix.close_else {jumpTables : List Aeneas.Std.U32} {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents parent child normal}
    (invariant : StructuredCompletedPrefix (jumpTables := jumpTables) emit before types functions returns locals (parents ++ [parent]) child normal)
    (completed : StructuredUniversalElse (jumpTables := jumpTables) emit before types functions returns locals (parents ++ [parent]) child)
    (frame : runtime.compiler.Frame) (target : U32) (bt : blocktype)
    (condition noEntry : U32) (yes : List instr) (yesExit : Nat) (yesNormal : Bool)
    (frames : before.frames.val = after.frames.val ++ [frame])
    (kind : frame.kind = .Else) (noGuard : frame.if_pc = none)
    (height : frame.height.val = slots locals + slots child.front)
    (width : frame.results.val = slots child.results)
    (position : target.val = before.function.code.val.length)
    (codeEq : after.function.code.val = patchCode before.function.code.val frame.fixups.val target)
    (localsEq : compilerLocals after = locals)
    (layout : CompilerLayout after (child.front ++ child.results))
    (form : child.form = .else_ bt condition yes yesExit noEntry yesNormal)
    (parentEntered : parent.entered = true) (childEntered : child.entered = true)
    (signature : BlockSignature types bt child.params child.results) :
    StructuredUniversalPrefix (jumpTables := jumpTables) emit after types functions returns locals parents
      (parent.advance (.IFELSE bt yes child.source)) (child.front ++ child.results) ∧
    StructuredUniversalElse (jumpTables := jumpTables) emit after types functions returns locals parents
      (parent.advance (.IFELSE bt yes child.source)) := by
  have lengthEq : after.function.code.val.length = before.function.code.val.length := by
    simp [codeEq, patch_code_length]
  have advance : ∀ parentLabel labels groups,
      FramePlans after.function.code.val.length locals after.frames.val (parentLabel :: labels) groups →
      ScopeLabel (parent.advance (.IFELSE bt yes child.source)) parentLabel →
      List.Forall₂ ScopeLabel parents.reverse labels →
      StructuredParentPrefixes (jumpTables := jumpTables) emit types functions returns locals (resolvedCode after.function.code.val groups)
        parents labels (parent.advance (.IFELSE bt yes child.source)) ∧
      StructuredPrefix (jumpTables := jumpTables) emit types functions returns locals (resolvedCode after.function.code.val groups)
        (parentLabel :: labels) parent.input (parent.source ++ [.IFELSE bt yes child.source])
        parent.bodyPc after.function.code.val.length (child.front ++ child.results) ∧
      StructuredElseFrames (jumpTables := jumpTables) emit types functions returns locals (resolvedCode after.function.code.val groups)
        (parent.advance (.IFELSE bt yes child.source) :: parents.reverse) (parentLabel :: labels) := by
    intro parentLabel labels groups plans shape parentShapes
    have oldParentShape : ScopeLabel parent parentLabel :=
      ⟨shape.front, by simpa [SourceScope.advance, SourceScope.branchTypes] using shape.branchTypes, shape.results⟩
    let label : LabelTarget := ⟨child.front, child.results, child.results, target, target.val, [], [], normal, frame.end_reachable⟩
    have future : FrameFuture before.function.code.val.length locals frame label 0#u32 := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro _; exact height
      · intro _; exact width
      · intro _; simpa [kind, label] using width
      · exact Nat.le_of_eq position.symm
      · intro _; exact Nat.le_of_eq position.symm
      · simp [kind]
      · simp [kind]
      · exact fun h => h
      · intros; rfl
      · simp [noGuard]
    have outer : FramePlans before.function.code.val.length locals after.frames.val (parentLabel :: labels) groups := by
      simpa only [lengthEq] using plans
    have allPlans := FramePlans.push outer frame label 0#u32 future
    rw [← frames] at allPlans
    have normalized : FramePlans before.function.code.val.length locals before.frames.val
        (label :: parentLabel :: labels) (⟨frame.fixups.val, target⟩ :: groups) := by
      simpa [frameGroups, noGuard, label] using allPlans
    have childShape : ScopeLabel child label := by
      refine ⟨rfl, ?_, rfl⟩
      simp [SourceScope.branchTypes, form, label]
    have allShapes : List.Forall₂ ScopeLabel (parents ++ [parent]).reverse (parentLabel :: labels) := by
      simpa using List.Forall₂.cons oldParentShape parentShapes
    obtain ⟨saved, noCode⟩ := invariant.prefixes label (parentLabel :: labels) _ normalized childShape allShapes position rfl
    have allArms := completed label (parentLabel :: labels) _ normalized childShape allShapes
    have yesEvidence : StructuredElseEvidence (jumpTables := jumpTables) emit types functions returns locals
        (resolvedCode before.function.code.val (⟨frame.fixups.val, target⟩ :: groups))
        (parentLabel :: labels) child label := by
      cases allArms with
      | cons _ _ evidence _ => exact evidence
    simp only [StructuredElseEvidence, childEntered, ite_true, form] at yesEvidence
    obtain ⟨conditionSlot, guardFound, yesCode, skip, noStart⟩ := yesEvidence
    obtain ⟨outerSaved, _, _, parentSaved⟩ := saved.pop
    have closed : StructuredPrefix (jumpTables := jumpTables) emit types functions returns locals
        (resolvedCode before.function.code.val (⟨frame.fixups.val, target⟩ :: groups))
        (parentLabel :: labels) child.arguments [.IFELSE bt yes child.source] child.entry target.val
        (child.front ++ child.results) := by
      have body : StructuredCode emit types functions returns locals
          (resolvedCode before.function.code.val (⟨frame.fixups.val, target⟩ :: groups)) jumpTables
          (label :: parentLabel :: labels) child.input child.source noEntry.val target.val
          (child.front ++ child.results) := by
        simpa only [noStart, position] using noCode
      simpa [SourceScope.arguments, SourceScope.input, form, label] using
        StructuredPrefix.if_else signature conditionSlot guardFound yesCode skip body
    have restored := parentSaved.resume parentEntered childEntered closed
    have resolve : resolvedCode after.function.code.val groups =
        resolvedCode before.function.code.val (⟨frame.fixups.val, target⟩ :: groups) := by
      simp only [codeEq, resolvedCode]
    refine ⟨?_, ?_, ?_⟩
    · rw [resolve]
      exact outerSaved.advance_current (.IFELSE bt yes child.source)
    · simpa only [resolve, lengthEq, position] using restored
    · rw [resolve]
      have outerArms : StructuredElseFrames (jumpTables := jumpTables) emit types functions returns locals
          (resolvedCode before.function.code.val (⟨frame.fixups.val, target⟩ :: groups))
          (parent :: parents.reverse) (parentLabel :: labels) := by
        simpa using allArms.outer
      exact outerArms.advance (.IFELSE bt yes child.source)
  refine ⟨⟨localsEq, layout, ?_, ?_⟩, ?_⟩
  · intro f member
    have original := invariant.sites f (by rw [frames]; exact List.mem_append_left _ member)
    simpa only [codeEq] using original.patch frame.fixups.val target
  · intro label labels groups plans shape parentShapes
    have outcome := advance label labels groups plans shape parentShapes
    exact ⟨outcome.1, outcome.2.1⟩
  · intro label labels groups plans shape parentShapes
    exact (advance label labels groups plans shape parentShapes).2.2

end Itasca.Compiler

end

/-! ## StructuredUniversalRoot -/

section

namespace Itasca.Compiler
open Aeneas.Std
theorem StructuredUniversalPrefix.root_finish {jumpTables : List Aeneas.Std.U32} {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals current}
    (invariant : StructuredUniversalPrefix (jumpTables := jumpTables) emit compiler types functions returns locals [] current returns)
    (frame : runtime.compiler.Frame) (target : U32)
    (frames : compiler.frames.val = [frame]) (kind : frame.kind = .Body) (noGuard : frame.if_pc = none)
    (height : frame.height.val = slots locals) (width : frame.results.val = slots returns)
    (position : target.val = compiler.function.code.val.length)
    (form : current.form = .body) (front : current.front = []) (params : current.params = [])
    (results : current.results = returns) (start : current.bodyPc = 0) :
    StructuredCode emit types functions returns locals (patchCode compiler.function.code.val frame.fixups.val target) jumpTables
      [⟨[], returns, returns, target, target.val, [], [], true, frame.end_reachable⟩]
      [] current.source 0 target.val returns := by
  have plans := root_frame_plan compiler.function.code.val locals returns frame target true kind noGuard height width position
  rw [← frames] at plans
  have shape := root_scope_label current returns target true frame.end_reachable form front results
  have code := (invariant.prefixes _ [] _ plans shape .nil).2
  have finished := code.finish (by simp [resolved_code_length]) (by simp [NormalLive])
  simpa [resolvedCode, SourceScope.input, front, params, start, position] using finished

/-- A terminal root body closes at the actual final PC even when its result
signature is nonempty and the emitted unreachable epilogue returns zero words. -/
theorem StructuredUniversalTerminal.root_finish {jumpTables : List Aeneas.Std.U32} {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals current}
    (invariant : StructuredUniversalTerminal (jumpTables := jumpTables) emit compiler types functions returns locals [] current)
    (frame : runtime.compiler.Frame) (target : U32)
    (frames : compiler.frames.val = [frame]) (kind : frame.kind = .Body) (noGuard : frame.if_pc = none)
    (height : frame.height.val = slots locals) (width : frame.results.val = slots returns)
    (position : target.val = compiler.function.code.val.length)
    (form : current.form = .body) (front : current.front = []) (params : current.params = [])
    (results : current.results = returns) (start : current.bodyPc = 0) :
    StructuredCode emit types functions returns locals (patchCode compiler.function.code.val frame.fixups.val target) jumpTables
      [⟨[], returns, returns, target, target.val, [], [], false, frame.end_reachable⟩]
      [] current.source 0 target.val returns := by
  have plans := root_frame_plan compiler.function.code.val locals returns frame target false kind noGuard height width position
  rw [← frames] at plans
  have shape := root_scope_label current returns target false frame.end_reachable form front results
  have code := (invariant.prefixes _ [] _ plans shape .nil).2
  have finished := code.finish target.val returns (by omega) (by simp [resolved_code_length, position])
  simpa [resolvedCode, SourceScope.input, front, params, start, position] using finished

end Itasca.Compiler

end

/-! ## StructuredUniversalCloseBlock -/

section

namespace Itasca.Compiler
open Aeneas.Std

/-- Exact BLOCK END patching removes its resolution group and resumes the
suspended parent. The completed body's relation is derived from the universal
prefix, rather than supplied as a correctness premise. -/
theorem StructuredUniversalPrefix.close_block {jumpTables : List Aeneas.Std.U32} {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents parent child}
    (invariant : StructuredUniversalPrefix (jumpTables := jumpTables) emit before types functions returns locals (parents ++ [parent]) child
      (child.front ++ child.results))
    (frame : runtime.compiler.Frame) (target : U32) (bt : blocktype)
    (frames : before.frames.val = after.frames.val ++ [frame])
    (kind : frame.kind = .Block) (noGuard : frame.if_pc = none)
    (height : frame.height.val = slots locals + slots child.front)
    (width : frame.results.val = slots child.results)
    (position : target.val = before.function.code.val.length)
    (codeEq : after.function.code.val = patchCode before.function.code.val frame.fixups.val target)
    (localsEq : compilerLocals after = locals)
    (layout : CompilerLayout after (child.front ++ child.results))
    (form : child.form = .block bt) (entry : child.entry = child.bodyPc)
    (parentEntered : parent.entered = true) (childEntered : child.entered = true)
    (signature : BlockSignature types bt child.params child.results) :
    StructuredUniversalPrefix (jumpTables := jumpTables) emit after types functions returns locals parents
      (parent.advance (.BLOCK bt child.source)) (child.front ++ child.results) := by
  have lengthEq : after.function.code.val.length = before.function.code.val.length := by
    simp [codeEq, patch_code_length]
  refine ⟨localsEq, layout, ?_, ?_⟩
  · intro f member
    have original := invariant.sites f (by rw [frames]; exact List.mem_append_left _ member)
    simpa only [codeEq] using original.patch frame.fixups.val target
  · intro parentLabel labels groups plans shape parentShapes
    have oldParentShape : ScopeLabel parent parentLabel :=
      ⟨shape.front, by simpa [SourceScope.advance, SourceScope.branchTypes] using shape.branchTypes, shape.results⟩
    let label : LabelTarget := ⟨child.front, child.results, child.results, target, target.val, [], [], true, frame.end_reachable⟩
    have future : FrameFuture before.function.code.val.length locals frame label 0#u32 := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro _; exact height
      · intro _; exact width
      · intro _; simpa [kind, label] using width
      · exact Nat.le_of_eq position.symm
      · intro _; exact Nat.le_of_eq position.symm
      · simp [kind]
      · simp [kind]
      · exact fun h => h
      · intros; rfl
      · simp [noGuard]
    have outer : FramePlans before.function.code.val.length locals after.frames.val (parentLabel :: labels) groups := by
      simpa only [lengthEq] using plans
    have allPlans := FramePlans.push outer frame label 0#u32 future
    rw [← frames] at allPlans
    have normalized : FramePlans before.function.code.val.length locals before.frames.val
        (label :: parentLabel :: labels) (⟨frame.fixups.val, target⟩ :: groups) := by
      simpa [frameGroups, noGuard, label] using allPlans
    have childShape : ScopeLabel child label := by
      refine ⟨rfl, ?_, rfl⟩
      simp [SourceScope.branchTypes, form, label]
    have allShapes : List.Forall₂ ScopeLabel (parents ++ [parent]).reverse (parentLabel :: labels) := by
      simpa using List.Forall₂.cons oldParentShape parentShapes
    obtain ⟨saved, current⟩ := invariant.prefixes label (parentLabel :: labels) _ normalized childShape allShapes
    have bodyCode := current.finish (by simp [resolved_code_length]) (by simp [NormalLive, label])
    obtain ⟨outerSaved, _, _, parentSaved⟩ := saved.pop
    have closed : StructuredPrefix (jumpTables := jumpTables) emit types functions returns locals
        (resolvedCode before.function.code.val (⟨frame.fixups.val, target⟩ :: groups))
        (parentLabel :: labels) child.arguments [.BLOCK bt child.source] child.entry target.val
        (child.front ++ child.results) := by
      have body : StructuredCode emit types functions returns locals
          (resolvedCode before.function.code.val (⟨frame.fixups.val, target⟩ :: groups)) jumpTables
          (label :: parentLabel :: labels) (child.front ++ child.params) child.source child.bodyPc
          target.val (child.front ++ child.results) := by
        simpa only [SourceScope.input, position] using bodyCode
      simpa [SourceScope.arguments, SourceScope.input, form, entry] using StructuredPrefix.block signature body
    have restored := parentSaved.resume parentEntered childEntered closed
    have resolve : resolvedCode after.function.code.val groups =
        resolvedCode before.function.code.val (⟨frame.fixups.val, target⟩ :: groups) := by
      simp only [codeEq, resolvedCode]
    refine ⟨?_, ?_⟩
    · rw [resolve]
      exact outerSaved.advance_current (.BLOCK bt child.source)
    · simpa only [resolve, lengthEq, position, SourceScope.advance, SourceScope.input] using restored

end Itasca.Compiler

end

/-! ## StructuredUniversalCloseDeadBlock -/

section

namespace Itasca.Compiler
open Aeneas.Std

/-- A block with neither a normal exit nor a recorded forward branch leaves
its parent terminal; omitted source tails remain justified by the body. -/
theorem StructuredUniversalTerminal.close_block_dead {jumpTables : List Aeneas.Std.U32} {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents parent child}
    (invariant : StructuredUniversalTerminal (jumpTables := jumpTables) emit before types functions returns locals (parents ++ [parent]) child)
    (frame : runtime.compiler.Frame) (target : U32) (bt : blocktype)
    (frames : before.frames.val = after.frames.val ++ [frame])
    (kind : frame.kind = .Block) (noGuard : frame.if_pc = none)
    (height : frame.height.val = slots locals + slots child.front)
    (width : frame.results.val = slots child.results)
    (position : target.val = before.function.code.val.length)
    (codeEq : after.function.code.val = patchCode before.function.code.val frame.fixups.val target)
    (localsEq : compilerLocals after = locals)
    (branchDead : frame.end_reachable = false)
    (form : child.form = .block bt) (entry : child.entry = child.bodyPc)
    (parentEntered : parent.entered = true) (childEntered : child.entered = true)
    (signature : BlockSignature types bt child.params child.results) :
    StructuredUniversalTerminal (jumpTables := jumpTables) emit after types functions returns locals parents (parent.advance (.BLOCK bt child.source)) := by
  have lengthEq : after.function.code.val.length = before.function.code.val.length := by
    simp [codeEq, patch_code_length]
  refine ⟨localsEq, ?_, ?_⟩
  · intro f member
    have original := invariant.sites f (by rw [frames]; exact List.mem_append_left _ member)
    simpa only [codeEq] using original.patch frame.fixups.val target
  · intro parentLabel labels groups plans shape parentShapes
    have oldParentShape : ScopeLabel parent parentLabel :=
      ⟨shape.front, by simpa [SourceScope.advance, SourceScope.branchTypes] using shape.branchTypes, shape.results⟩
    let label : LabelTarget := ⟨child.front, child.results, child.results, target, target.val, [], [], false, frame.end_reachable⟩
    have future : FrameFuture before.function.code.val.length locals frame label 0#u32 := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro _; exact height
      · intro _; exact width
      · intro _; simpa [kind, label] using width
      · exact Nat.le_of_eq position.symm
      · intro _; exact Nat.le_of_eq position.symm
      · simp [kind]
      · simp [kind]
      · exact fun h => h
      · intros; rfl
      · simp [noGuard]
    have outer : FramePlans before.function.code.val.length locals after.frames.val (parentLabel :: labels) groups := by
      simpa only [lengthEq] using plans
    have allPlans := FramePlans.push outer frame label 0#u32 future
    rw [← frames] at allPlans
    have normalized : FramePlans before.function.code.val.length locals before.frames.val
        (label :: parentLabel :: labels) (⟨frame.fixups.val, target⟩ :: groups) := by
      simpa [frameGroups, noGuard, label] using allPlans
    have childShape : ScopeLabel child label := by
      refine ⟨rfl, ?_, rfl⟩
      simp [SourceScope.branchTypes, form, label]
    have allShapes : List.Forall₂ ScopeLabel (parents ++ [parent]).reverse (parentLabel :: labels) := by
      simpa using List.Forall₂.cons oldParentShape parentShapes
    obtain ⟨saved, current⟩ := invariant.prefixes label (parentLabel :: labels) _ normalized childShape allShapes
    have bodyCode := current.finish target.val (child.front ++ child.results) (by omega) (by simp [resolved_code_length, position])
    obtain ⟨outerSaved, _, _, parentSaved⟩ := saved.pop
    have closed : StructuredDeadPrefix (jumpTables := jumpTables) emit types functions returns locals
        (resolvedCode before.function.code.val (⟨frame.fixups.val, target⟩ :: groups))
        (parentLabel :: labels) child.arguments [.BLOCK bt child.source] child.entry target.val := by
      have body : StructuredCode emit types functions returns locals
          (resolvedCode before.function.code.val (⟨frame.fixups.val, target⟩ :: groups)) jumpTables
          (label :: parentLabel :: labels) (child.front ++ child.params) child.source child.bodyPc
          target.val (child.front ++ child.results) := by
        simpa only [SourceScope.input, position] using bodyCode
      simpa [SourceScope.arguments, SourceScope.input, form, entry] using
        StructuredDeadPrefix.block signature (by simpa [label, branchDead] using body)
    have restored := parentSaved.resume_dead parentEntered childEntered closed
    have resolve : resolvedCode after.function.code.val groups =
        resolvedCode before.function.code.val (⟨frame.fixups.val, target⟩ :: groups) := by
      simp only [codeEq, resolvedCode]
    refine ⟨?_, ?_⟩
    · rw [resolve]
      exact outerSaved.advance_current (.BLOCK bt child.source)
    · simpa only [resolve, lengthEq, position, SourceScope.advance, SourceScope.input] using restored

/-- A recorded branch to a block exit restores the parent continuation even
when the last source path in the block is terminal. -/
theorem StructuredUniversalTerminal.close_block_resume {jumpTables : List Aeneas.Std.U32} {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents parent child}
    (invariant : StructuredUniversalTerminal (jumpTables := jumpTables) emit before types functions returns locals (parents ++ [parent]) child)
    (frame : runtime.compiler.Frame) (target : U32) (bt : blocktype)
    (frames : before.frames.val = after.frames.val ++ [frame])
    (kind : frame.kind = .Block) (noGuard : frame.if_pc = none)
    (height : frame.height.val = slots locals + slots child.front)
    (width : frame.results.val = slots child.results)
    (position : target.val = before.function.code.val.length)
    (codeEq : after.function.code.val = patchCode before.function.code.val frame.fixups.val target)
    (localsEq : compilerLocals after = locals)
    (layout : CompilerLayout after (child.front ++ child.results))
    (branchLive : frame.end_reachable = true)
    (form : child.form = .block bt) (entry : child.entry = child.bodyPc)
    (parentEntered : parent.entered = true) (childEntered : child.entered = true)
    (signature : BlockSignature types bt child.params child.results) :
    StructuredUniversalPrefix (jumpTables := jumpTables) emit after types functions returns locals parents
      (parent.advance (.BLOCK bt child.source)) (child.front ++ child.results) := by
  have lengthEq : after.function.code.val.length = before.function.code.val.length := by
    simp [codeEq, patch_code_length]
  refine ⟨localsEq, layout, ?_, ?_⟩
  · intro f member
    have original := invariant.sites f (by rw [frames]; exact List.mem_append_left _ member)
    simpa only [codeEq] using original.patch frame.fixups.val target
  · intro parentLabel labels groups plans shape parentShapes
    have oldParentShape : ScopeLabel parent parentLabel :=
      ⟨shape.front, by simpa [SourceScope.advance, SourceScope.branchTypes] using shape.branchTypes, shape.results⟩
    let label : LabelTarget := ⟨child.front, child.results, child.results, target, target.val, [], [], false, frame.end_reachable⟩
    have future : FrameFuture before.function.code.val.length locals frame label 0#u32 := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro _; exact height
      · intro _; exact width
      · intro _; simpa [kind, label] using width
      · exact Nat.le_of_eq position.symm
      · intro _; exact Nat.le_of_eq position.symm
      · simp [kind]
      · simp [kind]
      · exact fun h => h
      · intros; rfl
      · simp [noGuard]
    have outer : FramePlans before.function.code.val.length locals after.frames.val (parentLabel :: labels) groups := by
      simpa only [lengthEq] using plans
    have allPlans := FramePlans.push outer frame label 0#u32 future
    rw [← frames] at allPlans
    have normalized : FramePlans before.function.code.val.length locals before.frames.val
        (label :: parentLabel :: labels) (⟨frame.fixups.val, target⟩ :: groups) := by
      simpa [frameGroups, noGuard, label] using allPlans
    have childShape : ScopeLabel child label := by
      refine ⟨rfl, ?_, rfl⟩
      simp [SourceScope.branchTypes, form, label]
    have allShapes : List.Forall₂ ScopeLabel (parents ++ [parent]).reverse (parentLabel :: labels) := by
      simpa using List.Forall₂.cons oldParentShape parentShapes
    obtain ⟨saved, current⟩ := invariant.prefixes label (parentLabel :: labels) _ normalized childShape allShapes
    have bodyCode := current.finish target.val (child.front ++ child.results) (by omega) (by simp [resolved_code_length, position])
    obtain ⟨outerSaved, _, _, parentSaved⟩ := saved.pop
    have closed : StructuredPrefix (jumpTables := jumpTables) emit types functions returns locals
        (resolvedCode before.function.code.val (⟨frame.fixups.val, target⟩ :: groups))
        (parentLabel :: labels) child.arguments [.BLOCK bt child.source] child.entry target.val
        (child.front ++ child.results) := by
      have body : StructuredCode emit types functions returns locals
          (resolvedCode before.function.code.val (⟨frame.fixups.val, target⟩ :: groups)) jumpTables
          (label :: parentLabel :: labels) (child.front ++ child.params) child.source child.bodyPc
          target.val (child.front ++ child.results) := by
        simpa only [SourceScope.input, position] using bodyCode
      simpa [SourceScope.arguments, SourceScope.input, form, entry] using StructuredPrefix.block (branchLive := true) signature (by simpa [label, branchLive] using body)
    have restored := parentSaved.resume parentEntered childEntered closed
    have resolve : resolvedCode after.function.code.val groups =
        resolvedCode before.function.code.val (⟨frame.fixups.val, target⟩ :: groups) := by
      simp only [codeEq, resolvedCode]
    refine ⟨?_, ?_⟩
    · rw [resolve]
      exact outerSaved.advance_current (.BLOCK bt child.source)
    · simpa only [resolve, lengthEq, position, SourceScope.advance, SourceScope.input] using restored

end Itasca.Compiler

end

/-! ## StructuredIfEndPrefix -/

section

namespace Itasca.Compiler
open Aeneas.Std

/-- An implicit empty ELSE joins directly at the normal exit. Its input and
output stacks agree, so the compiler emits no skip instruction. -/
theorem StructuredPrefix.if_end {jumpTables : List Aeneas.Std.U32} {emit types functions returns locals code labels front params yes bt pc exit cond yesNormal yesBranch}
    (signature : BlockSignature types bt params params)
    (condition : cond.val = slots locals + slots (front ++ params))
    (guard : code[pc]? = some (.JumpIfZero cond exit))
    (yesCode : StructuredCode emit types functions returns locals code jumpTables
      (⟨front, params, params, exit, exit.val, [], [], yesNormal, yesBranch⟩ :: labels)
      (front ++ params) yes (pc + 1) exit.val (front ++ params)) :
    StructuredPrefix (jumpTables := jumpTables) emit types functions returns locals code labels (front ++ params ++ [.I32]) [.IFELSE bt yes []]
      pc exit.val (front ++ params) := by
  exact StructuredPrefix.if_else (noNormal := true) (noBranch := false) signature condition guard yesCode (.direct rfl rfl)
    (.nil _ _ _ yesCode.next_le_length (NormalLive.cons rfl))

end Itasca.Compiler

end

end

/-! ## LoopAndCallPrefixes -/

section

open Itasca.Representation

/-!
# Loop And Call Prefixes

Loop closure, empty prefixes and calls compose within the structured compiler relation.
-/

/-! ## StructuredUniversalCloseLoop -/

section

namespace Itasca.Compiler
open Aeneas.Std

/-- LOOP END resumes its parent only from the normal body continuation. Loop
branches retain their backward target and never become forward END fixups. -/
theorem StructuredUniversalPrefix.close_loop {jumpTables : List Aeneas.Std.U32} {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents parent child}
    (invariant : StructuredUniversalPrefix (jumpTables := jumpTables) emit before types functions returns locals (parents ++ [parent]) child
      (child.front ++ child.results))
    (frame : runtime.compiler.Frame) (target : U32) (bt : blocktype)
    (frames : before.frames.val = after.frames.val ++ [frame])
    (kind : frame.kind = .Loop) (noGuard : frame.if_pc = none) (noFixups : frame.fixups.val = [])
    (height : frame.height.val = slots locals + slots child.front)
    (inputs : frame.params.val = slots child.params) (width : frame.results.val = slots child.results)
    (position : target.val = before.function.code.val.length)
    (codeEq : after.function.code.val = before.function.code.val)
    (localsEq : compilerLocals after = locals)
    (layout : CompilerLayout after (child.front ++ child.results))
    (form : child.form = .loop bt) (entry : child.entry = frame.start_pc.val)
    (body : child.bodyPc = frame.start_pc.val + 1)
    (head : before.function.code.val[frame.start_pc.val]? = some .LoopHead)
    (parentEntered : parent.entered = true) (childEntered : child.entered = true)
    (signature : BlockSignature types bt child.params child.results) :
    StructuredUniversalPrefix (jumpTables := jumpTables) emit after types functions returns locals parents
      (parent.advance (.LOOP bt child.source)) (child.front ++ child.results) := by
  refine ⟨localsEq, layout, ?_, ?_⟩
  · intro f member
    have original := invariant.sites f (by rw [frames]; exact List.mem_append_left _ member)
    simpa only [codeEq] using original
  · intro parentLabel labels groups plans shape parentShapes
    have oldParentShape : ScopeLabel parent parentLabel :=
      ⟨shape.front, by simpa [SourceScope.advance, SourceScope.branchTypes] using shape.branchTypes, shape.results⟩
    let label : LabelTarget := ⟨child.front, child.params, child.results, frame.start_pc,
      target.val, [.LOOP bt child.source], [], true, true⟩
    have future : FrameFuture before.function.code.val.length locals frame label 0#u32 := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro _; exact height
      · intro _; exact width
      · intro _; simpa [kind, label] using inputs
      · exact Nat.le_of_eq position.symm
      · simp [kind]
      · intro _; rfl
      · intro _; rfl
      · intro _; rfl
      · simp [kind]
      · simp [noGuard]
    have outer : FramePlans before.function.code.val.length locals after.frames.val (parentLabel :: labels) groups := by
      simpa only [codeEq] using plans
    have allPlans := FramePlans.push outer frame label 0#u32 future
    rw [← frames] at allPlans
    have normalized : FramePlans before.function.code.val.length locals before.frames.val
        (label :: parentLabel :: labels) (⟨[], frame.start_pc⟩ :: groups) := by
      simpa [frameGroups, noGuard, noFixups, label] using allPlans
    have childShape : ScopeLabel child label := by
      refine ⟨rfl, ?_, rfl⟩
      simp [SourceScope.branchTypes, form, label]
    have allShapes : List.Forall₂ ScopeLabel (parents ++ [parent]).reverse (parentLabel :: labels) := by
      simpa using List.Forall₂.cons oldParentShape parentShapes
    obtain ⟨saved, current⟩ := invariant.prefixes label (parentLabel :: labels) _ normalized childShape allShapes
    simp only [resolvedCode, patchCode] at saved current
    have bodyCode := current.finish (by simp [resolved_code_length]) (by simp [NormalLive, label])
    obtain ⟨outerSaved, _, _, parentSaved⟩ := saved.pop
    have closed : StructuredPrefix (jumpTables := jumpTables) emit types functions returns locals (resolvedCode before.function.code.val groups)
        (parentLabel :: labels) child.arguments [.LOOP bt child.source] child.entry target.val
        (child.front ++ child.results) := by
      have bodyCode' : StructuredCode emit types functions returns locals (resolvedCode before.function.code.val groups) jumpTables
          (label :: parentLabel :: labels) (child.front ++ child.params) child.source
          (frame.start_pc.val + 1) target.val (child.front ++ child.results) := by
        simpa only [SourceScope.input, position, body] using bodyCode
      simpa [SourceScope.arguments, SourceScope.input, form, entry] using
        StructuredPrefix.loop signature (resolved_code_loop_head _ groups _ head) bodyCode'
    have restored := parentSaved.resume parentEntered childEntered closed
    refine ⟨?_, ?_⟩
    · rw [codeEq]
      exact outerSaved.advance_current (.LOOP bt child.source)
    · simpa only [codeEq, position, SourceScope.advance, SourceScope.input] using restored

/-- A terminal loop body keeps its parent terminal; its live backward branch
target is independent of the dead normal exit. -/
theorem StructuredUniversalTerminal.close_loop {jumpTables : List Aeneas.Std.U32} {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents parent child}
    (invariant : StructuredUniversalTerminal (jumpTables := jumpTables) emit before types functions returns locals (parents ++ [parent]) child)
    (frame : runtime.compiler.Frame) (target : U32) (bt : blocktype)
    (frames : before.frames.val = after.frames.val ++ [frame])
    (kind : frame.kind = .Loop) (noGuard : frame.if_pc = none) (noFixups : frame.fixups.val = [])
    (height : frame.height.val = slots locals + slots child.front)
    (inputs : frame.params.val = slots child.params) (width : frame.results.val = slots child.results)
    (position : target.val = before.function.code.val.length)
    (codeEq : after.function.code.val = before.function.code.val)
    (localsEq : compilerLocals after = locals)
    (form : child.form = .loop bt) (entry : child.entry = frame.start_pc.val)
    (body : child.bodyPc = frame.start_pc.val + 1)
    (head : before.function.code.val[frame.start_pc.val]? = some .LoopHead)
    (parentEntered : parent.entered = true) (childEntered : child.entered = true)
    (signature : BlockSignature types bt child.params child.results) :
    StructuredUniversalTerminal (jumpTables := jumpTables) emit after types functions returns locals parents (parent.advance (.LOOP bt child.source)) := by
  refine ⟨localsEq, ?_, ?_⟩
  · intro f member
    have original := invariant.sites f (by rw [frames]; exact List.mem_append_left _ member)
    simpa only [codeEq] using original
  · intro parentLabel labels groups plans shape parentShapes
    have oldParentShape : ScopeLabel parent parentLabel :=
      ⟨shape.front, by simpa [SourceScope.advance, SourceScope.branchTypes] using shape.branchTypes, shape.results⟩
    let label : LabelTarget := ⟨child.front, child.params, child.results, frame.start_pc,
      target.val, [.LOOP bt child.source], [], false, true⟩
    have future : FrameFuture before.function.code.val.length locals frame label 0#u32 := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro _; exact height
      · intro _; exact width
      · intro _; simpa [kind, label] using inputs
      · exact Nat.le_of_eq position.symm
      · simp [kind]
      · intro _; rfl
      · intro _; rfl
      · intro _; rfl
      · simp [kind]
      · simp [noGuard]
    have outer : FramePlans before.function.code.val.length locals after.frames.val (parentLabel :: labels) groups := by
      simpa only [codeEq] using plans
    have allPlans := FramePlans.push outer frame label 0#u32 future
    rw [← frames] at allPlans
    have normalized : FramePlans before.function.code.val.length locals before.frames.val
        (label :: parentLabel :: labels) (⟨[], frame.start_pc⟩ :: groups) := by
      simpa [frameGroups, noGuard, noFixups, label] using allPlans
    have childShape : ScopeLabel child label := by
      refine ⟨rfl, ?_, rfl⟩
      simp [SourceScope.branchTypes, form, label]
    have allShapes : List.Forall₂ ScopeLabel (parents ++ [parent]).reverse (parentLabel :: labels) := by
      simpa using List.Forall₂.cons oldParentShape parentShapes
    obtain ⟨saved, current⟩ := invariant.prefixes label (parentLabel :: labels) _ normalized childShape allShapes
    simp only [resolvedCode, patchCode] at saved current
    have bodyCode := current.finish target.val (child.front ++ child.results) (by omega) (by simp [resolved_code_length, position])
    obtain ⟨outerSaved, _, _, parentSaved⟩ := saved.pop
    have closed : StructuredDeadPrefix (jumpTables := jumpTables) emit types functions returns locals (resolvedCode before.function.code.val groups)
        (parentLabel :: labels) child.arguments [.LOOP bt child.source] child.entry target.val := by
      have bodyCode' : StructuredCode emit types functions returns locals (resolvedCode before.function.code.val groups) jumpTables
          (label :: parentLabel :: labels) (child.front ++ child.params) child.source
          (frame.start_pc.val + 1) target.val (child.front ++ child.results) := by
        simpa only [SourceScope.input, position, body] using bodyCode
      simpa [SourceScope.arguments, SourceScope.input, form, entry] using
        StructuredDeadPrefix.loop signature (resolved_code_loop_head _ groups _ head) bodyCode'
    have restored := parentSaved.resume_dead parentEntered childEntered closed
    refine ⟨?_, ?_⟩
    · rw [codeEq]
      exact outerSaved.advance_current (.LOOP bt child.source)
    · simpa only [codeEq, position, SourceScope.advance, SourceScope.input] using restored

end Itasca.Compiler

end

/-! ## StructuredUniversalCall -/

section

namespace Itasca.Compiler
open Aeneas.Std

theorem StructuredPrefix.emit_call {jumpTables : List Aeneas.Std.U32} {emit types functions returns locals code labels initial source start front params results}
    (prior : StructuredPrefix (jumpTables := jumpTables) emit types functions returns locals code labels initial source start code.length (front ++ params))
    (index base : U32)
    (signature : functions[index.val]? = some ⟨.mk_list params, .mk_list results⟩)
    (arguments : base.val = slots locals + slots front) :
    StructuredPrefix (jumpTables := jumpTables) emit types functions returns locals (code ++ [runtime.bytecode.Instr.Call index base]) labels initial
      (source ++ [.CALL (.mk_uN index.val)]) start (code ++ [runtime.bytecode.Instr.Call index base]).length (front ++ results) := by
  have fetched : (code ++ [runtime.bytecode.Instr.Call index base])[code.length]? = some (runtime.bytecode.Instr.Call index base) := by simp
  simpa only [List.length_append, List.length_singleton] using
    (prior.extend [runtime.bytecode.Instr.Call index base]).append (StructuredPrefix.call signature arguments fetched)

theorem Lowered.structured_resolved_call {jumpTables : List Aeneas.Std.U32} {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals labels groups initial source start front params results index base}
    (lowered : Lowered before after (.Call index base) (front ++ results))
    (invariant : StructuredResolvedInv (jumpTables := jumpTables) emit before types functions returns locals labels groups initial source start (front ++ params))
    (signature : functions[index.val]? = some ⟨.mk_list params, .mk_list results⟩)
    (arguments : base.val = slots locals + slots front) :
    StructuredResolvedInv (jumpTables := jumpTables) emit after types functions returns locals labels groups initial
      (source ++ [.CALL (.mk_uN index.val)]) start (front ++ results) := by
  refine ⟨lowered.2.2.1.trans invariant.localsEq, lowered.2.1, ?_, ?_⟩
  · intro group member site atSite
    have old := invariant.inside group member site atSite
    simp only [lowered.1, List.length_append, List.length_singleton]
    omega
  · have resolved := resolved_code_append_code before.function.code.val [runtime.bytecode.Instr.Call index base] groups invariant.inside
    have prior : StructuredPrefix (jumpTables := jumpTables) emit types functions returns locals (resolvedCode before.function.code.val groups)
        labels initial source start (resolvedCode before.function.code.val groups).length (front ++ params) := by
      simpa only [resolved_code_length] using invariant.code
    have advanced := prior.emit_call index base signature arguments
    simpa only [lowered.1, resolved, List.length_append, resolved_code_length] using advanced

/-- A direct-call callback advances every pending source/control prefix using
only the source signature and actual argument-base coordinate. -/
theorem Lowered.structured_universal_call {jumpTables : List Aeneas.Std.U32} {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current front params results index base}
    (lowered : Lowered before after (.Call index base) (front ++ results))
    (frames : after.frames = before.frames)
    (invariant : StructuredUniversalPrefix (jumpTables := jumpTables) emit before types functions returns locals parents current (front ++ params))
    (signature : functions[index.val]? = some ⟨.mk_list params, .mk_list results⟩)
    (arguments : base.val = slots locals + slots front) :
    StructuredUniversalPrefix (jumpTables := jumpTables) emit after types functions returns locals parents
      (current.advance (.CALL (.mk_uN index.val))) (front ++ results) := by
  have codeEq := lowered.1
  have lengthOrder : before.function.code.val.length ≤ after.function.code.val.length := by simp [codeEq]
  refine ⟨lowered.2.2.1.trans invariant.localsEq, lowered.2.1, ?_, ?_⟩
  · intro frame member
    rw [frames] at member
    simpa only [codeEq] using (invariant.sites frame member).extend [runtime.bytecode.Instr.Call index base]
  · intro label labels groups plans shape parentShapes
    have oldPlans : FramePlans before.function.code.val.length locals before.frames.val (label :: labels) groups := by
      rw [← frames]
      exact plans.before lengthOrder
    have oldShape : ScopeLabel current label :=
      ⟨shape.front, by simpa [SourceScope.advance, SourceScope.branchTypes] using shape.branchTypes, shape.results⟩
    have old := invariant.resolved oldPlans oldShape parentShapes
    have next := lowered.structured_resolved_call old signature arguments
    have saved := (invariant.prefixes label labels groups oldPlans oldShape parentShapes).1
    have resolved := resolved_code_append_code before.function.code.val [runtime.bytecode.Instr.Call index base] groups old.inside
    refine ⟨?_, next.code⟩
    simpa only [codeEq, resolved] using
      (saved.extend [runtime.bytecode.Instr.Call index base]).advance_current (.CALL (.mk_uN index.val))

end Itasca.Compiler

end

/-! ## StructuredUniversalEmpty -/

section

namespace Itasca.Compiler
open Aeneas.Std

/-- Instructions with no emitted bytecode advance every possible structured
completion while retaining all pending fixups and parent prefixes. -/
theorem LoweredEmpty.structured_universal_advance {jumpTables : List Aeneas.Std.U32} {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current stack instruction output}
    (lowered : LoweredEmpty before after output) (frames : after.frames = before.frames)
    (invariant : StructuredUniversalPrefix (jumpTables := jumpTables) emit before types functions returns locals parents current stack)
    (head : emit stack instruction [] output)
    (notTable : ∀ depths fallback, instruction ≠ .BR_TABLE depths fallback) :
    StructuredUniversalPrefix (jumpTables := jumpTables) emit after types functions returns locals parents (current.advance instruction) output := by
  have codeEq := lowered.1
  refine ⟨lowered.2.2.1.trans invariant.localsEq, lowered.2.1, ?_, ?_⟩
  · intro frame member
    simpa only [codeEq] using invariant.sites frame (by simpa only [frames] using member)
  · intro label labels groups plans shape parentShapes
    have oldPlans : FramePlans before.function.code.val.length locals before.frames.val (label :: labels) groups := by
      simpa only [codeEq, frames] using plans
    have oldShape : ScopeLabel current label :=
      ⟨shape.front, by simpa [SourceScope.advance, SourceScope.branchTypes] using shape.branchTypes, shape.results⟩
    obtain ⟨saved, prefixCode⟩ := invariant.prefixes label labels groups oldPlans oldShape parentShapes
    have fragment : Segment (resolvedCode before.function.code.val groups) before.function.code.val.length []
        before.function.code.val.length := ⟨resolvedCode before.function.code.val groups, [], by simp, by simp [resolved_code_length], by simp⟩
    have advanced := prefixCode.append (StructuredPrefix.linear head notTable fragment)
    exact ⟨by simpa only [codeEq] using saved.advance_current instruction,
      by simpa only [codeEq, SourceScope.advance, SourceScope.input] using advanced⟩

end Itasca.Compiler

end

end

/-! ## CloseIf -/

section

open Itasca.Representation

/-!
# Closing an IF without ELSE

The shared exit resolves the guard at END. The omitted arm supplies the identity behavior required by the source block signature and completes the structured prefix.
-/

namespace Itasca.Compiler
open Aeneas.Std

/-- END without ELSE resolves the guard at the shared exit. The missing arm
is the identity required by the source block signature. -/
theorem StructuredCompletedPrefix.close_if {jumpTables : List Aeneas.Std.U32} {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents parent child normal}
    (invariant : StructuredCompletedPrefix (jumpTables := jumpTables) emit before types functions returns locals (parents ++ [parent]) child normal)
    (completed : StructuredUniversalElse (jumpTables := jumpTables) emit before types functions returns locals (parents ++ [parent]) child)
    (frame : runtime.compiler.Frame) (target : U32) (bt : blocktype)
    (guard : Usize) (condition old : U32)
    (frames : before.frames.val = after.frames.val ++ [frame])
    (kind : frame.kind = .Then) (guardEq : frame.if_pc = some guard)
    (guardCode : before.function.code.val[guard.val]? = some (.JumpIfZero condition old))
    (distinct : ∀ other ∈ after.frames.val, other.if_pc ≠ some guard)
    (height : frame.height.val = slots locals + slots child.front)
    (width : frame.results.val = slots child.results)
    (position : target.val = before.function.code.val.length)
    (codeEq : after.function.code.val = patchCode
      (before.function.code.val.set guard.val (.JumpIfZero condition target)) frame.fixups.val target)
    (localsEq : compilerLocals after = locals)
    (layout : CompilerLayout after (child.front ++ child.results))
    (form : child.form = .then_ bt condition) (entry : child.entry = guard.val)
    (bodyStart : child.bodyPc = child.entry + 1)
    (conditionSlot : condition.val = slots locals + slots child.input)
    (sameTypes : child.params = child.results)
    (parentEntered : parent.entered = true) (childEntered : child.entered = true)
    (signature : BlockSignature types bt child.params child.results) :
    StructuredUniversalPrefix (jumpTables := jumpTables) emit after types functions returns locals parents
      (parent.advance (.IFELSE bt child.source [])) (child.front ++ child.results) ∧
    StructuredUniversalElse (jumpTables := jumpTables) emit after types functions returns locals parents
      (parent.advance (.IFELSE bt child.source [])) := by
  have lengthEq : after.function.code.val.length = before.function.code.val.length := by
    simp [codeEq, patch_code_length]
  have advance : ∀ parentLabel labels groups,
      FramePlans after.function.code.val.length locals after.frames.val (parentLabel :: labels) groups →
      ScopeLabel (parent.advance (.IFELSE bt child.source [])) parentLabel →
      List.Forall₂ ScopeLabel parents.reverse labels →
      StructuredParentPrefixes (jumpTables := jumpTables) emit types functions returns locals (resolvedCode after.function.code.val groups)
        parents labels (parent.advance (.IFELSE bt child.source [])) ∧
      StructuredPrefix (jumpTables := jumpTables) emit types functions returns locals (resolvedCode after.function.code.val groups)
        (parentLabel :: labels) parent.input (parent.source ++ [.IFELSE bt child.source []])
        parent.bodyPc after.function.code.val.length (child.front ++ child.results) ∧
      StructuredElseFrames (jumpTables := jumpTables) emit types functions returns locals (resolvedCode after.function.code.val groups)
        (parent.advance (.IFELSE bt child.source []) :: parents.reverse) (parentLabel :: labels) := by
    intro parentLabel labels groups plans shape parentShapes
    have oldParentShape : ScopeLabel parent parentLabel :=
      ⟨shape.front, by simpa [SourceScope.advance, SourceScope.branchTypes] using shape.branchTypes, shape.results⟩
    let label : LabelTarget := ⟨child.front, child.results, child.results, target, target.val, [], [], normal, frame.end_reachable⟩
    have future : FrameFuture before.function.code.val.length locals frame label target := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro _; exact height
      · intro _; exact width
      · intro _; simpa [kind, label] using width
      · exact Nat.le_of_eq position.symm
      · intro _; exact Nat.le_of_eq position.symm
      · simp [kind]
      · simp [kind]
      · exact fun h => h
      · intros; rfl
      · intro _; exact Nat.le_of_eq position.symm
    have outer : FramePlans before.function.code.val.length locals after.frames.val (parentLabel :: labels) groups := by
      simpa only [lengthEq] using plans
    have allPlans := FramePlans.push outer frame label target future
    rw [← frames] at allPlans
    have normalized : FramePlans before.function.code.val.length locals before.frames.val
        (label :: parentLabel :: labels) (⟨[guard], target⟩ :: ⟨frame.fixups.val, target⟩ :: groups) := by
      simpa [frameGroups, guardEq, label] using allPlans
    have childShape : ScopeLabel child label := by
      refine ⟨rfl, ?_, rfl⟩
      simp [SourceScope.branchTypes, form, label]
    have allShapes : List.Forall₂ ScopeLabel (parents ++ [parent]).reverse (parentLabel :: labels) := by
      simpa using List.Forall₂.cons oldParentShape parentShapes
    obtain ⟨saved, noCode⟩ := invariant.prefixes label (parentLabel :: labels) _ normalized childShape allShapes position rfl
    have allArms := completed label (parentLabel :: labels) _ normalized childShape allShapes
    have guardFound : (resolvedCode before.function.code.val
        (⟨[guard], target⟩ :: ⟨frame.fixups.val, target⟩ :: groups))[child.entry]? =
        some (.JumpIfZero condition target) := by
      rw [entry]
      have current := invariant.sites frame (by simp [frames])
      have away := outer.away_guard
        (fun f member => invariant.sites f (by rw [frames]; exact List.mem_append_left _ member))
        guardCode distinct
      exact resolved_code_guard _ [] _ guard condition old target guardCode (by
        intro group member site atSite
        simp only [List.nil_append, List.mem_cons] at member
        rcases member with rfl | remaining
        · exact current.branches.not_guard guardCode site atSite
        · exact away group remaining site atSite)
    obtain ⟨outerSaved, _, _, parentSaved⟩ := saved.pop
    have closed : StructuredPrefix (jumpTables := jumpTables) emit types functions returns locals
        (resolvedCode before.function.code.val (⟨[guard], target⟩ :: ⟨frame.fixups.val, target⟩ :: groups))
        (parentLabel :: labels) child.arguments [.IFELSE bt child.source []] child.entry target.val
        (child.front ++ child.results) := by
      have body : StructuredCode emit types functions returns locals
          (resolvedCode before.function.code.val (⟨[guard], target⟩ :: ⟨frame.fixups.val, target⟩ :: groups)) jumpTables
          (⟨child.front, child.params, child.params, target, target.val, [], [], normal, frame.end_reachable⟩ :: parentLabel :: labels)
          child.input child.source (child.entry + 1) target.val (child.front ++ child.params) := by
        simpa only [label, bodyStart, position, sameTypes] using noCode
      have sig : BlockSignature types bt child.params child.params := by simpa only [sameTypes] using signature
      simpa [SourceScope.arguments, SourceScope.input, form, sameTypes] using
        StructuredPrefix.if_end sig conditionSlot guardFound body
    have restored := parentSaved.resume parentEntered childEntered closed
    have resolve : resolvedCode after.function.code.val groups =
        resolvedCode before.function.code.val (⟨[guard], target⟩ :: ⟨frame.fixups.val, target⟩ :: groups) := by
      simp only [codeEq, resolvedCode, patchCode, guardCode, retarget]
    refine ⟨?_, ?_, ?_⟩
    · rw [resolve]
      exact outerSaved.advance_current (.IFELSE bt child.source [])
    · simpa only [resolve, lengthEq, position] using restored
    · rw [resolve]
      have outerArms : StructuredElseFrames (jumpTables := jumpTables) emit types functions returns locals
          (resolvedCode before.function.code.val (⟨[guard], target⟩ :: ⟨frame.fixups.val, target⟩ :: groups))
          (parent :: parents.reverse) (parentLabel :: labels) := by
        simpa using allArms.outer
      exact outerArms.advance (.IFELSE bt child.source [])
  refine ⟨⟨localsEq, layout, ?_, ?_⟩, ?_⟩
  · intro f member
    have original := invariant.sites f (by rw [frames]; exact List.mem_append_left _ member)
    simpa only [codeEq] using (original.set_guard guard condition old target guardCode).patch frame.fixups.val target
  · intro label labels groups plans shape parentShapes
    have outcome := advance label labels groups plans shape parentShapes
    exact ⟨outcome.1, outcome.2.1⟩
  · intro label labels groups plans shape parentShapes
    exact (advance label labels groups plans shape parentShapes).2.2

end Itasca.Compiler

end

end

/-! ## Function -/

section

open Itasca.Representation

/-!
# Function

Structured function prefixes preserve label widening and the control relation needed at function completion.
-/

/-! ## StructuredLabelWiden -/

section

namespace Itasca.Compiler
open Aeneas.Std
theorem BranchTableEntry.widen_labels {locals labels stack code depth entry next}
    (evidence : BranchTableEntry locals labels stack code depth entry next)
    {other} (shape : LabelsWiden labels other) :
    BranchTableEntry locals other stack code depth entry next := by
  obtain ⟨label, dst, src, count, fragmentEnd, lookup, live, layout, fragment, remaining, scope⟩ := evidence
  obtain ⟨otherLabel, otherAt, same⟩ := LabelsWiden.lookup shape lookup
  refine ⟨otherLabel, dst, src, count, fragmentEnd, otherAt, same.branchLive live, ?_, ?_, remaining, scope⟩
  · simpa only [BranchLayout, ← same.front, ← same.branchTypes] using layout
  · simpa only [← same.target] using fragment

theorem BranchTableLayout.widen_labels {tables locals labels stack code depths fallback pc next selector start len}
    (evidence : BranchTableLayout tables locals labels stack code depths fallback pc next selector start len)
    {other} (shape : LabelsWiden labels other) :
    BranchTableLayout tables locals other stack code depths fallback pc next selector start len := by
  refine ⟨evidence.selectorSlot, evidence.length, evidence.instruction, evidence.arithmetic, ?_⟩
  intro index depth found
  obtain ⟨entry, lookup, arm⟩ := evidence.entries index depth found
  exact ⟨entry, lookup, arm.widen_labels shape⟩

theorem StructuredCode.widen_labels {jumpTables : List U32} {emit types functions returns locals code labels stack source pc next after}
    (relation : StructuredCode emit types functions returns locals code jumpTables labels stack source pc next after)
    {other} (shape : LabelsWiden labels other) :
    StructuredCode emit types functions returns locals code jumpTables other stack source pc next after := by
  induction relation generalizing other with
  | nil labels stack pc bound live => exact .nil other stack pc bound (shape.normal live)
  | linear head ordinary fragment rest ih => exact .linear head ordinary fragment (ih shape)
  | skip forward instruction rest ih => exact .skip forward instruction (ih shape)
  | block signature body rest target bounds bodyIH restIH targetIH =>
    exact .block signature (bodyIH (.cons (LabelWiden.refl _) shape))
      (fun live => restIH live shape) (fun live => targetIH live shape) bounds
  | loop signature head body rest bounds bodyIH restIH =>
    exact .loop signature head (bodyIH (.cons (LabelWiden.refl _) shape))
      (fun live => restIH live shape) bounds
  | ifElse signature condition guard yes skip no rest bounds yesIH noIH restIH =>
    exact .ifElse signature condition guard (yesIH (.cons (LabelWiden.refl _) shape)) skip
      (noIH (.cons (LabelWiden.refl _) shape)) (fun live => restIH live shape) bounds
  | @branch jumpTables labels stack after depth label dst src count pc fragmentEnd next final lookup live layout fragment remaining scope =>
    obtain ⟨otherLabel, otherAt, same⟩ := LabelsWiden.lookup shape lookup
    apply StructuredCode.branch (dst := dst) (src := src) (count := count) otherAt (same.branchLive live) ?_ ?_ remaining scope
    · simpa only [BranchLayout, ← same.front, ← same.branchTypes] using layout
    · simpa only [← same.target] using fragment
  | @branchIf jumpTables labels stack after depth label dst src count cond resume pc next final lookup live layout condition fragment rest ih =>
    obtain ⟨otherLabel, otherAt, same⟩ := LabelsWiden.lookup shape lookup
    apply StructuredCode.branchIf (dst := dst) (src := src) (count := count) otherAt (same.branchLive live) ?_ condition ?_ (ih shape)
    · simpa only [BranchLayout, ← same.front, ← same.branchTypes] using layout
    · simpa only [← same.target] using fragment
  | branchTable gate table bounds => exact .branchTable gate (table.widen_labels shape) bounds
  | call signature arguments instruction rest ih => exact .call signature arguments instruction (ih shape)
  | unreachable instruction remaining scope => exact .unreachable instruction remaining scope
  | return_ source size instruction remaining scope => exact .return_ source size instruction remaining scope

end Itasca.Compiler

end

/-! ## StructuredFunctionBodyClose -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- Appending the literal epilogue reconciles the root's separate normal and
branch flags with the retained function label. A zero-result dead body may
safely acquire a live empty epilogue, without changing its body evidence. -/
theorem structured_body_code_epilogue {jumpTables : List Aeneas.Std.U32} {emit types functions returns locals body code target normal branch}
    (relation : StructuredCode emit types functions returns locals code jumpTables
      [⟨[], returns, returns, target, target.val, [], [], normal, branch⟩]
      [] body 0 target.val returns)
    (position : target.val = code.length)
    (compiled : runtime.bytecode.CompiledFunction) (src count : U32)
    (width : count.val = slots returns)
    (emitted : compiled.code.val = code ++ [.Return src (if normal || branch then count else 0#u32)]) :
    StructuredCode emit types functions returns locals compiled.code.val jumpTables
      [functionRootLabel returns compiled target] [] body 0 target.val returns ∧
      compiled.code.val[target.val]? = some (.Return src (if normal || branch then count else 0#u32)) ∧
      compiled.code.val.length = target.val + 1 := by
  have found : compiled.code.val[target.val]? = some (.Return src (if normal || branch then count else 0#u32)) := by
    simp [emitted, position]
  have normalLive : normal = true → (functionRootLabel returns compiled target).normalLive = true := by
    intro live
    simp [functionRootLabel, found, live, width]
  have branchLive : branch = true → (functionRootLabel returns compiled target).branchLive = true := by
    intro live
    simp [functionRootLabel, found, live, width]
  refine ⟨?_, found, by simp [emitted, position]⟩
  have extended := relation.extend [.Return src (if normal || branch then count else 0#u32)]
  rw [← emitted] at extended
  apply extended.widen_labels
  exact .cons ⟨rfl, rfl, rfl, rfl, rfl, normalLive, branchLive⟩ .nil

/-- The actual final END constructs the retained body/epilogue relation from
the completed root prefix, after resolving every root branch. -/
@[step] theorem structured_close_function_body {jumpTables : List Aeneas.Std.U32} {emit : List valtype → instr → List Bytecode → List valtype → Prop} {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (frame : runtime.compiler.Frame)
    (rest : alloc.vec.Vec runtime.compiler.Frame) (target : U32)
    (frames : compiler.frames.val = rest.val ++ [frame])
    (kind : frame.kind = .Body) (noIf : frame.if_pc = none)
    (position : target.val = compiler.function.code.val.length)
    (branches : BranchSites compiler.function.code.val frame.fixups.val)
    (mapFits : frame.map.val < compiler.function.controls.val.length)
    (coordinateFits : compiler.function.body_start.val + state.pos.val ≤ Usize.max)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (emitCoordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max)
    (types functions : List functype) (returns locals : List valtype) (body : List instr)
    (width : frame.results.val = slots returns)
    (bodyCode : StructuredCode emit types functions returns locals
      (patchCode compiler.function.code.val frame.fixups.val target) jumpTables
      [⟨[], returns, returns, target, target.val, [], [], compiler.reachable, frame.end_reachable⟩]
      [] body 0 target.val returns) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops compiler state .Block .Empty ⦃ out =>
      out.1 = .Ok () → out.2.frames = rest ∧
        StructuredCode emit types functions returns locals out.2.function.code.val jumpTables
          [functionRootLabel returns out.2.function target] [] body 0 target.val returns ∧
        (∃ count, out.2.function.code.val[target.val]? = some (.Return frame.height count)) ∧
        out.2.function.code.val.length = target.val + 1 ⦄ := by
  apply WP.spec_mono (close_function_effect ops law compiler state frame rest target frames kind noIf
    position branches mapFits coordinateFits codeFits sourceFits emitCoordinateFits)
  intro out effect accepted
  obtain ⟨popped, reachable, code, control⟩ := effect accepted
  have code' : out.2.function.code.val = patchCode compiler.function.code.val frame.fixups.val target ++
      [.Return frame.height (if compiler.reachable || frame.end_reachable then frame.results else 0#u32)] := by
    simpa [scopeExitLive, kind] using code
  obtain ⟨body', return', end'⟩ := structured_body_code_epilogue bodyCode
    (by simpa only [patch_code_length] using position) out.2.function frame.height frame.results width code'
  exact ⟨popped, body', ⟨_, return'⟩, end'⟩

end Itasca.Compiler

end

/-! ## StructuredResolvedBranchPrefix -/

section

namespace Itasca.Compiler
open Aeneas.Std
theorem StructuredPrefix.resolved_branch {jumpTables : List Aeneas.Std.U32} {emit types functions returns locals labels initial source start stack}
    {code : List Bytecode} {before after : List FixupTarget} {group : FixupTarget}
    {depth : Nat} {label : LabelTarget} {dst src count old : U32} {site : Usize}
    (prior : StructuredPrefix (jumpTables := jumpTables) emit types functions returns locals (resolvedCode code (before ++ group :: after))
      labels initial source start code.length stack)
    (inside : FixupsInside (before ++ group :: after) code.length)
    (position : site.val = code.length + (if count = 0#u32 ∨ src = dst then 0 else 1))
    (lookup : labels[depth]? = some label) (live : label.branchLive = true)
    (target : label.target = group.target) (layout : BranchLayout locals stack label dst src count) :
    StructuredDeadPrefix (jumpTables := jumpTables) emit types functions returns locals
      (resolvedCode (code ++ branchInstructions dst src count old)
        (before ++ {group with sites := group.sites ++ [site]} :: after))
      labels initial (source ++ [.BR (.mk_uN depth)]) start
      (code.length + (branchInstructions dst src count group.target).length) := by
  rw [resolved_code_new_br code before after group dst src count old site position inside]
  apply (prior.extend (branchInstructions dst src count group.target)).terminal
  apply StructuredDeadPrefix.branch lookup live layout
  rw [target]
  exact ⟨resolvedCode code (before ++ group :: after), [], by simp,
    resolved_code_length _ _, rfl⟩

end Itasca.Compiler

end

/-! ## StructuredResolvedConditionalPrefix -/

section

namespace Itasca.Compiler
open Aeneas.Std
theorem StructuredPrefix.resolved_branch_if {jumpTables : List Aeneas.Std.U32} {emit types functions returns locals labels initial source start stack}
    {code : List Bytecode} {before after : List FixupTarget} {group : FixupTarget}
    {depth : Nat} {label : LabelTarget} {dst src count old condition resume : U32} {site : Usize}
    (prior : StructuredPrefix (jumpTables := jumpTables) emit types functions returns locals (resolvedCode code (before ++ group :: after))
      labels initial source start code.length (stack ++ [.I32]))
    (inside : FixupsInside (before ++ group :: after) code.length)
    (position : site.val = code.length + (if count = 0#u32 ∨ src = dst then 0 else 2))
    (resumePosition : resume.val = code.length + (if count = 0#u32 ∨ src = dst then 1 else 3))
    (lookup : labels[depth]? = some label) (live : label.branchLive = true)
    (target : label.target = group.target) (layout : BranchLayout locals stack label dst src count)
    (conditionSlot : condition.val = slots locals + slots stack) :
    StructuredPrefix (jumpTables := jumpTables) emit types functions returns locals
      (resolvedCode (code ++ branchIfInstructions dst src count old condition resume)
        (before ++ {group with sites := group.sites ++ [site]} :: after))
      labels initial (source ++ [.BR_IF (.mk_uN depth)]) start resume.val stack := by
  rw [resolved_code_new_br_if code before after group dst src count old condition resume site position inside]
  apply (prior.extend (branchIfInstructions dst src count group.target condition resume)).append
  apply StructuredPrefix.branch_if lookup live layout conditionSlot
  rw [target]
  refine ⟨resolvedCode code (before ++ group :: after), [], by simp, resolved_code_length _ _, ?_⟩
  by_cases empty : count = 0#u32 ∨ src = dst
  · simpa [branchIfInstructions, empty] using resumePosition
  · simpa [branchIfInstructions, empty] using resumePosition

end Itasca.Compiler

end

/-! ## StructuredUniversalBranch -/

section

namespace Itasca.Compiler
open Aeneas.Std
theorem StructuredUniversalPrefix.branch_forward {jumpTables : List Aeneas.Std.U32} {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current stack}
    (invariant : StructuredUniversalPrefix (jumpTables := jumpTables) emit before types functions returns locals parents current stack)
    (frame : runtime.compiler.Frame) (index depth : Nat) (scope : SourceScope)
    (dst src count old : U32) (site : Usize) (fixups : alloc.vec.Vec Usize)
    (found : before.frames.val[index]? = some frame)
    (position : index + depth + 1 = before.frames.val.length)
    (scopeAt : (current :: parents.reverse)[depth]? = some scope)
    (discarded : List valtype) (stackEq : stack = scope.front ++ discarded ++ scope.branchTypes)
    (destination : dst.val = slots locals + slots scope.front)
    (source : src.val = slots locals + slots (scope.front ++ discarded))
    (width : count.val = slots scope.branchTypes)
    (sitePosition : site.val = before.function.code.val.length +
      (if count = 0#u32 ∨ src = dst then 0 else 1))
    (appended : fixups.val = frame.fixups.val ++ [site])
    (codeEq : after.function.code.val = before.function.code.val ++ branchInstructions dst src count old)
    (framesEq : after.frames.val = before.frames.val.set index {frame with end_reachable := true, fixups})
    (localsEq : compilerLocals after = locals) :
    StructuredUniversalTerminal (jumpTables := jumpTables) emit after types functions returns locals parents (current.advance (.BR (.mk_uN depth))) := by
  have lengthOrder : before.function.code.val.length ≤ after.function.code.val.length := by simp [codeEq]
  refine ⟨localsEq, ?_, ?_⟩
  · intro f member
    rw [framesEq] at member
    rcases List.mem_or_eq_of_mem_set member with previous | rfl
    · simpa only [codeEq] using (invariant.sites f previous).extend (branchInstructions dst src count old)
    · have frameOk := invariant.sites frame (List.mem_of_getElem? found)
      simpa only [codeEq] using frameOk.add_branch dst src count old site fixups appended sitePosition
  · intro top labels groups plans shape parentShapes
    obtain ⟨label, earlier, suffix, labelAt, live, priorPlans, grouped⟩ :=
      plans.before_mark fixups framesEq found position
    have oldPlans := priorPlans.before lengthOrder
    have oldShape : ScopeLabel current top :=
      ⟨shape.front, by simpa [SourceScope.advance, SourceScope.branchTypes] using shape.branchTypes, shape.results⟩
    have allShapes : List.Forall₂ ScopeLabel (current :: parents.reverse) (top :: labels) :=
      .cons oldShape parentShapes
    have selected := scope_labels_lookup allShapes scopeAt labelAt
    have layout : BranchLayout locals stack label dst src count := by
      refine ⟨discarded, ?_, ?_, ?_, ?_⟩
      · simpa only [selected.front, selected.branchTypes] using stackEq
      · simpa only [selected.front] using destination
      · simpa only [selected.front] using source
      · simpa only [selected.branchTypes] using width
    have prior := invariant.resolved oldPlans oldShape parentShapes
    have saved := (invariant.prefixes top labels _ oldPlans oldShape parentShapes).1
    have resolved := resolved_code_new_br before.function.code.val earlier suffix
      ⟨frame.fixups.val, label.target⟩ dst src count old site sitePosition prior.inside
    have terminal := prior.code.resolved_branch (old := old) prior.inside sitePosition labelAt live rfl layout
    rw [grouped, appended]
    refine ⟨?_, ?_⟩
    · rw [codeEq, resolved]
      exact (saved.extend (branchInstructions dst src count label.target)).advance_current (.BR (.mk_uN depth))
    · by_cases elided : count = 0#u32 ∨ src = dst
      all_goals simpa [codeEq, SourceScope.advance, SourceScope.input, branchInstructions, elided] using terminal

end Itasca.Compiler

end

/-! ## StructuredUniversalConditional -/

section

namespace Itasca.Compiler
open Aeneas.Std
theorem StructuredUniversalPrefix.branch_if_forward {jumpTables : List Aeneas.Std.U32} {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current stack}
    (invariant : StructuredUniversalPrefix (jumpTables := jumpTables) emit before types functions returns locals parents current (stack ++ [.I32]))
    (frame : runtime.compiler.Frame) (index depth : Nat) (scope : SourceScope)
    (dst src count old condition resume : U32) (site : Usize) (fixups : alloc.vec.Vec Usize)
    (found : before.frames.val[index]? = some frame)
    (position : index + depth + 1 = before.frames.val.length)
    (scopeAt : (current :: parents.reverse)[depth]? = some scope)
    (discarded : List valtype) (stackEq : stack = scope.front ++ discarded ++ scope.branchTypes)
    (destination : dst.val = slots locals + slots scope.front)
    (source : src.val = slots locals + slots (scope.front ++ discarded))
    (width : count.val = slots scope.branchTypes)
    (sitePosition : site.val = before.function.code.val.length +
      (if count = 0#u32 ∨ src = dst then 0 else 2))
    (appended : fixups.val = frame.fixups.val ++ [site])
    (codeEq : after.function.code.val = before.function.code.val ++ branchIfInstructions dst src count old condition resume)
    (framesEq : after.frames.val = before.frames.val.set index {frame with end_reachable := true, fixups})
    (localsEq : compilerLocals after = locals) (afterLayout : CompilerLayout after stack)
    (conditionSlot : condition.val = slots locals + slots stack)
    (resumePosition : resume.val = before.function.code.val.length +
      (if count = 0#u32 ∨ src = dst then 1 else 3)) :
    StructuredUniversalPrefix (jumpTables := jumpTables) emit after types functions returns locals parents (current.advance (.BR_IF (.mk_uN depth))) stack := by
  have lengthOrder : before.function.code.val.length ≤ after.function.code.val.length := by simp [codeEq]
  refine ⟨localsEq, afterLayout, ?_, ?_⟩
  · intro f member
    rw [framesEq] at member
    rcases List.mem_or_eq_of_mem_set member with previous | rfl
    · simpa only [codeEq] using (invariant.sites f previous).extend (branchIfInstructions dst src count old condition resume)
    · have frameOk := invariant.sites frame (List.mem_of_getElem? found)
      simpa only [codeEq] using frameOk.add_conditional dst src count old condition resume site fixups appended sitePosition
  · intro top labels groups plans shape parentShapes
    obtain ⟨label, earlier, suffix, labelAt, live, priorPlans, grouped⟩ :=
      plans.before_mark fixups framesEq found position
    have oldPlans := priorPlans.before lengthOrder
    have oldShape : ScopeLabel current top :=
      ⟨shape.front, by simpa [SourceScope.advance, SourceScope.branchTypes] using shape.branchTypes, shape.results⟩
    have allShapes : List.Forall₂ ScopeLabel (current :: parents.reverse) (top :: labels) :=
      .cons oldShape parentShapes
    have selected := scope_labels_lookup allShapes scopeAt labelAt
    have layout : BranchLayout locals stack label dst src count := by
      refine ⟨discarded, ?_, ?_, ?_, ?_⟩
      · simpa only [selected.front, selected.branchTypes] using stackEq
      · simpa only [selected.front] using destination
      · simpa only [selected.front] using source
      · simpa only [selected.branchTypes] using width
    have prior := invariant.resolved oldPlans oldShape parentShapes
    have saved := (invariant.prefixes top labels _ oldPlans oldShape parentShapes).1
    have resolved := resolved_code_new_br_if before.function.code.val earlier suffix
      ⟨frame.fixups.val, label.target⟩ dst src count old condition resume site sitePosition prior.inside
    have terminal := prior.code.resolved_branch_if (old := old) prior.inside sitePosition resumePosition labelAt live rfl layout conditionSlot
    rw [grouped, appended]
    refine ⟨?_, ?_⟩
    · rw [codeEq, resolved]
      exact (saved.extend (branchIfInstructions dst src count label.target condition resume)).advance_current (.BR_IF (.mk_uN depth))
    · by_cases elided : count = 0#u32 ∨ src = dst
      all_goals simpa [codeEq, SourceScope.advance, SourceScope.input, branchIfInstructions, elided, resumePosition] using terminal

end Itasca.Compiler

end

/-! ## StructuredElseBranches -/

section

namespace Itasca.Compiler
open Aeneas.Std

/-- A forward branch strengthens only its selected future exit and appends
new resolved instructions; completed ELSE arms remain an exact prefix. -/
theorem StructuredUniversalElse.branch_forward {jumpTables : List Aeneas.Std.U32} {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current}
    (invariant : StructuredUniversalElse (jumpTables := jumpTables) emit before types functions returns locals parents current)
    (sites : ∀ frame ∈ before.frames.val, FrameSites before.function.code.val frame)
    (frame : runtime.compiler.Frame) (index depth : Nat)
    (dst src count old : U32) (site : Usize) (fixups : alloc.vec.Vec Usize)
    (found : before.frames.val[index]? = some frame)
    (position : index + depth + 1 = before.frames.val.length)
    (sitePosition : site.val = before.function.code.val.length +
      (if count = 0#u32 ∨ src = dst then 0 else 1))
    (appended : fixups.val = frame.fixups.val ++ [site])
    (codeEq : after.function.code.val = before.function.code.val ++ branchInstructions dst src count old)
    (framesEq : after.frames.val = before.frames.val.set index {frame with end_reachable := true, fixups}) :
    StructuredUniversalElse (jumpTables := jumpTables) emit after types functions returns locals parents (current.advance (.BR (.mk_uN depth))) := by
  intro top labels groups plans shape parentShapes
  have order : before.function.code.val.length ≤ after.function.code.val.length := by simp [codeEq]
  obtain ⟨label, earlier, suffix, labelAt, live, priorPlans, grouped⟩ :=
    plans.before_mark fixups framesEq found position
  have oldPlans := priorPlans.before order
  have oldShape : ScopeLabel current top :=
    ⟨shape.front, by simpa [SourceScope.advance, SourceScope.branchTypes] using shape.branchTypes, shape.results⟩
  have prior := invariant top labels _ oldPlans oldShape parentShapes
  have resolved := resolved_code_new_br before.function.code.val earlier suffix
    ⟨frame.fixups.val, label.target⟩ dst src count old site sitePosition (oldPlans.inside sites)
  rw [grouped, appended, codeEq, resolved]
  exact (prior.extend (branchInstructions dst src count label.target)).advance (.BR (.mk_uN depth))

/-- Conditional forward branches preserve completed-arm certificates for the
same reason, including the emitted transfer/guard pair when needed. -/
theorem StructuredUniversalElse.branch_if_forward {jumpTables : List Aeneas.Std.U32} {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current}
    (invariant : StructuredUniversalElse (jumpTables := jumpTables) emit before types functions returns locals parents current)
    (sites : ∀ frame ∈ before.frames.val, FrameSites before.function.code.val frame)
    (frame : runtime.compiler.Frame) (index depth : Nat)
    (dst src count old condition resume : U32) (site : Usize) (fixups : alloc.vec.Vec Usize)
    (found : before.frames.val[index]? = some frame)
    (position : index + depth + 1 = before.frames.val.length)
    (sitePosition : site.val = before.function.code.val.length +
      (if count = 0#u32 ∨ src = dst then 0 else 2))
    (appended : fixups.val = frame.fixups.val ++ [site])
    (codeEq : after.function.code.val = before.function.code.val ++ branchIfInstructions dst src count old condition resume)
    (framesEq : after.frames.val = before.frames.val.set index {frame with end_reachable := true, fixups}) :
    StructuredUniversalElse (jumpTables := jumpTables) emit after types functions returns locals parents (current.advance (.BR_IF (.mk_uN depth))) := by
  intro top labels groups plans shape parentShapes
  have order : before.function.code.val.length ≤ after.function.code.val.length := by simp [codeEq]
  obtain ⟨label, earlier, suffix, labelAt, live, priorPlans, grouped⟩ :=
    plans.before_mark fixups framesEq found position
  have oldPlans := priorPlans.before order
  have oldShape : ScopeLabel current top :=
    ⟨shape.front, by simpa [SourceScope.advance, SourceScope.branchTypes] using shape.branchTypes, shape.results⟩
  have prior := invariant top labels _ oldPlans oldShape parentShapes
  have resolved := resolved_code_new_br_if before.function.code.val earlier suffix
    ⟨frame.fixups.val, label.target⟩ dst src count old condition resume site sitePosition (oldPlans.inside sites)
  rw [grouped, appended, codeEq, resolved]
  exact (prior.extend (branchIfInstructions dst src count label.target condition resume)).advance (.BR_IF (.mk_uN depth))

end Itasca.Compiler

end

/-! ## StructuredUniversalLoopBranch -/

section

namespace Itasca.Compiler
open Aeneas.Std

/-- A loop branch has a known literal target and adds no forward fixup. The
static plan derives its liveness and target from the physical LOOP frame. -/
theorem StructuredUniversalPrefix.branch_loop {jumpTables : List Aeneas.Std.U32} {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current stack}
    (invariant : StructuredUniversalPrefix (jumpTables := jumpTables) emit before types functions returns locals parents current stack)
    (frame : runtime.compiler.Frame) (index depth : Nat) (scope : SourceScope)
    (dst src count : U32)
    (found : before.frames.val[index]? = some frame)
    (position : index + depth + 1 = before.frames.val.length)
    (isLoop : frame.kind = .Loop)
    (scopeAt : (current :: parents.reverse)[depth]? = some scope)
    (discarded : List valtype) (stackEq : stack = scope.front ++ discarded ++ scope.branchTypes)
    (destination : dst.val = slots locals + slots scope.front)
    (source : src.val = slots locals + slots (scope.front ++ discarded))
    (width : count.val = slots scope.branchTypes)
    (codeEq : after.function.code.val = before.function.code.val ++ branchInstructions dst src count frame.start_pc)
    (framesEq : after.frames = before.frames) (localsEq : compilerLocals after = locals) :
    StructuredUniversalTerminal (jumpTables := jumpTables) emit after types functions returns locals parents (current.advance (.BR (.mk_uN depth))) := by
  have lengthOrder : before.function.code.val.length ≤ after.function.code.val.length := by simp [codeEq]
  refine ⟨localsEq, ?_, ?_⟩
  · intro f member
    rw [framesEq] at member
    simpa only [codeEq] using (invariant.sites f member).extend (branchInstructions dst src count frame.start_pc)
  · intro top labels groups plans shape parentShapes
    have oldPlans : FramePlans before.function.code.val.length locals before.frames.val (top :: labels) groups := by
      rw [← framesEq]
      exact plans.before lengthOrder
    obtain ⟨label, guard, labelAt, future⟩ := oldPlans.lookup found position
    have oldShape : ScopeLabel current top :=
      ⟨shape.front, by simpa [SourceScope.advance, SourceScope.branchTypes] using shape.branchTypes, shape.results⟩
    have selected := scope_labels_lookup (List.Forall₂.cons oldShape parentShapes) scopeAt labelAt
    have layout : BranchLayout locals stack label dst src count := by
      refine ⟨discarded, ?_, ?_, ?_, ?_⟩
      · simpa only [selected.front, selected.branchTypes] using stackEq
      · simpa only [selected.front] using destination
      · simpa only [selected.front] using source
      · simpa only [selected.branchTypes] using width
    have prior := invariant.resolved oldPlans oldShape parentShapes
    have saved := (invariant.prefixes top labels groups oldPlans oldShape parentShapes).1
    have resolved := resolved_code_append_code before.function.code.val
      (branchInstructions dst src count frame.start_pc) groups prior.inside
    refine ⟨?_, ?_⟩
    · rw [codeEq, resolved]
      exact (saved.extend (branchInstructions dst src count frame.start_pc)).advance_current (.BR (.mk_uN depth))
    · have fragment : Segment (resolvedCode before.function.code.val groups ++ branchInstructions dst src count frame.start_pc)
          before.function.code.val.length (branchInstructions dst src count label.target)
          after.function.code.val.length := by
        rw [future.loopTarget isLoop]
        exact ⟨resolvedCode before.function.code.val groups, [], by simp,
          resolved_code_length _ _, by simp [codeEq, resolved_code_length]⟩
      have terminal := (prior.code.extend (branchInstructions dst src count frame.start_pc)).terminal
        (StructuredDeadPrefix.branch labelAt (future.loopLive isLoop) layout fragment)
      simpa only [codeEq, resolved, SourceScope.advance, SourceScope.input] using terminal

/-- Conditional loop branches preserve the active prefix at their literal
fallthrough coordinate, using the same fixed loop target. -/
theorem StructuredUniversalPrefix.branch_if_loop {jumpTables : List Aeneas.Std.U32} {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current stack}
    (invariant : StructuredUniversalPrefix (jumpTables := jumpTables) emit before types functions returns locals parents current (stack ++ [.I32]))
    (frame : runtime.compiler.Frame) (index depth : Nat) (scope : SourceScope)
    (dst src count condition resume : U32)
    (found : before.frames.val[index]? = some frame)
    (position : index + depth + 1 = before.frames.val.length)
    (isLoop : frame.kind = .Loop)
    (scopeAt : (current :: parents.reverse)[depth]? = some scope)
    (discarded : List valtype) (stackEq : stack = scope.front ++ discarded ++ scope.branchTypes)
    (destination : dst.val = slots locals + slots scope.front)
    (source : src.val = slots locals + slots (scope.front ++ discarded))
    (width : count.val = slots scope.branchTypes)
    (codeEq : after.function.code.val = before.function.code.val ++ branchIfInstructions dst src count frame.start_pc condition resume)
    (framesEq : after.frames = before.frames) (localsEq : compilerLocals after = locals)
    (afterLayout : CompilerLayout after stack)
    (conditionSlot : condition.val = slots locals + slots stack)
    (resumePosition : resume.val = after.function.code.val.length) :
    StructuredUniversalPrefix (jumpTables := jumpTables) emit after types functions returns locals parents (current.advance (.BR_IF (.mk_uN depth))) stack := by
  have lengthOrder : before.function.code.val.length ≤ after.function.code.val.length := by simp [codeEq]
  refine ⟨localsEq, afterLayout, ?_, ?_⟩
  · intro f member
    rw [framesEq] at member
    simpa only [codeEq] using (invariant.sites f member).extend (branchIfInstructions dst src count frame.start_pc condition resume)
  · intro top labels groups plans shape parentShapes
    have oldPlans : FramePlans before.function.code.val.length locals before.frames.val (top :: labels) groups := by
      rw [← framesEq]
      exact plans.before lengthOrder
    obtain ⟨label, guard, labelAt, future⟩ := oldPlans.lookup found position
    have oldShape : ScopeLabel current top :=
      ⟨shape.front, by simpa [SourceScope.advance, SourceScope.branchTypes] using shape.branchTypes, shape.results⟩
    have selected := scope_labels_lookup (List.Forall₂.cons oldShape parentShapes) scopeAt labelAt
    have layout : BranchLayout locals stack label dst src count := by
      refine ⟨discarded, ?_, ?_, ?_, ?_⟩
      · simpa only [selected.front, selected.branchTypes] using stackEq
      · simpa only [selected.front] using destination
      · simpa only [selected.front] using source
      · simpa only [selected.branchTypes] using width
    have prior := invariant.resolved oldPlans oldShape parentShapes
    have saved := (invariant.prefixes top labels groups oldPlans oldShape parentShapes).1
    have resolved := resolved_code_append_code before.function.code.val
      (branchIfInstructions dst src count frame.start_pc condition resume) groups prior.inside
    refine ⟨?_, ?_⟩
    · rw [codeEq, resolved]
      exact (saved.extend (branchIfInstructions dst src count frame.start_pc condition resume)).advance_current (.BR_IF (.mk_uN depth))
    · have fragment : Segment (resolvedCode before.function.code.val groups ++ branchIfInstructions dst src count frame.start_pc condition resume)
          before.function.code.val.length (branchIfInstructions dst src count label.target condition resume) resume.val := by
        rw [future.loopTarget isLoop]
        exact ⟨resolvedCode before.function.code.val groups, [], by simp,
          resolved_code_length _ _, by simp [resumePosition, codeEq, resolved_code_length]⟩
      have advanced := (prior.code.extend (branchIfInstructions dst src count frame.start_pc condition resume)).append
        (StructuredPrefix.branch_if labelAt (future.loopLive isLoop) layout conditionSlot fragment)
      simpa only [codeEq, resolved, resumePosition, SourceScope.advance, SourceScope.input] using advanced

end Itasca.Compiler

end

/-! ## StructuredUniversalOpen -/

section

namespace Itasca.Compiler
open Aeneas.Std

/-- Opening BLOCK or LOOP suspends the current source prefix and starts an
empty child body. The exact callback equations supply the emitted hook (if any)
and the freshly appended frame; no future exit coordinate is chosen here. -/
theorem StructuredUniversalPrefix.open_plain {jumpTables : List Aeneas.Std.U32} {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current stack}
    (invariant : StructuredUniversalPrefix (jumpTables := jumpTables) emit before types functions returns locals parents current stack)
    (child : SourceScope) (frame : runtime.compiler.Frame) (emitted : List Bytecode)
    (codeEq : after.function.code.val = before.function.code.val ++ emitted)
    (framesEq : after.frames.val = before.frames.val ++ [frame])
    (noGuard : frame.if_pc = none) (noBranches : frame.fixups.val = [])
    (localsEq : compilerLocals after = locals) (layout : CompilerLayout after stack)
    (parentEntered : current.entered = true) (childEntered : child.entered = true)
    (entry : child.entry = before.function.code.val.length)
    (body : child.bodyPc = after.function.code.val.length) (source : child.source = [])
    (input : child.input = stack) (arguments : child.arguments = stack) :
    StructuredUniversalPrefix (jumpTables := jumpTables) emit after types functions returns locals (parents ++ [current]) child stack := by
  have lengthOrder : before.function.code.val.length ≤ after.function.code.val.length := by simp [codeEq]
  refine ⟨localsEq, layout, ?_, ?_⟩
  · intro f member
    rw [framesEq] at member
    rcases List.mem_append.mp member with old | fresh
    · simpa only [codeEq] using (invariant.sites f old).extend emitted
    · simp only [List.mem_singleton] at fresh
      subst f
      exact ⟨by simp [ForwardSites, noBranches], by simp [noGuard]⟩
  · intro label labels groups plans shape parentShapes
    rw [framesEq] at plans
    obtain ⟨top, outer, pending, target, labelsEq, groupsEq, priorPlans, future⟩ := plans.pop
    simp only [List.cons.injEq] at labelsEq
    obtain ⟨rfl, rfl⟩ := labelsEq
    have simplified : groups = ⟨[], label.target⟩ :: pending := by
      simpa [frameGroups, noGuard, noBranches] using groupsEq
    rw [simplified]
    have resolve : resolvedCode after.function.code.val (⟨[], label.target⟩ :: pending) =
        resolvedCode before.function.code.val pending ++ emitted := by
      simp only [resolvedCode, patchCode, codeEq]
      apply resolved_code_append_code
      exact priorPlans.inside invariant.sites
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append] at parentShapes
    cases parentShapes with
    | @cons _ parentLabel _ outerLabels parentShape parentShapes =>
      have oldPlans := priorPlans.before lengthOrder
      obtain ⟨saved, prefixCode⟩ := invariant.prefixes parentLabel outerLabels pending
        oldPlans parentShape parentShapes
      have prior : StructuredPrefix (jumpTables := jumpTables) emit types functions returns locals (resolvedCode before.function.code.val pending)
          (parentLabel :: outerLabels) current.input current.source current.bodyPc
          (resolvedCode before.function.code.val pending).length stack := by
        simpa only [resolved_code_length] using prefixCode
      refine ⟨?_, ?_⟩
      · rw [resolve]
        apply StructuredParentPrefixes.push (saved.extend emitted) parentLabel child parentShape
        · simp only [List.length_append, resolved_code_length, entry]
          omega
        · unfold StructuredParentPrefix
          simp only [parentEntered, childEntered, ite_true]
          simpa only [entry, arguments, resolved_code_length] using prior.suspend_after emitted
      · simpa only [source, input, body] using
          StructuredPrefix.empty emit types functions returns locals
            (resolvedCode after.function.code.val (⟨[], label.target⟩ :: pending))
            (label :: parentLabel :: outerLabels) stack after.function.code.val.length

/-- IF adds one fresh guard group before beginning its child body. Its target
remains universally quantified until ELSE or END resolves that group. -/
theorem StructuredUniversalPrefix.open_if {jumpTables : List Aeneas.Std.U32} {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current stack}
    (invariant : StructuredUniversalPrefix (jumpTables := jumpTables) emit before types functions returns locals parents current (stack ++ [.I32]))
    (child : SourceScope) (frame : runtime.compiler.Frame) (condition : U32) (site : Usize)
    (sitePosition : site.val = before.function.code.val.length)
    (codeEq : after.function.code.val = before.function.code.val ++ [.JumpIfZero condition core.num.U32.MAX])
    (framesEq : after.frames.val = before.frames.val ++ [frame])
    (guardEq : frame.if_pc = some site) (noBranches : frame.fixups.val = [])
    (localsEq : compilerLocals after = locals) (layout : CompilerLayout after stack)
    (parentEntered : current.entered = true) (childEntered : child.entered = true)
    (entry : child.entry = before.function.code.val.length)
    (body : child.bodyPc = after.function.code.val.length) (source : child.source = [])
    (input : child.input = stack) (arguments : child.arguments = stack ++ [.I32]) :
    StructuredUniversalPrefix (jumpTables := jumpTables) emit after types functions returns locals (parents ++ [current]) child stack := by
  have lengthOrder : before.function.code.val.length ≤ after.function.code.val.length := by simp [codeEq]
  refine ⟨localsEq, layout, ?_, ?_⟩
  · intro f member
    rw [framesEq] at member
    rcases List.mem_append.mp member with old | fresh
    · simpa only [codeEq] using (invariant.sites f old).extend [.JumpIfZero condition core.num.U32.MAX]
    · simp only [List.mem_singleton] at fresh
      subst f
      refine ⟨by simp [ForwardSites, noBranches], ?_⟩
      intro guard atGuard
      have same : guard = site := by simpa [guardEq] using atGuard.symm
      subst guard
      exact ⟨condition, core.num.U32.MAX, by simp [codeEq, sitePosition]⟩
  · intro label labels groups plans shape parentShapes
    rw [framesEq] at plans
    obtain ⟨top, outer, pending, target, labelsEq, groupsEq, priorPlans, future⟩ := plans.pop
    simp only [List.cons.injEq] at labelsEq
    obtain ⟨rfl, rfl⟩ := labelsEq
    have simplified : groups = ⟨[site], target⟩ :: ⟨[], label.target⟩ :: pending := by
      simpa [frameGroups, guardEq, noBranches] using groupsEq
    rw [simplified]
    have resolve : resolvedCode after.function.code.val (⟨[site], target⟩ :: ⟨[], label.target⟩ :: pending) =
        resolvedCode before.function.code.val pending ++ [.JumpIfZero condition target] := by
      change resolvedCode after.function.code.val (⟨[site], target⟩ :: pending) = _
      rw [codeEq]
      exact resolved_code_open_guard _ _ condition core.num.U32.MAX target site sitePosition
        (priorPlans.inside invariant.sites)
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append] at parentShapes
    cases parentShapes with
    | @cons _ parentLabel _ outerLabels parentShape parentShapes =>
      have oldPlans := priorPlans.before lengthOrder
      obtain ⟨saved, prefixCode⟩ := invariant.prefixes parentLabel outerLabels pending
        oldPlans parentShape parentShapes
      have prior : StructuredPrefix (jumpTables := jumpTables) emit types functions returns locals (resolvedCode before.function.code.val pending)
          (parentLabel :: outerLabels) current.input current.source current.bodyPc
          (resolvedCode before.function.code.val pending).length (stack ++ [.I32]) := by
        simpa only [resolved_code_length] using prefixCode
      refine ⟨?_, ?_⟩
      · rw [resolve]
        apply StructuredParentPrefixes.push (saved.extend [.JumpIfZero condition target]) parentLabel child parentShape
        · simp only [List.length_append, resolved_code_length, entry]
          omega
        · unfold StructuredParentPrefix
          simp only [parentEntered, childEntered, ite_true]
          simpa only [entry, arguments, resolved_code_length] using prior.suspend_after [.JumpIfZero condition target]
      · simpa only [source, input, body] using
          StructuredPrefix.empty emit types functions returns locals
            (resolvedCode after.function.code.val (⟨[site], target⟩ :: ⟨[], label.target⟩ :: pending))
            (label :: parentLabel :: outerLabels) stack after.function.code.val.length

end Itasca.Compiler

end

/-! ## StructuredCodeLabels -/

section

namespace Itasca.Compiler
open Aeneas.Std

theorem StructuredCode.Targets.cons {emission types functions returns locals code jumpTables label labels next after}
    (outer : StructuredCode.Targets emission types functions returns locals code jumpTables labels)
    (target : label.branchLive = true → StructuredCode emission types functions returns locals code jumpTables labels (label.front ++ label.branchTypes)
      (label.cont ++ label.after) label.target.val next after)
    (aligned : label.branchLive = true → ExitAligned labels next)
    (root : label.branchLive = true → RootAligned code returns labels next after) :
    StructuredCode.Targets emission types functions returns locals code jumpTables (label :: labels) := by
  intro depth found lookup live
  cases depth with
  | zero =>
    have same : found = label := by simpa using lookup.symm
    subst found
    exact ⟨next, after, by simpa using target live, by simpa using aligned live, by simpa using root live⟩
  | succ depth =>
    simpa using outer depth found (by simpa using lookup) live

theorem StructuredCode.Normals.cons {emission types functions returns locals code jumpTables label labels next after}
    (outer : StructuredCode.Normals emission types functions returns locals code jumpTables labels)
    (target : label.normalLive = true → StructuredCode emission types functions returns locals code jumpTables labels (label.front ++ label.resultTypes)
      label.after label.normalExit next after)
    (aligned : label.normalLive = true → ExitAligned labels next)
    (root : label.normalLive = true → RootAligned code returns labels next after) :
    StructuredCode.Normals emission types functions returns locals code jumpTables (label :: labels) := by
  intro depth found lookup live
  cases depth with
  | zero =>
    have same : found = label := by simpa using lookup.symm
    subst found
    exact ⟨next, after, by simpa using target live, by simpa using aligned live, by simpa using root live⟩
  | succ depth => simpa using outer depth found (by simpa using lookup) live

theorem StructuredCode.Point.block_body {emission types functions returns locals code jumpTables labels front params results
    after body pc normalExit branchExit next final normalLive branchLive}
    (bodyCode : StructuredCode emission types functions returns locals code jumpTables
      (⟨front, results, results, branchExit, normalExit, [], after, normalLive, branchLive⟩ :: labels)
      (front ++ params) body pc normalExit (front ++ results))
    (rest : normalLive = true → StructuredCode emission types functions returns locals code jumpTables labels (front ++ results) after normalExit next final)
    (targetRest : branchLive = true → StructuredCode emission types functions returns locals code jumpTables labels (front ++ results) after
      branchExit.val next final)
    (outer : StructuredCode.Targets emission types functions returns locals code jumpTables labels)
    (normal : StructuredCode.Normals emission types functions returns locals code jumpTables labels)
    (restAligned : ExitAligned labels next)
    (root : RootAligned code returns labels next final) :
    StructuredCode.Point emission types functions returns locals code jumpTables
      (⟨front, results, results, branchExit, normalExit, [], after, normalLive, branchLive⟩ :: labels)
      (front ++ params) body pc normalExit (front ++ results) :=
  ⟨bodyCode, outer.cons (by simpa using targetRest) (fun _ => restAligned) (fun _ => root),
    normal.cons (by simpa using rest) (fun _ => restAligned) (fun _ => root), ExitAligned.cons _ _, RootAligned.cons _ _ _ _ _ _⟩

theorem StructuredCode.Point.loop_body {emission types functions returns locals code jumpTables labels front params results
    after body bt entry exit next final normalLive}
    (signature : BlockSignature types bt params results)
    (head : code[entry.val]? = some .LoopHead)
    (bodyCode : StructuredCode emission types functions returns locals code jumpTables
      (⟨front, params, results, entry, exit, [.LOOP bt body], after, normalLive, true⟩ :: labels)
      (front ++ params) body (entry.val + 1) exit (front ++ results))
    (rest : normalLive = true → StructuredCode emission types functions returns locals code jumpTables labels (front ++ results) after exit next final)
    (bounds : entry.val ≤ next ∧ next ≤ code.length)
    (outer : StructuredCode.Targets emission types functions returns locals code jumpTables labels)
    (normal : StructuredCode.Normals emission types functions returns locals code jumpTables labels)
    (aligned : ExitAligned labels next)
    (root : RootAligned code returns labels next final) :
    StructuredCode.Point emission types functions returns locals code jumpTables
      (⟨front, params, results, entry, exit, [.LOOP bt body], after, normalLive, true⟩ :: labels)
      (front ++ params) body (entry.val + 1) exit (front ++ results) := by
  exact ⟨bodyCode, outer.cons (fun _ => StructuredCode.loop signature head bodyCode rest bounds) (fun _ => aligned) (fun _ => root),
    normal.cons rest (fun _ => aligned) (fun _ => root), ExitAligned.cons _ _, RootAligned.cons _ _ _ _ _ _⟩

/-- A selected then arm retains a skip only if normal fallthrough is live. -/
theorem StructuredCode.if_then {emission types functions returns locals code jumpTables labels front params results
    after yes bt pc yesExit exit next final yesNormal yesBranch} {noEntry : U32}
    (signature : BlockSignature types bt params results)
    (yesCode : StructuredCode emission types functions returns locals code jumpTables
      (⟨front, results, results, exit, yesExit, [], after, yesNormal, yesBranch⟩ :: labels)
      (front ++ params) yes pc yesExit (front ++ results))
    (skip : IfSkip code yesExit noEntry exit yesNormal)
    (order : noEntry.val ≤ exit.val)
    (rest : yesNormal = true ∨ yesBranch = true →
      StructuredCode emission types functions returns locals code jumpTables labels (front ++ results) after exit.val next final)
    (bounds : pc ≤ next ∧ next ≤ code.length) :
    StructuredCode emission types functions returns locals code jumpTables labels (front ++ params)
      (.BLOCK bt yes :: after) pc next final := by
  apply StructuredCode.block signature yesCode ?_ (fun live => rest (Or.inr live)) bounds
  intro live
  cases skip with
  | direct normal otherwise => simpa only [normal] using rest (Or.inl live)
  | emitted fragment =>
    have skipLive : Segment code yesExit [.Jump exit] noEntry.val := by simpa only [live, ite_true] using fragment
    have forward : yesExit < exit.val := by
      obtain ⟨_, _, _, _, h⟩ := skipLive
      simp only [List.length_singleton] at h
      omega
    have fetched := skipLive.fetch (index := 0) (by rfl)
    simp only [Nat.add_zero] at fetched
    exact StructuredCode.skip forward fetched (rest (Or.inl live))

/-- The ordinary block has coincident fallthrough and branch exits. -/
theorem StructuredCode.ordinary_block {emission types functions returns locals code jumpTables labels front params results
    after body bt pc exit next final normalLive branchLive}
    (signature : BlockSignature types bt params results)
    (bodyCode : StructuredCode emission types functions returns locals code jumpTables
      (⟨front, results, results, exit, exit.val, [], after, normalLive, branchLive⟩ :: labels)
      (front ++ params) body pc exit.val (front ++ results))
    (rest : normalLive = true ∨ branchLive = true →
      StructuredCode emission types functions returns locals code jumpTables labels (front ++ results) after exit.val next final)
    (bounds : pc ≤ next ∧ next ≤ code.length) :
    StructuredCode emission types functions returns locals code jumpTables labels (front ++ params) (.BLOCK bt body :: after) pc next final :=
  StructuredCode.block signature bodyCode (fun live => rest (Or.inl live)) (fun live => rest (Or.inr live)) bounds

end Itasca.Compiler

end

/-! ## StructuredFunction -/

section

namespace Itasca.Compiler
open Aeneas.Std

/-- Initial execution receives the body's structured point and the implicit
label's source continuation at the checked epilogue. -/
theorem StructuredFunctionCode.entry {emit typeTable functions params declared results body compiled epilogue}
    (certificate : StructuredFunctionCode emit typeTable functions params declared results body compiled epilogue) :
    StructuredCode.Point emit typeTable functions results (params ++ declared) compiled.code.val compiled.jump_tables.val
      [functionRootLabel results compiled epilogue] [] body 0 epilogue.val results := by
  have bound : epilogue.val ≤ compiled.code.val.length := by have := certificate.endPosition; omega
  have root (live : (functionRootLabel results compiled epilogue).branchLive = true) :
      RootAligned compiled.code.val results [] epilogue.val results := by
    intro _
    obtain ⟨count, found⟩ := certificate.returnCode
    exact ⟨certificate.endPosition.symm, rfl, compiled.local_slots, count,
      function_root_label_live found live, found⟩
  refine ⟨certificate.bodyCode, ?_, ?_, ExitAligned.cons _ _, RootAligned.cons _ _ _ _ _ _⟩
  · apply StructuredCode.Targets.cons
    · intro depth label lookup; simp at lookup
    · intro _
      exact StructuredCode.nil [] _ _ bound NormalLive.nil
    · intro _ label lookup; simp at lookup
    · exact root
  · apply StructuredCode.Normals.cons
    · intro depth label lookup; simp at lookup
    · intro _
      exact StructuredCode.nil [] _ _ bound NormalLive.nil
    · intro _ label lookup; simp at lookup
    · exact root

end Itasca.Compiler

end

end
