import Itasca.Runtime.Compiler.Local.Control.Table.StructuredUniversalTerminal
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalDormant
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ElseFrames
import Itasca.Runtime.Compiler.Local.Relations.Prefix.SuspendedPrefix
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CompilerCodeMonotoneControl
import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.FixupBudget
import Itasca.Runtime.Compiler.Local.Relations.Prefix.ResolvedGuards
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalRoot
import Itasca.Runtime.Compiler.Local.Relations.Prefix.PrefixZipper

/-!
Sections, each formerly its own module: StructuredUniversalDormant, StructuredUniversalBranchTable, StructuredPrefixClose, StructuredCompletedPrefix, StructuredParentPrefixChange, StructuredElseSource, StructuredUniversalElse, StructuredUniversalDormantElse, StructuredElseFrames, StructuredPrefixControl, StructuredPrefixElse, StructuredUniversalCloseDeadElse.
-/

/-! ## StructuredUniversalDormant -/

section

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end

/-! ## StructuredUniversalBranchTable -/

section

namespace Itasca.Runtime.Compiler
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
end Itasca.Runtime.Compiler

end

/-! ## StructuredPrefixClose -/

section

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end

/-! ## StructuredCompletedPrefix -/

section

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end

/-! ## StructuredParentPrefixChange -/

section

namespace Itasca.Runtime.Compiler

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

end Itasca.Runtime.Compiler

end

/-! ## StructuredElseSource -/

section

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end

/-! ## StructuredUniversalElse -/

section

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end

/-! ## StructuredUniversalDormantElse -/

section

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end

/-! ## StructuredElseFrames -/

section

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end

/-! ## StructuredPrefixControl -/

section

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end

/-! ## StructuredPrefixElse -/

section

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end

/-! ## StructuredUniversalCloseDeadElse -/

section

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end
