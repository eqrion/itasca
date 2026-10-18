import Exec.Code.Local.Control.Common.StructuredUniversalTerminal
import Exec.Code.Local.Control.Common.StructuredParentPrefixPop
import Exec.Code.Local.Control.Common.UniversalDormant
namespace Exec.Code
open Aeneas.Std

/-- An unentered source subtree emits no executable body. Its enclosing
terminal prefix remains retained; no code relation is asserted for the child. -/
structure StructuredUniversalDormant (emit : List valtype → instr → List Bytecode → List valtype → Prop) {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope) : Prop where
  unentered : current.entered = false
  localsEq : compilerLocals compiler = locals
  sites : ∀ frame ∈ compiler.frames.val, FrameSites compiler.function.code.val frame
  prefixes : ∀ label labels groups,
    FramePlans compiler.function.code.val.length locals compiler.frames.val (label :: labels) groups →
    ScopeLabel current label → List.Forall₂ ScopeLabel parents.reverse labels →
    StructuredParentPrefixes emit types functions returns locals (resolvedCode compiler.function.code.val groups)
      parents labels current

theorem StructuredUniversalDormant.skip {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current}
    (invariant : StructuredUniversalDormant emit before types functions returns locals parents current)
    (instruction : instr) (codeEq : after.function.code = before.function.code)
    (framesEq : after.frames = before.frames) (localsEq : compilerLocals after = locals) :
    StructuredUniversalDormant emit after types functions returns locals parents (current.advance instruction) := by
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
theorem StructuredUniversalTerminal.open_dormant {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current}
    (invariant : StructuredUniversalTerminal emit before types functions returns locals parents current)
    (child : SourceScope) (frame : runtime.compiler.Frame)
    (codeEq : after.function.code = before.function.code)
    (framesEq : after.frames.val = before.frames.val ++ [frame])
    (noGuard : frame.if_pc = none) (noBranches : frame.fixups.val = [])
    (localsEq : compilerLocals after = locals)
    (parentEntered : current.entered = true) (childEntered : child.entered = false)
    (entry : child.entry = before.function.code.val.length) :
    StructuredUniversalDormant emit after types functions returns locals (parents ++ [current]) child := by
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
      have prior : StructuredDeadPrefix emit types functions returns locals (resolvedCode before.function.code.val pending)
          (parentLabel :: outerLabels) current.input current.source current.bodyPc
          (resolvedCode before.function.code.val pending).length := by
        simpa only [resolvedCode_length] using prefixCode
      rw [resolve]
      apply StructuredParentPrefixes.push saved parentLabel child parentShape
      · simp [entry, resolvedCode_length]
      · unfold StructuredParentPrefix
        simp only [parentEntered, childEntered, ite_true, Bool.false_eq_true, ite_false]
        simpa only [entry, resolvedCode_length] using prior.suspend

theorem StructuredUniversalDormant.open_dormant {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current}
    (invariant : StructuredUniversalDormant emit before types functions returns locals parents current)
    (child : SourceScope) (frame : runtime.compiler.Frame)
    (codeEq : after.function.code = before.function.code)
    (framesEq : after.frames.val = before.frames.val ++ [frame])
    (noGuard : frame.if_pc = none) (noBranches : frame.fixups.val = [])
    (localsEq : compilerLocals after = locals)
    (childEntered : child.entered = false)
    (entry : child.entry = before.function.code.val.length) :
    StructuredUniversalDormant emit after types functions returns locals (parents ++ [current]) child := by
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
      · simp [entry, resolvedCode_length]
      · simp [StructuredParentPrefix, invariant.unentered]

/-- Closing an unentered child restores the terminal prefix of its entered
parent. The child's discarded source is retained syntactically in that suffix. -/
theorem StructuredUniversalDormant.close_terminal {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents parent child}
    (invariant : StructuredUniversalDormant emit before types functions returns locals (parents ++ [parent]) child)
    (frame : runtime.compiler.Frame) (label : LabelTarget) (guardTarget : U32)
    (frames : before.frames.val = after.frames.val ++ [frame])
    (future : FrameFuture before.function.code.val.length locals frame label guardTarget)
    (shape : ScopeLabel child label)
    (codeEq : after.function.code.val = resolvedCode before.function.code.val (frameGroups frame label guardTarget))
    (sites : ∀ f ∈ after.frames.val, FrameSites after.function.code.val f)
    (localsEq : compilerLocals after = locals) (parentEntered : parent.entered = true)
    (instruction : instr) :
    StructuredUniversalTerminal emit after types functions returns locals parents (parent.advance instruction) := by
  refine ⟨localsEq, sites, ?_⟩
  intro parentLabel labels groups plans parentShape parentShapes
  have lengthEq : after.function.code.val.length = before.function.code.val.length := by
    simp [codeEq, resolvedCode_length]
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
  · rw [codeEq, ← resolvedCode_append_groups]
    exact outerSaved.advance_current instruction
  · simpa only [codeEq, ← resolvedCode_append_groups, resolvedCode_length,
      SourceScope.advance, SourceScope.input] using restored

/-- If the parent was itself unentered, closing its child preserves that
mode without constructing an execution relation for either discarded body. -/
theorem StructuredUniversalDormant.close_dormant {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents parent child}
    (invariant : StructuredUniversalDormant emit before types functions returns locals (parents ++ [parent]) child)
    (frame : runtime.compiler.Frame) (label : LabelTarget) (guardTarget : U32)
    (frames : before.frames.val = after.frames.val ++ [frame])
    (future : FrameFuture before.function.code.val.length locals frame label guardTarget)
    (shape : ScopeLabel child label)
    (codeEq : after.function.code.val = resolvedCode before.function.code.val (frameGroups frame label guardTarget))
    (sites : ∀ f ∈ after.frames.val, FrameSites after.function.code.val f)
    (localsEq : compilerLocals after = locals) (parentEntered : parent.entered = false)
    (instruction : instr) :
    StructuredUniversalDormant emit after types functions returns locals parents (parent.advance instruction) := by
  refine ⟨parentEntered, localsEq, sites, ?_⟩
  intro parentLabel labels groups plans parentShape parentShapes
  have lengthEq : after.function.code.val.length = before.function.code.val.length := by
    simp [codeEq, resolvedCode_length]
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
  rw [codeEq, ← resolvedCode_append_groups]
  exact outerSaved.advance_current instruction

end Exec.Code

