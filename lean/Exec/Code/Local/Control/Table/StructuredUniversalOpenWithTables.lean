import Exec.Code.Local.Control.Table.StructuredUniversalPrefixWithTables
import Exec.Code.Local.Control.Table.StructuredParentPrefixChangeWithTables
import Exec.Code.Local.Control.Common.UniversalOpen
namespace Exec.Code
open Aeneas.Std

/-- Opening BLOCK or LOOP suspends the current source prefix and starts an
empty child body. The exact callback equations supply the emitted hook (if any)
and the freshly appended frame; no future exit coordinate is chosen here. -/
theorem StructuredUniversalPrefixWithTables.open_plain {jumpTables : List Aeneas.Std.U32} {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current stack}
    (invariant : StructuredUniversalPrefixWithTables (jumpTables := jumpTables) emit before types functions returns locals parents current stack)
    (child : SourceScope) (frame : runtime.compiler.Frame) (emitted : List Bytecode)
    (codeEq : after.function.code.val = before.function.code.val ++ emitted)
    (framesEq : after.frames.val = before.frames.val ++ [frame])
    (noGuard : frame.if_pc = none) (noBranches : frame.fixups.val = [])
    (localsEq : compilerLocals after = locals) (layout : CompilerLayout after stack)
    (parentEntered : current.entered = true) (childEntered : child.entered = true)
    (entry : child.entry = before.function.code.val.length)
    (body : child.bodyPc = after.function.code.val.length) (source : child.source = [])
    (input : child.input = stack) (arguments : child.arguments = stack) :
    StructuredUniversalPrefixWithTables (jumpTables := jumpTables) emit after types functions returns locals (parents ++ [current]) child stack := by
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
      apply resolvedCode_append_code
      exact priorPlans.inside invariant.sites
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append] at parentShapes
    cases parentShapes with
    | @cons _ parentLabel _ outerLabels parentShape parentShapes =>
      have oldPlans := priorPlans.before lengthOrder
      obtain ⟨saved, prefixCode⟩ := invariant.prefixes parentLabel outerLabels pending
        oldPlans parentShape parentShapes
      have prior : StructuredPrefixWithTables (jumpTables := jumpTables) emit types functions returns locals (resolvedCode before.function.code.val pending)
          (parentLabel :: outerLabels) current.input current.source current.bodyPc
          (resolvedCode before.function.code.val pending).length stack := by
        simpa only [resolvedCode_length] using prefixCode
      refine ⟨?_, ?_⟩
      · rw [resolve]
        apply StructuredParentPrefixesWithTables.push (saved.extend emitted) parentLabel child parentShape
        · simp only [List.length_append, resolvedCode_length, entry]
          omega
        · unfold StructuredParentPrefixWithTables
          simp only [parentEntered, childEntered, ite_true]
          simpa only [entry, arguments, resolvedCode_length] using prior.suspend_after emitted
      · simpa only [source, input, body] using
          StructuredPrefixWithTables.empty emit types functions returns locals
            (resolvedCode after.function.code.val (⟨[], label.target⟩ :: pending))
            (label :: parentLabel :: outerLabels) stack after.function.code.val.length

/-- IF adds one fresh guard group before beginning its child body. Its target
remains universally quantified until ELSE or END resolves that group. -/
theorem StructuredUniversalPrefixWithTables.open_if {jumpTables : List Aeneas.Std.U32} {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current stack}
    (invariant : StructuredUniversalPrefixWithTables (jumpTables := jumpTables) emit before types functions returns locals parents current (stack ++ [.I32]))
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
    StructuredUniversalPrefixWithTables (jumpTables := jumpTables) emit after types functions returns locals (parents ++ [current]) child stack := by
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
      exact resolvedCode_open_guard _ _ condition core.num.U32.MAX target site sitePosition
        (priorPlans.inside invariant.sites)
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append] at parentShapes
    cases parentShapes with
    | @cons _ parentLabel _ outerLabels parentShape parentShapes =>
      have oldPlans := priorPlans.before lengthOrder
      obtain ⟨saved, prefixCode⟩ := invariant.prefixes parentLabel outerLabels pending
        oldPlans parentShape parentShapes
      have prior : StructuredPrefixWithTables (jumpTables := jumpTables) emit types functions returns locals (resolvedCode before.function.code.val pending)
          (parentLabel :: outerLabels) current.input current.source current.bodyPc
          (resolvedCode before.function.code.val pending).length (stack ++ [.I32]) := by
        simpa only [resolvedCode_length] using prefixCode
      refine ⟨?_, ?_⟩
      · rw [resolve]
        apply StructuredParentPrefixesWithTables.push (saved.extend [.JumpIfZero condition target]) parentLabel child parentShape
        · simp only [List.length_append, resolvedCode_length, entry]
          omega
        · unfold StructuredParentPrefixWithTables
          simp only [parentEntered, childEntered, ite_true]
          simpa only [entry, arguments, resolvedCode_length] using prior.suspend_after [.JumpIfZero condition target]
      · simpa only [source, input, body] using
          StructuredPrefixWithTables.empty emit types functions returns locals
            (resolvedCode after.function.code.val (⟨[site], target⟩ :: ⟨[], label.target⟩ :: pending))
            (label :: parentLabel :: outerLabels) stack after.function.code.val.length

end Exec.Code

