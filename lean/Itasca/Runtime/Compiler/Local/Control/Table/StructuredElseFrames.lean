import Itasca.Runtime.Compiler.Local.Control.Table.StructuredElseSource
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ElseFrames
namespace Itasca.Runtime.Code
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
    simp [codeEq, resolvedCode_length]
  have outer : FramePlans before.function.code.val.length locals after.frames.val (parentLabel :: labels) groups := by
    simpa only [lengthEq] using plans
  have oldParentShape : ScopeLabel parent parentLabel :=
    ⟨parentShape.front, by simpa [SourceScope.advance, SourceScope.branchTypes] using parentShape.branchTypes, parentShape.results⟩
  have allPlans := FramePlans.push outer frame label guardTarget future
  rw [← frames] at allPlans
  have allShapes : List.Forall₂ ScopeLabel (parents ++ [parent]).reverse (parentLabel :: labels) := by
    simpa using List.Forall₂.cons oldParentShape parentShapes
  have arms := invariant label (parentLabel :: labels) _ allPlans shape allShapes
  rw [codeEq, ← resolvedCode_append_groups]
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
    exact resolvedCode_append_code _ _ _ (priorPlans.inside sites)
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
    exact resolvedCode_open_guard _ _ condition core.num.U32.MAX target site position (priorPlans.inside sites)
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append] at parentShapes ⊢
  cases parentShapes with
  | @cons _ parentLabel _ outerLabels parentShape parentShapes =>
    have arms := invariant parentLabel outerLabels pending (priorPlans.before order) parentShape parentShapes
    rw [resolve]
    exact .cons child label (StructuredElseEvidence.fresh fresh) (arms.extend _)

end Itasca.Runtime.Code

