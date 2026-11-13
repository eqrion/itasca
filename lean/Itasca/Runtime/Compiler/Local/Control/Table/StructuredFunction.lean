import Itasca.Runtime.Compiler.Local.Relations.Prefix.ConsumedPrefix
import Itasca.Runtime.Compiler.Local.Control.Table.StructuredUniversalTerminal
import Itasca.Runtime.Compiler.Local.Callbacks.Function.CloseFunction
import Itasca.Runtime.Compiler.Local.Relations.Function.Function
import Itasca.Runtime.Compiler.Local.Relations.Control.ResolvedBranchPrefix
import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.FixupBudget
import Itasca.Runtime.Compiler.Local.Control.Control.StructuredElseResolvedAppend
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalRoot
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ElseFrames
import Itasca.Runtime.Compiler.Local.Control.Table.StructuredUniversalCloseDeadElse
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalPrefix
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredLabels
import Itasca.Runtime.Compiler.Local.Relations.Layout.LayoutProofs
import Itasca.Support.Result

/-!
Sections, each formerly its own module: StructuredLabelWiden, StructuredFunctionBodyClose, StructuredResolvedBranchPrefix, StructuredResolvedConditionalPrefix, StructuredUniversalBranch, StructuredUniversalConditional, StructuredElseBranches, StructuredUniversalLoopBranch, StructuredUniversalOpen, StructuredCodeLabels, StructuredFunction.
-/

/-! ## StructuredLabelWiden -/

section

namespace Itasca.Runtime.Compiler
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


end Itasca.Runtime.Compiler

end

/-! ## StructuredFunctionBodyClose -/

section

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end

/-! ## StructuredResolvedBranchPrefix -/

section

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end

/-! ## StructuredResolvedConditionalPrefix -/

section

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end

/-! ## StructuredUniversalBranch -/

section

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end

/-! ## StructuredUniversalConditional -/

section

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end

/-! ## StructuredElseBranches -/

section

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end

/-! ## StructuredUniversalLoopBranch -/

section

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end

/-! ## StructuredUniversalOpen -/

section

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end

/-! ## StructuredCodeLabels -/

section

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end

/-! ## StructuredFunction -/

section

namespace Itasca.Runtime.Compiler
open Aeneas.Std
/-- Complete retained syntax/layout evidence for one defined function. The
well-formedness field is the actual bytecode check, not execution correctness. -/
structure StructuredFunctionCode (emit : List valtype → instr → List Bytecode → List valtype → Prop) (typeTable functions : List functype)
    (params declared results : List valtype) (body : List instr)
    (compiled : runtime.bytecode.CompiledFunction) (epilogue : U32) : Prop where
  signature : typeTable[compiled.type_index.val]? = some ⟨.mk_list params, .mk_list results⟩
  locals : compiled.locals.val.map Itasca.Translate.valueType = params ++ declared
  parameterSlots : compiled.param_slots.val = slots params
  localSlots : compiled.local_slots.val = slots (params ++ declared)
  capacity : compiled.local_slots.val ≤ compiled.slot_count.val
  fetchBound : compiled.code.val.length ≤ U32.max
  checked : runtime.bytecode.CompiledFunction.well_formed compiled = .ok true
  bodyCode : StructuredCode emit typeTable functions results (params ++ declared) compiled.code.val compiled.jump_tables.val
    [functionRootLabel results compiled epilogue] [] body 0 epilogue.val results
  returnCode : ∃ count, compiled.code.val[epilogue.val]? = some (.Return compiled.local_slots count)
  endPosition : compiled.code.val.length = epilogue.val + 1

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

end Itasca.Runtime.Compiler

end
