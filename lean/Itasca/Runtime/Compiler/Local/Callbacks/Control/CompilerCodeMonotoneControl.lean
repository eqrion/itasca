import Itasca.Runtime.Compiler.Local.Lowering.Control.BranchEffects
import Itasca.Runtime.Compiler.Local.Lowering.Control.BranchContracts
import Itasca.Runtime.Compiler.Local.Callbacks.Control.EndContracts
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ElseContracts
import Itasca.Runtime.Compiler.Local.Source.SourceEntryChain
import Itasca.Runtime.Compiler.Local.Relations.Layout.CompileInv
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerTerminalMetadata
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CloseScope
import Itasca.Runtime.Compiler.Local.Callbacks.Control.EnterIf
import Itasca.Runtime.Compiler.Local.Relations.Control.BranchCertificates
import Itasca.Runtime.Compiler.Local.Relations.Control.ResolvedBranchPrefix
import Itasca.Runtime.Compiler.Local.Initializer.InitializerElementAppend
import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.OpenPrefix
import Itasca.Runtime.Compiler.Local.Relations.Prefix.SuspendedPrefix
import Itasca.Runtime.Compiler.Local.Control.Control.StructuredElseResolvedAppend
import Itasca.Runtime.Compiler.Local.Relations.Prefix.PrefixZipper
import Itasca.Runtime.Compiler.Local.Callbacks.CodeGrowth.CompilerCodeMonotoneLiteral

/-!
Sections, each formerly its own module: ScopeFrameSelect, CompilerBranchMetadata, CloseGuardedScope, EnterElse, ElseSuccess, ElseTransition, ScopeStackElse, ScopeStackClose, CompilerCodeMonotoneControl.
-/

/-! ## ScopeFrameSelect -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

private theorem paired_lookup {α β : Type} {R : α → β → Prop} {left right}
    (paired : List.Forall₂ R left right) (index : Nat) (item : α)
    (found : left[index]? = some item) : ∃ value, right[index]? = some value ∧ R item value := by
  induction paired generalizing index with
  | nil => simp at found
  | @cons a b left right head tail ih =>
    cases index with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at found; subst item; exact ⟨b, rfl, head⟩
    | succ index => exact ih index found

private theorem paired_reverse {α β : Type} {R : α → β → Prop} {left right}
    (paired : List.Forall₂ R left right) : List.Forall₂ R left.reverse right.reverse := by
  induction paired with
  | nil => exact .nil
  | cons head tail ih => simpa only [List.reverse_cons] using List.rel_append ih (.cons head .nil)

/-- Reverse source depth selects the same retained physical frame. -/
theorem ScopeFrameStack.selected {A : Type} {locals parents current}
    {compiler : runtime.compiler.FunctionCompiler A}
    (stack : ScopeFrameStack locals compiler parents current)
    (depth : Nat) (scope : SourceScope)
    (selected : (current :: parents.reverse)[depth]? = some scope) :
    ∃ index : Usize, ∃ frame,
      compiler.frames.val[index.val]? = some frame ∧
      index.val + depth + 1 = compiler.frames.val.length ∧
      FrameScope locals compiler scope frame := by
  have paired : List.Forall₂ (FrameScope locals compiler)
      (current :: parents.reverse) compiler.frames.val.reverse := by
    simpa only [List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.singleton_append] using paired_reverse stack.frames
  obtain ⟨frame, reversed, shape⟩ := paired_lookup paired depth scope selected
  have bound := (List.getElem?_eq_some_iff.mp reversed).1
  simp only [List.length_reverse] at bound
  let index : Usize := UScalar.ofNatCore (compiler.frames.val.length - 1 - depth) (by
    have size : compiler.frames.val.length ≤ Usize.max := by scalar_tac
    scalar_tac)
  refine ⟨index, frame, ?_, ?_, shape⟩
  · change compiler.frames.val[compiler.frames.val.length - 1 - depth]? = some frame
    simpa only [List.getElem?_reverse bound] using reversed
  · change compiler.frames.val.length - 1 - depth + depth + 1 = compiler.frames.val.length
    omega

/-- Live scopes obtain source slot geometry from the retained frame, including
ancestor scopes selected by a nonzero branch depth. -/
theorem ScopeFrameStack.selected_live {A : Type} {locals parents current}
    {compiler : runtime.compiler.FunctionCompiler A}
    (stack : ScopeFrameStack locals compiler parents current)
    (chain : SourceEntryChain parents current) (live : current.entered = true)
    (depth : Nat) (scope : SourceScope)
    (selected : (current :: parents.reverse)[depth]? = some scope) :
    ∃ index : Usize, ∃ frame,
      compiler.frames.val[index.val]? = some frame ∧
      index.val + depth + 1 = compiler.frames.val.length ∧
      FrameScope locals compiler scope frame ∧
      scope.entered = true ∧ frame.height.val = slots locals + slots scope.front := by
  obtain ⟨index, frame, found, position, shape⟩ := stack.selected depth scope selected
  have member : scope ∈ parents ++ [current] := by
    have member := List.mem_of_getElem? selected
    simpa only [List.mem_cons, List.mem_reverse, List.mem_append, List.mem_singleton, List.mem_nil_iff, or_false, false_or, or_comm] using member
  have entered := chain.all_entered live scope member
  exact ⟨index, frame, found, position, shape, entered, shape.height entered⟩


theorem ScopeFrameShape.branch_width {locals scope} {frame : runtime.compiler.Frame}
    (shape : ScopeFrameShape locals scope frame) :
    (match frame.kind with | .Loop => frame.params | _ => frame.results).val = slots scope.branchTypes := by
  rw [shape.kind]
  cases form : scope.form <;> simp [ScopeForm.kind, SourceScope.branchTypes, form, shape.params, shape.results]

/-- The source coordinate used by an actual branch is representable because it
is a prefix of the current checked live operand-stack layout. -/
theorem branch_source_coordinate {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    {locals target discarded arguments : List valtype}
    (layout : CompilerLayout compiler (target ++ discarded ++ arguments))
    (localTypes : compilerLocals compiler = locals) :
    ∃ source : U32, source.val = slots locals + slots (target ++ discarded) ∧
      source.val + slots arguments = compiler.height.val := by
  have height : compiler.height.val = slots locals + slots (target ++ discarded ++ arguments) := by
    simpa only [localTypes] using layout.height
  have bound := compiler.height.hBounds
  change compiler.height.val < 2^32 at bound
  have sum : slots (target ++ discarded ++ arguments) = slots (target ++ discarded) + slots arguments := slots_append _ _
  let source : U32 := UScalar.ofNatCore (slots locals + slots (target ++ discarded)) (by change slots locals + slots (target ++ discarded) < 2^32; omega)
  refine ⟨source, rfl, ?_⟩
  change slots locals + slots (target ++ discarded) + slots arguments = compiler.height.val
  omega
end Itasca.Runtime.Compiler

end

/-! ## CompilerBranchMetadata -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096

theorem compiler_branch_stable_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (depth skip : U32) (conditional : Bool)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops before depth skip conditional = .ok (status, after)) :
    CompilerStable before after := by
  have frame := (runtime.compiler.control.FunctionCompiler.branch.inv ops before after depth skip conditional status accepted).frame
  rw [frame]
  exact ⟨rfl, Nat.le_refl _⟩

end Itasca.Runtime.Compiler

end

/-! ## CloseGuardedScope -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
@[step] theorem close_guarded_scope_effect {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (frame : runtime.compiler.Frame)
    (rest : alloc.vec.Vec runtime.compiler.Frame) (target : U32)
    (frames : compiler.frames.val = rest.val ++ [frame])
    (guard : Usize) (condition old : U32)
    (nonBody : frame.kind ≠ .Body) (hasIf : frame.if_pc = some guard)
    (guardCode : compiler.function.code.val[guard.val]? = some (.JumpIfZero condition old))
    (position : target.val = compiler.function.code.val.length)
    (branches : BranchSites compiler.function.code.val frame.fixups.val)
    (mapFits : frame.map.val < compiler.function.controls.val.length)
    (coordinateFits : compiler.function.body_start.val + state.pos.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops compiler state .Block .Empty ⦃ out =>
      out.1 = .Ok () →
        out.2.frames = rest ∧ out.2.reachable = scopeExitLive compiler.reachable frame ∧
        out.2.function.code.val = patchCode (compiler.function.code.val.set guard.val (.JumpIfZero condition target)) frame.fixups.val target ∧
        ∃ closed, out.2.function.controls.val[frame.map.val]? = some closed ∧
          closed.end_pc.val = target.val ∧
          closed.source_end.val = compiler.function.body_start.val + state.pos.val ⦄ := by
  have normal := runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end.total ops law compiler state .Block .Empty
    ⟨frame, rest, frames, branches,
      (by
        intro queried selected
        have same : queried = guard := Option.some.inj (selected.symm.trans hasIf)
        subst queried
        exact ⟨.zero condition, old, guardCode⟩),
      mapFits, coordinateFits, (by intro body; exact False.elim (nonBody body))⟩
  obtain ⟨⟨status, after⟩, called, _⟩ := WP.spec_imp_exists normal
  rw [called, WP.spec_ok]
  intro successful
  dsimp only at successful ⊢
  subst status
  have effect := runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end.inv ops compiler after state .Block .Empty (.Ok ()) called
  obtain ⟨remaining, reachable, code, original, closed, selected, controls, start, sourceStart, endPc, sourceEnd⟩ :=
    effect.guarded_success law ⟨frame, rest, target, frames, position, guard, condition, old, hasIf, guardCode, branches, mapFits⟩
  have exactCode : after.function.code.val = patchCode (compiler.function.code.val.set guard.val (.JumpIfZero condition target)) frame.fixups.val target := by
    cases kindEq : frame.kind <;> first
      | exact False.elim (nonBody kindEq)
      | simpa only [kindEq, List.append_nil] using code

  have closedLookup : after.function.controls.val[frame.map.val]? = some closed := by
    rw [controls]
    exact List.getElem?_set_self mapFits
  refine ⟨remaining, reachable, ?_, closed, closedLookup, endPc, sourceEnd⟩
  exact exactCode

end Itasca.Runtime.Compiler

end

/-! ## EnterElse -/

section

/-! The actual ELSE callback preserves source control metadata, records the
then-arm skip when needed, and retargets the original condition to the start
of the else arm. Unentered and non-fallthrough arms are handled explicitly. -/
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- When the then arm does not fall through, ELSE emits no skip instruction;
it still retargets the initial conditional guard and restores entry reachability. -/
@[step] theorem compiler_else_dead {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (frame : runtime.compiler.Frame) (prior : List runtime.compiler.Frame)
    (guard : Usize) (condition target : U32)
    (frames : compiler.frames.val = prior ++ [frame])
    (reachable : compiler.reachable = false) (guardPc : frame.if_pc = some guard)
    (guardCode : compiler.function.code.val[guard.val]? = some (.JumpIfZero condition core.num.U32.MAX))
    (position : target.val = compiler.function.code.val.length) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else ops compiler state bt ⦃ out =>
      out.1 = .Ok () → out.2.reachable = frame.entry_reachable ∧
        out.2.function.code.val = compiler.function.code.val.set guard.val (.JumpIfZero condition target) ∧
        out.2.frames.val = prior ++ [{ frame with kind := .Else, if_pc := none }] ⦄ := by
  have guardSites : ∀ queried, frame.if_pc = some queried →
      ∃ branch old, compiler.function.code.val[queried.val]? = some (BranchKind.instruction branch old) := by
    intro queried selected
    have same : queried = guard := Option.some.inj (selected.symm.trans guardPc)
    subst queried
    exact ⟨.zero condition, core.num.U32.MAX, guardCode⟩
  have normal := runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else.total ops law compiler state bt frame prior frames guardSites
    (by intro live; simp only [reachable, Bool.false_eq_true] at live)
  obtain ⟨⟨status, after⟩, called, _⟩ := WP.spec_imp_exists normal
  rw [called, WP.spec_ok]
  intro successful
  dsimp only at successful
  subst status
  have effect := runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else.inv ops compiler after state bt (.Ok ()) called
  obtain ⟨reach, published, restore, finished⟩ := effect.dead_success law frame prior frames reachable
  rw [guardPc] at finished
  have code := finished.guard_success condition core.num.U32.MAX target guardCode position
  exact ⟨reach, code, published⟩

@[step] theorem compiler_else_unentered {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (frame : runtime.compiler.Frame) (prior : List runtime.compiler.Frame)
    (frames : compiler.frames.val = prior ++ [frame])
    (reachable : compiler.reachable = false) (guardPc : frame.if_pc = none) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else ops compiler state bt ⦃ out =>
      out.1 = .Ok () → out.2.reachable = frame.entry_reachable ∧
        out.2.function.code = compiler.function.code ∧
        out.2.frames.val = prior ++ [{ frame with kind := .Else, if_pc := none }] ⦄ := by
  have normal := runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else.total ops law compiler state bt frame prior frames
    (by intro guard selected; rw [guardPc] at selected; cases selected)
    (by intro live; simp only [reachable, Bool.false_eq_true] at live)
  obtain ⟨⟨status, after⟩, called, _⟩ := WP.spec_imp_exists normal
  rw [called, WP.spec_ok]
  intro successful
  dsimp only at successful
  subst status
  have effect := runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else.inv ops compiler after state bt (.Ok ()) called
  obtain ⟨reach, published, restore, finished⟩ := effect.dead_success law frame prior frames reachable
  rw [guardPc] at finished
  cases finished with
  | unguarded observed =>
    have frame := compiler_observe_frame_raw ops _ state (.Ok ()) after observed
    refine ⟨reach, ?_, published⟩
    rw [frame]
    rfl

end Itasca.Runtime.Compiler

end

/-! ## ElseSuccess -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts

set_option maxRecDepth 4096

/-- Successful ELSE emission records its skip without an external fixup-vector
capacity assumption; each append is recovered from the actual normal return. -/
theorem compiler_else_live_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (frame : runtime.compiler.Frame) (prior : List runtime.compiler.Frame)
    (guard : Usize) (condition target : U32)
    (frames : compiler.frames.val = prior ++ [frame])
    (reachable : compiler.reachable = true) (guardPc : frame.if_pc = some guard)
    (guardCode : compiler.function.code.val[guard.val]? = some (.JumpIfZero condition core.num.U32.MAX))
    (position : target.val = compiler.function.code.val.length + 1)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else ops compiler state bt = .ok (.Ok (), after)) :
    after.reachable = frame.entry_reachable ∧
    after.function.code.val = (compiler.function.code.val ++ [runtime.bytecode.Instr.Jump core.num.U32.MAX]).set guard.val
      (.JumpIfZero condition target) ∧
    ∃ fixups, fixups.val = frame.fixups.val ++ [alloc.vec.Vec.len compiler.function.code] ∧
      after.frames.val = prior ++ [{ frame with kind := .Else, if_pc := none, end_reachable := true, fixups }] := by
  exact (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else.inv ops compiler after state bt (.Ok ()) accepted).live_success
    law ⟨frame, prior, guard, condition, core.num.U32.MAX, target, frames, reachable, guardPc, guardCode, position⟩

end Itasca.Runtime.Compiler

end

/-! ## ElseTransition -/

section

/-!
Else-transition frame geometry, resolved guard prefixes and branch-site retention. The argument constructs ElseTransition from its frame-plan and fixup-site facts for callback and scope proofs.
-/

/-! ## Else Prefix -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

theorem resolved_code_guard_set (code : List Bytecode) (groups : List FixupTarget)
    (guard : Usize) (condition old target : U32)
    (found : code[guard.val]? = some (.JumpIfZero condition old)) :
    resolvedCode (code.set guard.val (.JumpIfZero condition target)) groups =
      resolvedCode code (⟨[guard], target⟩ :: groups) := by
  simp only [resolvedCode, patchCode, found, retarget]

/-- The actual ELSE update resolves its guard and appends one forward skip.
The resolved view of the completed then body is preserved as an exact prefix. -/
theorem resolved_code_else_live (code : List Bytecode) (groups : List FixupTarget)
    (fixups : List Usize) (guard site : Usize) (condition old noEntry exit : U32)
    (found : code[guard.val]? = some (.JumpIfZero condition old))
    (position : site.val = code.length)
    (inside : FixupsInside (⟨fixups, exit⟩ :: groups) code.length) :
    resolvedCode ((code ++ [runtime.bytecode.Instr.Jump core.num.U32.MAX]).set guard.val (.JumpIfZero condition noEntry))
      (⟨fixups ++ [site], exit⟩ :: groups) =
      resolvedCode code (⟨[guard], noEntry⟩ :: ⟨fixups, exit⟩ :: groups) ++ [.Jump exit] := by
  have guardBound := (List.getElem?_eq_some_iff.mp found).1
  rw [List.set_append_left guard.val _ guardBound]
  have inside' : FixupsInside ([] ++ ⟨fixups, exit⟩ :: groups)
      (code.set guard.val (.JumpIfZero condition noEntry)).length := by
    simpa using inside
  have eq := resolved_code_new_branch (code.set guard.val (.JumpIfZero condition noEntry)) [] [] groups
    ⟨fixups, exit⟩ .jump core.num.U32.MAX site (by simpa using position) inside'
  simpa only [List.append_nil, List.nil_append, BranchKind.instruction,
    resolved_code_guard_set code (⟨fixups, exit⟩ :: groups) guard condition old noEntry found] using eq

end Itasca.Runtime.Compiler

end

/-! ## Else Sites -/

section

namespace Itasca.Runtime.Compiler
open Aeneas.Std

theorem FrameSites.set_guard {code frame} (valid : FrameSites code frame)
    (guard : Usize) (condition old target : U32)
    (found : code[guard.val]? = some (.JumpIfZero condition old)) :
    FrameSites (code.set guard.val (.JumpIfZero condition target)) frame := by
  have changed := valid.patch [guard] target
  simpa [patchCode, found, retarget] using changed

theorem FrameSites.else_live {code frame} (valid : FrameSites code frame)
    (guard site : Usize) (condition old noEntry : U32) (fixups : alloc.vec.Vec Usize)
    (found : code[guard.val]? = some (.JumpIfZero condition old))
    (position : site.val = code.length) (appended : fixups.val = frame.fixups.val ++ [site]) :
    FrameSites ((code ++ [runtime.bytecode.Instr.Jump core.num.U32.MAX]).set guard.val (.JumpIfZero condition noEntry))
      {frame with kind := .Else, if_pc := none, end_reachable := true, fixups} := by
  have marked := valid.add_branch 0#u32 0#u32 0#u32 core.num.U32.MAX site fixups appended
    (by simpa using position)
  have branches : FrameSites (code ++ [runtime.bytecode.Instr.Jump core.num.U32.MAX])
      {frame with end_reachable := true, fixups} := by
    simpa [branchInstructions] using marked
  have atGuard : (code ++ [runtime.bytecode.Instr.Jump core.num.U32.MAX])[guard.val]? =
      some (.JumpIfZero condition old) := fetch_extend found _
  have patched := branches.set_guard guard condition old noEntry atGuard
  exact ⟨patched.branches, by simp⟩

theorem FrameSites.else_dead {code frame} (valid : FrameSites code frame)
    (guard : Usize) (condition old noEntry : U32)
    (found : code[guard.val]? = some (.JumpIfZero condition old)) :
    FrameSites (code.set guard.val (.JumpIfZero condition noEntry))
      {frame with kind := .Else, if_pc := none} := by
  have patched := valid.set_guard guard condition old noEntry found
  exact ⟨patched.branches, by simp⟩

end Itasca.Runtime.Compiler

end

/-! ## Frame Plan Else -/

section

namespace Itasca.Runtime.Compiler
open Aeneas.Std

/-- A future ELSE plan determines the preceding THEN plan. The completed
normal path ends before the optional skip; its guard resolves to the actual
new ELSE entry. Recorded branches remain live in the shared forward target. -/
theorem FrameFuture.before_else {afterLength beforeLength locals frame label fixups}
    (normal : Bool) (noEntry : U32)
    (future : FrameFuture afterLength locals
      {frame with kind := .Else, if_pc := none, end_reachable := frame.end_reachable || normal, fixups}
      label 0#u32)
    (kind : frame.kind = .Then)
    (order : beforeLength ≤ afterLength) (guardBound : beforeLength ≤ noEntry.val) :
    FrameFuture beforeLength locals frame
      {label with normalExit := beforeLength, cont := [], after := [], normalLive := normal} noEntry := by
  refine ⟨future.height, future.results, ?_, Nat.le_refl _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro entered
    simpa [kind] using future.branchWidth entered
  · intro _
    exact order.trans (future.forwardBound (by simp))
  · simp [kind]
  · simp [kind]
  · intro marked
    exact future.marked (by simp [marked])
  · simp [kind]
  · intro _; exact guardBound

end Itasca.Runtime.Compiler

end

/-! ## Else Transition -/

section

namespace Itasca.Runtime.Compiler
open Aeneas.Std

/-- Exact physical ELSE update, including the optional skip selected by the
completed then arm's reachability. These are source callback effects only. -/
structure ElseTransition {A : Type} (before after : runtime.compiler.FunctionCompiler A)
    (prior : List runtime.compiler.Frame) (frame : runtime.compiler.Frame)
    (guard site : Usize) (condition old noEntry : U32) (fixups : alloc.vec.Vec Usize)
    (normal : Bool) : Prop where
  beforeFrames : before.frames.val = prior ++ [frame]
  afterFrames : after.frames.val = prior ++ [{frame with kind := .Else, if_pc := none, end_reachable := frame.end_reachable || normal, fixups}]
  guardCode : before.function.code.val[guard.val]? = some (.JumpIfZero condition old)
  sitePosition : site.val = before.function.code.val.length
  noPosition : noEntry.val = before.function.code.val.length + (if normal then 1 else 0)
  fixupsEq : fixups.val = frame.fixups.val ++ (if normal then [site] else [])
  codeEq : after.function.code.val =
    (before.function.code.val ++ (if normal then [runtime.bytecode.Instr.Jump core.num.U32.MAX] else [])).set guard.val (.JumpIfZero condition noEntry)

theorem ElseTransition.length {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {prior frame guard site condition old noEntry fixups normal}
    (change : ElseTransition before after prior frame guard site condition old noEntry fixups normal) :
    after.function.code.val.length = noEntry.val := by
  rw [change.codeEq, List.length_set, List.length_append, change.noPosition]
  cases normal <;> simp

theorem ElseTransition.order {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {prior frame guard site condition old noEntry fixups normal}
    (change : ElseTransition before after prior frame guard site condition old noEntry fixups normal) :
    before.function.code.val.length ≤ after.function.code.val.length := by
  rw [change.length, change.noPosition]
  omega

theorem ElseTransition.sites {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {prior frame guard site condition old noEntry fixups normal}
    (change : ElseTransition before after prior frame guard site condition old noEntry fixups normal)
    (valid : ∀ f ∈ before.frames.val, FrameSites before.function.code.val f) :
    ∀ f ∈ after.frames.val, FrameSites after.function.code.val f := by
  intro f member
  rw [change.afterFrames] at member
  rcases List.mem_append.mp member with previous | current
  · have original := valid f (by rw [change.beforeFrames]; exact List.mem_append_left _ previous)
    rw [change.codeEq]
    exact (original.extend _).set_guard guard condition old noEntry (fetch_extend change.guardCode _)
  · simp only [List.mem_singleton] at current
    subst f
    have original := valid frame (by simp [change.beforeFrames])
    cases normal with
    | true =>
      simpa [change.codeEq] using original.else_live guard site condition old noEntry fixups
        change.guardCode change.sitePosition (by simpa using change.fixupsEq)
    | false =>
      have fixed := original.else_dead guard condition old noEntry change.guardCode
      refine ⟨?_, by simp⟩
      simpa [change.codeEq, ForwardSites, change.fixupsEq] using fixed.branches

theorem ElseTransition.resolved {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {prior frame guard site condition old noEntry fixups normal}
    (change : ElseTransition before after prior frame guard site condition old noEntry fixups normal)
    (groups : List FixupTarget) (exit : U32)
    (inside : FixupsInside (⟨frame.fixups.val, exit⟩ :: groups) before.function.code.val.length) :
    resolvedCode after.function.code.val (⟨fixups.val, exit⟩ :: groups) =
      resolvedCode before.function.code.val (⟨[guard], noEntry⟩ :: ⟨frame.fixups.val, exit⟩ :: groups) ++
        (if normal then [.Jump exit] else []) := by
  cases normal with
  | true =>
    rw [change.codeEq, change.fixupsEq]
    simpa using resolved_code_else_live _ _ _ _ _ _ _ _ _ change.guardCode change.sitePosition inside
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil] at *
    rw [change.codeEq, change.fixupsEq]
    simpa using resolved_code_guard_set _ (⟨frame.fixups.val, exit⟩ :: groups) _ _ _ noEntry change.guardCode

end Itasca.Runtime.Compiler

end

end

/-! ## ScopeStackElse -/

section

/-!
Guard extension and the source-scope frame stack at else entry. ScopeFrameStack.begin_else composes the frame-local guard facts.
-/

/-! ## Scope Frame Guard Append -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
theorem ScopeFrameShape.guard_distinct {locals scope frame}
    (shape : ScopeFrameShape locals scope frame) (guard : Usize)
    (distinct : frame.if_pc ≠ some guard) : scope.guardPosition ≠ some guard.val := by
  intro equal
  apply distinct
  have mapped := shape.guard.trans equal
  cases atGuard : frame.if_pc with
  | none => simp [atGuard] at mapped
  | some other =>
    simp only [atGuard, Option.map_some, Option.some.injEq] at mapped
    have same : other = guard := by scalar_tac
    simp [same]

/-- ELSE may first append a skip before resolving its guard. -/
theorem FrameScope.set_guard_append {A : Type} {locals} {before after : runtime.compiler.FunctionCompiler A}
    {scope frame} (shape : FrameScope locals before scope frame) (suffix : List Bytecode)
    (guard : Usize) (condition old target : U32)
    (found : before.function.code.val[guard.val]? = some (.JumpIfZero condition old))
    (distinct : frame.if_pc ≠ some guard)
    (code : after.function.code.val = (before.function.code.val ++ suffix).set guard.val (.JumpIfZero condition target))
    (maps : before.function.controls.val.length ≤ after.function.controls.val.length) :
    FrameScope locals after scope frame := by
  apply shape.transport maps
  · simp [code]
  · rw [code]
    exact (shape.entryCode.extend suffix).set_guard guard condition old target
      (fetch_extend found suffix) (shape.toScopeFrameShape.guard_distinct guard distinct)
end Itasca.Runtime.Compiler

end

/-! ## Scope Stack Else -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

theorem ScopeFrameStack.parts {A : Type} {locals parents current}
    {compiler : runtime.compiler.FunctionCompiler A} (stack : ScopeFrameStack locals compiler parents current)
    (prior : List runtime.compiler.Frame) (frame : runtime.compiler.Frame)
    (frames : compiler.frames.val = prior ++ [frame]) :
    List.Forall₂ (FrameScope locals compiler) parents prior ∧ FrameScope locals compiler current frame := by
  obtain ⟨actualPrior, actualFrame, actualFrames, paired, shape⟩ := stack.split
  have equal : actualPrior = prior ∧ actualFrame = frame := by
    simpa using actualFrames.symm.trans frames
  rcases equal with ⟨rfl, rfl⟩
  exact ⟨paired, shape⟩

theorem scope_frames_imp_member {α β : Type} {R S : α → β → Prop} {left right}
    (paired : List.Forall₂ R left right)
    (change : ∀ a b, b ∈ right → R a b → S a b) : List.Forall₂ S left right := by
  induction paired with
  | nil => exact .nil
  | @cons a b left right related rest ih =>
    exact .cons (change a b (by simp) related)
      (ih (fun a b member related => change a b (List.mem_cons_of_mem _ member) related))

/-- The exact ELSE mutation preserves every paired frame, deriving outer guard
distinctness from nesting and updating the active scope's second-arm geometry. -/
theorem ScopeFrameStack.begin_else {A : Type} {locals parents current}
    {before after : runtime.compiler.FunctionCompiler A} (stack : ScopeFrameStack locals before parents current)
    (prior : List runtime.compiler.Frame) (frame : runtime.compiler.Frame)
    (guard site : Usize) (condition old noEntry : U32) (fixups : alloc.vec.Vec Usize) (normal : Bool)
    (change : ElseTransition before after prior frame guard site condition old noEntry fixups normal)
    (bt : blocktype) (form : current.form = .then_ bt condition) (guardEq : frame.if_pc = some guard)
    (maps : before.function.controls.val.length ≤ after.function.controls.val.length) :
    ScopeFrameStack locals after parents
      (current.begin_else bt condition before.function.code.val.length noEntry normal) := by
  obtain ⟨paired, shape⟩ := stack.parts prior frame change.beforeFrames
  have distinct := stack.distinct_guard prior frame change.beforeFrames guard guardEq
  have retained : List.Forall₂ (FrameScope locals after) parents prior := by
    apply scope_frames_imp_member paired
    intro scope other member original
    exact original.set_guard_append _ guard condition old noEntry change.guardCode
      (distinct other member) change.codeEq maps
  have fresh := shape.begin_else bt condition form before.function.code.val.length noEntry normal fixups
    maps change.order (Nat.le_of_eq change.length.symm)
  apply stack.replace_current _ prior _ change.afterFrames retained fresh rfl
  change current.entry ≤ noEntry.val
  have bounded := shape.entryBound
  rw [change.noPosition]
  omega
end Itasca.Runtime.Compiler

end

end

/-! ## ScopeStackClose -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Ordinary END resolves forward branches and removes the inner physical
frame; all suspended scope entry instructions survive those fixups. -/
theorem ScopeFrameStack.close_branches {A : Type} {locals parents parent current}
    {before after : runtime.compiler.FunctionCompiler A}
    (stack : ScopeFrameStack locals before (parents ++ [parent]) current)
    (frame : runtime.compiler.Frame) (target : U32)
    (frames : before.frames.val = after.frames.val ++ [frame])
    (branches : ForwardSites before.function.code.val frame.fixups.val)
    (code : after.function.code.val = patchCode before.function.code.val frame.fixups.val target)
    (maps : before.function.controls.val.length ≤ after.function.controls.val.length) :
    ScopeFrameStack locals after parents parent := by
  apply stack.pop frame frames
  intro scope other _ shape
  exact shape.patch_branches branches target code maps

/-- END of an IF without ELSE first resolves its guard and then its branch
fixups. Nesting derives every outer-frame guard exclusion used here. -/
theorem ScopeFrameStack.close_guard {A : Type} {locals parents parent current}
    {before after : runtime.compiler.FunctionCompiler A}
    (stack : ScopeFrameStack locals before (parents ++ [parent]) current)
    (frame : runtime.compiler.Frame) (guard : Usize) (condition old target : U32)
    (frames : before.frames.val = after.frames.val ++ [frame]) (guardEq : frame.if_pc = some guard)
    (found : before.function.code.val[guard.val]? = some (.JumpIfZero condition old))
    (branches : ForwardSites before.function.code.val frame.fixups.val)
    (code : after.function.code.val = patchCode
      (before.function.code.val.set guard.val (.JumpIfZero condition target)) frame.fixups.val target)
    (maps : before.function.controls.val.length ≤ after.function.controls.val.length) :
    ScopeFrameStack locals after parents parent := by
  have distinct := stack.distinct_guard after.frames.val frame frames guard guardEq
  have patchedSites : ForwardSites
      (before.function.code.val.set guard.val (.JumpIfZero condition target)) frame.fixups.val := by
    simpa [patchCode, found, retarget] using branches.patch [guard] target
  apply stack.pop frame frames
  intro scope other member shape
  apply shape.transport maps
  · simp [code, patch_code_length]
  · rw [code]
    exact (shape.entryCode.set_guard guard condition old target found
      (shape.toScopeFrameShape.guard_distinct guard (distinct other member))).patch_branches patchedSites target

/-- A wholly dormant IF has no guard to resolve at ELSE. Its retained outer
frames are unchanged while the active source scope switches arms. -/
theorem ScopeFrameStack.begin_else_dormant {A : Type} {locals parents current}
    {before after : runtime.compiler.FunctionCompiler A} (stack : ScopeFrameStack locals before parents current)
    (prior : List runtime.compiler.Frame) (frame : runtime.compiler.Frame)
    (bt : blocktype) (condition : U32) (form : current.form = .then_ bt condition)
    (noEntry : U32) (position : noEntry.val = before.function.code.val.length)
    (beforeFrames : before.frames.val = prior ++ [frame])
    (afterFrames : after.frames.val = prior ++ [{frame with kind := .Else, if_pc := none}])
    (code : after.function.code.val = before.function.code.val)
    (maps : before.function.controls.val.length ≤ after.function.controls.val.length) :
    ScopeFrameStack locals after parents (current.begin_else bt condition noEntry.val noEntry false) := by
  obtain ⟨paired, shape⟩ := stack.parts prior frame beforeFrames
  have order : before.function.code.val.length ≤ after.function.code.val.length := by rw [code]
  have retained : List.Forall₂ (FrameScope locals after) parents prior :=
    paired.imp (fun _ _ shape => shape.transport maps order (by rw [code]; exact shape.entryCode))
  have fresh := shape.begin_else bt condition form noEntry.val noEntry false frame.fixups maps order
    (by rw [position, code])
  simp only [Bool.or_false] at fresh
  apply stack.replace_current _ prior _ afterFrames retained fresh rfl
  change current.entry ≤ noEntry.val
  rw [position]
  exact shape.entryBound
end Itasca.Runtime.Compiler

end

/-! ## CompilerCodeMonotoneControl -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts

set_option maxRecDepth 4096
theorem compiler_branch_code_mono {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (depth skip : U32) (conditional : Bool)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops before depth skip conditional = .ok (status, after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
  exact ((runtime.compiler.control.FunctionCompiler.branch.inv ops before after depth skip conditional status accepted).code_bound law).1

theorem compiler_enter_code_mono {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind)
    (blockType : Itasca.signature.BlockType)
    (accepted : runtime.compiler.control.FunctionCompiler.enter ops before state kind blockType = .ok (.Ok (), after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
  obtain ⟨prior, ctrl, signature, height, startPc, condition, source, middle,
    controls, selected, heightEq, sourceEq, operand, publish, observed⟩ :=
      (runtime.compiler.control.FunctionCompiler.enter.inv ops before after state kind blockType (.Ok ()) accepted).2.2 rfl
  have publication := publish law
  have observedFrame := compiler_observe_frame ops law middle state
  rw [observed, WP.spec_ok] at observedFrame
  change after = _ at observedFrame
  rw [observedFrame]
  change before.function.code.val.length ≤ middle.function.code.val.length
  rw [publication.code, List.length_append]
  omega


theorem compiler_end_code_mono {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind)
    (blockType : Itasca.signature.BlockType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end
      ops before state kind blockType = .ok (.Ok (), after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
  have effect := runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end.inv ops before after state kind blockType (.Ok ()) accepted
  obtain ⟨frame, remaining, popped, frames, length, sources⟩ := effect.sources_frames law
  omega

theorem compiler_else_code_mono {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (blockType : Itasca.signature.BlockType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else
      ops before state blockType = .ok (.Ok (), after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
  have effect := runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else.inv ops before after state blockType (.Ok ()) accepted
  cases effect with
  | selected nonempty subtracted read progress =>
    obtain ⟨fixups, appended, frames, reachable, length, sources, cursor⟩ := progress.success_fields law
    omega

end Itasca.Runtime.Compiler

end
