import Itasca.Runtime.Compiler.Local.Callbacks.Control.EnterElse
import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.OpenPrefix
import Itasca.Runtime.Compiler.Local.Relations.Prefix.Prefix
import Itasca.Runtime.Compiler.Local.Control.Control.UniversalBranch
import Itasca.Runtime.Compiler.Local.Relations.Prefix.FutureFrames

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
