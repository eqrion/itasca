import Exec.Code.Local.Callbacks.Control.ElseSites
import Exec.Code.Local.Callbacks.Control.FramePlanElse
namespace Itasca.Runtime.Code
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
    simpa using resolvedCode_else_live _ _ _ _ _ _ _ _ _ change.guardCode change.sitePosition inside
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil] at *
    rw [change.codeEq, change.fixupsEq]
    simpa using resolvedCode_guard_set _ (⟨frame.fixups.val, exit⟩ :: groups) _ _ _ noEntry change.guardCode

end Itasca.Runtime.Code
