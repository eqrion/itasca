import Exec.Code.Local.Relations.Table.BranchTableFrames
import Exec.Code.Local.Relations.Table.BranchTableCallbackProduction
import Exec.Code.Local.Relations.Table.BranchTableSites
import Exec.Code.Local.Relations.Common.DormantFrames
namespace Exec.Code
open Aeneas Aeneas.Std

private theorem frame_maps_set (frames : List runtime.compiler.Frame) (index : Nat)
    (frame : runtime.compiler.Frame) (fixups : alloc.vec.Vec Usize)
    (lookup : frames[index]? = some frame) :
    (frames.set index {frame with end_reachable := true, fixups}).map (fun f => f.map) =
      frames.map (fun f => f.map) := by
  induction frames generalizing index with
  | nil => simp at lookup
  | cons head tail ih =>
    cases index with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at lookup
              subst frame
              rfl
    | succ index => simpa using ih index lookup

theorem TableTargetCode.frame_maps {A : Type}
    {before after : runtime.compiler.FunctionCompiler A} {depth : U32}
    (effect : TableTargetCode before after depth) :
    after.frames.val.map (fun f => f.map) = before.frames.val.map (fun f => f.map) := by
  cases effect with
  | loop index frame source lookup position kind operands code frames => rw [frames]
  | forward index frame source fixups site lookup position kind operands code frames appended sitePosition =>
    rw [frames]
    exact frame_maps_set _ _ frame fixups lookup

theorem TableTargetsBuilt.frame_maps {A : Type}
    {before after : runtime.compiler.FunctionCompiler A} {depths targets : List U32}
    (built : TableTargetsBuilt before after depths targets) :
    after.frames.val.map (fun f => f.map) = before.frames.val.map (fun f => f.map) := by
  induction built with
  | nil => rfl
  | cons _ _ _ _ _ _ effect rest ih => exact ih.trans effect.frame_maps

private theorem frame_scopes_of_shapes {A : Type}
    {before after : runtime.compiler.FunctionCompiler A} {locals scopes oldFrames newFrames}
    (old : List.Forall₂ (FrameScope locals before) scopes oldFrames)
    (shapes : List.Forall₂ (ScopeFrameShape locals) scopes newFrames)
    (maps : newFrames.map (fun f => f.map) = oldFrames.map (fun f => f.map))
    (suffix : List Bytecode) (code : after.function.code.val = before.function.code.val ++ suffix)
    (controls : before.function.controls.val.length ≤ after.function.controls.val.length) :
    List.Forall₂ (FrameScope locals after) scopes newFrames := by
  induction old generalizing newFrames with
  | nil => cases shapes; exact .nil
  | @cons scope frame scopes frames prior rest ih =>
    cases shapes with
    | @cons _ next _ nextFrames shape shapes =>
      simp only [List.map_cons, List.cons.injEq] at maps
      have extended := prior.extend suffix code controls
      refine .cons ⟨shape, ?_, extended.entryBound, extended.bodyBound, extended.entryCode⟩ (ih shapes maps.2)
      simpa only [maps.1] using extended.mapBound

/-- The complete live callback preserves all physical/source scope geometry,
entry code and clean dormant frames before the source zipper advances once. -/
theorem compiler_br_table_scope_frames {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (fallback : U32) (types : Itasca.signature.ResultType)
    {locals parents current} (prior : ScopeFrameStack locals before parents current)
    (chain : SourceEntryChain parents current) (entered : current.entered = true)
    (sites : ∀ frame ∈ before.frames.val, FrameSites before.function.code.val frame)
    (controls : before.function.controls.val.length ≤ after.function.controls.val.length)
    (live : before.reachable = true)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
      ops before state fallback types = .ok (.Ok (),after)) :
    ScopeFrameStack locals after parents current ∧ DormantFrames after.frames.val ∧
      (∀ frame ∈ after.frames.val, FrameSites after.function.code.val frame) := by
  obtain ⟨budget, depths, start, len, selector, emitted, lowered, targets,
    depthsEq, startEq, lenEq, emission, built, codeEq, framesEq, tables, count, cleared, dead, header⟩ :=
    compiler_br_table_production ops law before after state fallback types live accepted
  obtain ⟨emitBudget, code, sources, emittedEq, emittedCode, emittedSources⟩ := emission
  have emittedFrames : emitted.frames = before.frames := by rw [emittedEq]
  have emittedCodeEq : emitted.function.code.val = before.function.code.val ++ [.JumpTable selector start len] := by
    rw [emittedEq]; exact emittedCode
  obtain ⟨suffix, loweredCode, _⟩ := built.code_prefix
  have wholeCode : after.function.code.val = before.function.code.val ++ (.JumpTable selector start len :: suffix) := by
    rw [codeEq, loweredCode, emittedCodeEq]
    simp only [List.append_assoc, List.singleton_append]
  have shapes : List.Forall₂ (ScopeFrameShape locals) (parents ++ [current]) after.frames.val := by
    rw [framesEq]
    apply built.scope_shapes locals _
    simpa only [emittedFrames] using prior.frames.imp (fun _ _ p => p.toScopeFrameShape)
  have maps : after.frames.val.map (fun f => f.map) = before.frames.val.map (fun f => f.map) := by
    rw [framesEq, built.frame_maps, emittedFrames]
  have frames : ScopeFrameStack locals after parents current :=
    ⟨prior.nested, frame_scopes_of_shapes prior.frames shapes maps _ wholeCode controls⟩
  refine ⟨frames, ?_, ?_⟩
  · intro frame member
    exact DormantFrame.entered (frames.frame_entered chain entered frame member)
  · have emittedSites : ∀ frame ∈ emitted.frames.val, FrameSites emitted.function.code.val frame := by
      intro frame member
      rw [emittedFrames] at member
      simpa only [emittedCodeEq] using (sites frame member).extend [.JumpTable selector start len]
    simpa only [codeEq, framesEq] using built.frame_sites emittedSites
end Exec.Code
