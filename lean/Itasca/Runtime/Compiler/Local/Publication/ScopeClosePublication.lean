import Itasca.Runtime.Compiler.Local.Callbacks.Control.CloseMapEffect
import Itasca.Runtime.Compiler.Local.Publication.ControlMapPublication
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CompilerCodeMonotoneControl
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlCursor
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerCloseMetadata
import Itasca.Runtime.Compiler.Local.Coordinates.ControlSourceCoordinates

/-!
Publication of closed scope maps, from guarded/unguarded map effects to the scope geometry theorem. ScopeCloseGeometry and ScopeCloseMode retain the concrete close case.
-/

/-! ## Close Guarded Map Effect -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std
/-- Exact control-map vector update for a scope with a pending conditional branch. -/
theorem close_guarded_map_effect {A : Type} (ops : runtime.platform.Alloc A)
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
        out.2.frames = rest ∧
        out.2.function.code.val = patchCode (compiler.function.code.val.set guard.val (.JumpIfZero condition target)) frame.fixups.val target ∧
        ∃ original closed, compiler.function.controls.val[frame.map.val]? = some original ∧
          out.2.function.controls.val = compiler.function.controls.val.set frame.map.val closed ∧
          closed.start_pc = original.start_pc ∧ closed.source_start = original.source_start ∧
          closed.end_pc.val = target.val ∧
          closed.source_end.val = compiler.function.body_start.val + state.pos.val ⦄ := by
  have pop : alloc.vec.Vec.pop Global compiler.frames = .ok (some frame, rest) := by
    simp only [alloc.vec.Vec.pop, frames, List.getLast?_concat, List.dropLast_concat]
    congr 2
    apply alloc.vec.Vec.ext
    simp
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end
  have popSpec : alloc.vec.Vec.pop Global compiler.frames ⦃ out => out = (some frame, rest) ⦄ := by
    rw [pop]
    simp [WP.spec_ok]
  step with popSpec as ⟨o, remaining, ho, hremaining⟩
  subst o remaining
  simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  rw [compiler_pc_eq ops { compiler with frames := rest } target position]
  simp only [bind_ok, hasIf]
  step with compiler_patch ops { compiler with frames := rest } guard (.zero condition) old target guardCode as
    ⟨status, patched, statusEq, patchedEffect⟩
  subst status
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  have patchedBranches := patchedEffect.branch_sites (List.getElem?_eq_some_iff.mp guardCode).1 branches
  obtain ⟨patchedCode, rfl, codeSet⟩ := patchedEffect
  step with compiler_fixups_after_if ops _ frame.fixups target 0#usize
    (by simp) patchedBranches as ⟨s, params, budget, batch, func, frames', reach, source, before,
      height, offsets, depths, result, after, hsnapshot, onlyCode, effect⟩
  simp only [compilerSnapshot, Prod.mk.injEq] at hsnapshot
  rcases hsnapshot with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨code, rfl⟩ := onlyCode
  simp only [bind_ok]
  step as ⟨map, back, hmap, hback⟩
  step as ⟨pcword, hpcword⟩
  step as ⟨coordinate, hcoordinate⟩
  have choice : (if compiler.reachable then .ok (frame.kind, true)
      else if frame.end_reachable then .ok (frame.kind, true)
      else Aeneas.Std.bind (match frame.kind with
          | .Body | .Block | .Loop => (.ok false : Result Bool)
          | .Then => .ok true
          | .Else => .ok false) (fun thenLabel =>
        Aeneas.Std.bind (if thenLabel then .ok frame.entry_reachable else .ok false)
          (fun entered => .ok (frame.kind, entered)))) = .ok (frame.kind, scopeExitLive compiler.reachable frame) := by
    cases kind : frame.kind <;> cases reach : compiler.reachable <;> cases ends : frame.end_reachable <;>
      simp [scopeExitLive, kind, reach, ends, bind_ok]
  change WP.spec (Aeneas.Std.bind (if compiler.reachable then .ok (frame.kind, true)
      else if frame.end_reachable then .ok (frame.kind, true)
      else Aeneas.Std.bind (match frame.kind with
          | .Body | .Block | .Loop => (.ok false : Result Bool)
          | .Then => .ok true
          | .Else => .ok false) (fun thenLabel =>
        Aeneas.Std.bind (if thenLabel then .ok frame.entry_reachable else .ok false)
          (fun entered => .ok (frame.kind, entered)))) _) _
  rw [choice, bind_ok]
  have notBody : (match frame.kind with
      | .Body => (.ok true : Result Bool)
      | .Block | .Loop | .Then | .Else => .ok false) = .ok false := by
    cases kind : frame.kind <;> simp_all
  change WP.spec (Aeneas.Std.bind (match frame.kind with
    | .Body => (.ok true : Result Bool)
    | .Block | .Loop | .Then | .Else => .ok false) _) _
  rw [notBody, bind_ok]
  simp only [Bool.false_eq_true, ite_false]
  step with compiler_observe ops law _ state as ⟨out, hout, success⟩
  obtain ⟨hoff, hh, hl, hls, hlo, hr, hcode, hsources, hnext, hcap, hmono, hframes, hcontrols⟩ := hout success
  refine ⟨hframes, ?_, map, { map with source_end := coordinate, end_pc := pcword }, ?_, ?_, rfl, rfl, ?_, hcoordinate⟩
  · simpa [hcode, codeSet, BranchKind.instruction] using effect
  · simp [List.getElem?_eq_getElem mapFits, hmap]
  · rw [hcontrols, hback]
    simp [alloc.vec.Vec.set_val_eq]
  · rw [hpcword]
    scalar_tac

end Itasca.Runtime.Code

end

/-! ## Control Map Close Effect -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Exact scope-close effects establish the invariant for the remaining
owners, using only reader progress and the independently bounded body extent. -/
theorem ControlMapPublication.close_effect {A : Type}
    {before after : runtime.compiler.FunctionCompiler A}
    (held : ControlMapPublication before) (stable : CompilerStable before after)
    (frame : runtime.compiler.Frame) (rest : alloc.vec.Vec runtime.compiler.Frame)
    (frames : before.frames.val = rest.val ++ [frame]) (remaining : after.frames = rest)
    (entry closed : runtime.compiler.ControlMap)
    (found : before.function.controls.val[frame.map.val]? = some entry)
    (controls : after.function.controls.val = before.function.controls.val.set frame.map.val closed)
    (startPc : closed.start_pc = entry.start_pc) (startSource : closed.source_start = entry.source_start)
    (position : closed.end_pc.val = before.function.code.length)
    (endSource : closed.source_end.val = before.function.body_start.val+positionSource)
    (progress : before.next_source.val < positionSource)
    (endBound : before.function.body_start.val+positionSource ≤ before.function.body_end.val)
    (code : before.function.code.length ≤ after.function.code.length)
    (cursor : before.next_source.val ≤ after.next_source.val) : ControlMapPublication after := by
  have bounded := (held.entries frame.map.val entry found).close_fields startPc startSource
    position endSource progress endBound
  apply held.close stable frame.map.val entry closed (rest.val.map (fun frame => frame.map.val))
    found controls _ _ startSource bounded code cursor
  · simp [activeControlMaps,frames]
  · simp [activeControlMaps,remaining]

end Itasca.Runtime.Code

end

/-! ## Close Map Publication -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- An actual unguarded END retains control-map publication bounds. -/
theorem compiler_unguarded_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (frame : runtime.compiler.Frame)
    (rest : alloc.vec.Vec runtime.compiler.Frame) (target : U32)
    (held : ControlMapPublication before)
    (frames : before.frames.val = rest.val ++ [frame])
    (noIf : frame.if_pc = none)
    (position : target.val = before.function.code.val.length)
    (branches : BranchSites before.function.code.val frame.fixups.val)
    (mapFits : frame.map.val < before.function.controls.val.length)
    (coordinateFits : before.function.body_start.val+state.pos.val ≤ Usize.max)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (emitCoordinateFits : before.function.body_start.val+before.next_source.val ≤ Usize.max)
    (progress : before.next_source.val < state.pos.val)
    (endBound : before.function.body_start.val+state.pos.val ≤ before.function.body_end.val)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end
      ops before state .Block .Empty = .ok (.Ok (),after)) :
    ControlMapPublication after := by
  have effect := close_unguarded_map_effect ops law before state frame rest target frames noIf
    position branches mapFits coordinateFits codeFits sourceFits emitCoordinateFits
  rw [called,WP.spec_ok] at effect
  obtain ⟨remaining,_,entry,closed,found,controls,startPc,startSource,endPc,endSource⟩ := effect rfl
  have cursor := compiler_end_cursor ops law before after state .Block .Empty called
  apply held.close_effect (compiler_end_stable_result ops law before after state .Block .Empty (.Ok ()) called)
    frame rest frames remaining entry closed found controls startPc startSource (endPc.trans position)
    endSource progress endBound (compiler_end_code_mono ops law before after state .Block .Empty called)
  rw [cursor]
  omega

/-- An actual guarded END retains control-map publication bounds. -/
theorem compiler_guarded_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (frame : runtime.compiler.Frame)
    (rest : alloc.vec.Vec runtime.compiler.Frame) (target : U32)
    (held : ControlMapPublication before)
    (frames : before.frames.val = rest.val ++ [frame])
    (guard : Usize) (condition old : U32)
    (nonBody : frame.kind ≠ .Body) (hasIf : frame.if_pc = some guard)
    (guardCode : before.function.code.val[guard.val]? = some (.JumpIfZero condition old))
    (position : target.val = before.function.code.val.length)
    (branches : BranchSites before.function.code.val frame.fixups.val)
    (mapFits : frame.map.val < before.function.controls.val.length)
    (coordinateFits : before.function.body_start.val+state.pos.val ≤ Usize.max)
    (progress : before.next_source.val < state.pos.val)
    (endBound : before.function.body_start.val+state.pos.val ≤ before.function.body_end.val)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end
      ops before state .Block .Empty = .ok (.Ok (),after)) :
    ControlMapPublication after := by
  have effect := close_guarded_map_effect ops law before state frame rest target frames guard condition old
    nonBody hasIf guardCode position branches mapFits coordinateFits
  rw [called,WP.spec_ok] at effect
  obtain ⟨remaining,_,entry,closed,found,controls,startPc,startSource,endPc,endSource⟩ := effect rfl
  have cursor := compiler_end_cursor ops law before after state .Block .Empty called
  apply held.close_effect (compiler_end_stable_result ops law before after state .Block .Empty (.Ok ()) called)
    frame rest frames remaining entry closed found controls startPc startSource (endPc.trans position)
    endSource progress endBound (compiler_end_code_mono ops law before after state .Block .Empty called)
  rw [cursor]
  omega

end Itasca.Runtime.Code

end

/-! ## Scope Close Publication -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Closing geometry comes from the current physical scope and its branch
sites, independently of any completed publication certificate. -/
structure ScopeCloseGeometry {A : Type} (before : runtime.compiler.FunctionCompiler A) where
  frame : runtime.compiler.Frame
  rest : alloc.vec.Vec runtime.compiler.Frame
  target : U32
  frames : before.frames.val = rest.val ++ [frame]
  position : target.val = before.function.code.val.length
  branches : BranchSites before.function.code.val frame.fixups.val

/-- A conditional frame patches its pending guard; other closes require only
room for the root epilogue when the closing frame is the function body. -/
inductive ScopeCloseMode {A : Type} {before : runtime.compiler.FunctionCompiler A}
    (geometry : ScopeCloseGeometry before) : Prop where
  | unguarded (noIf : geometry.frame.if_pc = none)
      (codeFits : before.function.code.val.length < Usize.max)
      (sourceFits : before.function.source_offsets.val.length < Usize.max)
      (emitCoordinateFits : before.function.body_start.val+before.next_source.val ≤ Usize.max) :
      ScopeCloseMode geometry
  | guarded (guard : Usize) (condition old : U32)
      (nonBody : geometry.frame.kind ≠ .Body) (hasIf : geometry.frame.if_pc = some guard)
      (guardCode : before.function.code.val[guard.val]? = some (.JumpIfZero condition old)) :
      ScopeCloseMode geometry

/-- The actual END event retains both invariants. The map index is bounded by
its active owner, and reader progress supplies the positive source interval. -/
theorem compiler_scope_close_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind) (bt : Itasca.signature.BlockType)
    (geometry : ScopeCloseGeometry before) (mode : ScopeCloseMode geometry)
    (coordinates : SourceCoordinates before) (maps : ControlMapPublication before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (progress : before.next_source.val < state.pos.val)
    (endBound : before.function.body_start.val+state.pos.val ≤ before.function.body_end.val)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state kind bt = .ok (.Ok (),after)) :
    SourceCoordinates after ∧ ControlMapPublication after := by
  refine ⟨compiler_end_source_coordinates ops law before after state kind bt coordinates inside (by omega) called,?_⟩
  have mapFits : geometry.frame.map.val < before.function.controls.val.length := by
    apply maps.owners
    simp [activeControlMaps,geometry.frames]
  have coordinateFits : before.function.body_start.val+state.pos.val ≤ Usize.max := by
    have bound : before.function.body_end.val ≤ Usize.max := by scalar_tac
    omega
  have canonical : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state .Block .Empty =
      .ok (.Ok (),after) := called
  cases mode with
  | unguarded noIf codeFits sourceFits emitCoordinateFits =>
    exact compiler_unguarded_map_publication ops law before after state geometry.frame geometry.rest geometry.target
      maps geometry.frames noIf geometry.position geometry.branches mapFits coordinateFits codeFits sourceFits emitCoordinateFits
      progress endBound canonical
  | guarded guard condition old nonBody hasIf guardCode =>
    exact compiler_guarded_map_publication ops law before after state geometry.frame geometry.rest geometry.target
      maps geometry.frames guard condition old nonBody hasIf guardCode geometry.position geometry.branches mapFits coordinateFits
      progress endBound canonical

end Itasca.Runtime.Code

end
