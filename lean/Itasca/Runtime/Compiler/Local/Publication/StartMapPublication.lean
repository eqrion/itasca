import Itasca.Runtime.Compiler.Local.Callbacks.Function.FinishContracts
import Itasca.Runtime.Compiler.Local.Lowering.Control.BranchEffects
import Itasca.Runtime.Compiler.Local.Callbacks.Control.BranchCallbacks
import Itasca.Runtime.Compiler.Local.Callbacks.Control.EndContracts
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ElseContracts
import Itasca.Runtime.Compiler.Local.Lowering.Control.UnreachableContracts
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CloseMapEffect
import Itasca.Runtime.Compiler.Local.Publication.ScopeEntryPublication
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CompilerCodeMonotoneControl
import Itasca.Runtime.Compiler.Local.Relations.Control.BranchCertificates
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerTerminalMetadata
import Itasca.Runtime.Compiler.Local.Coordinates.ControlSourceCoordinates
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlObservedLayout
import Itasca.Runtime.Compiler.Local.Callbacks.CodeGrowth.CompilerCodeMonotoneLiteral
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulLowered
import Itasca.Runtime.Compiler.Local.Lowering.Literal.LiteralSources
import Itasca.Runtime.Compiler.Local.Relations.Calls.IndirectCallMetadata
import Itasca.Runtime.Compiler.Local.Callbacks.Simd.CompilerTableScratchSimd
import Itasca.Runtime.Compiler.Local.Lowering.Simd.SimdEffects
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CompilerCodeMonotoneCallbacks
import Itasca.Runtime.Compiler.Local.Relations.Instructions.WellFormedAcceptance
import Itasca.Runtime.Compiler.Local.Callbacks.Function.EnterDead
import Itasca.Runtime.Compiler.Local.Relations.Function.FunctionEnvironment

/-!
Sections, each formerly its own module: ScopeClosePublication, FinalControlMapBounds, RootMapPublication, BranchMapOwners, BranchMapPublication, LoweringMapPublication, LiteralMapPublication, CallbackMapPublication, ElseMapPublication, FunctionPublicationRanges, FunctionPublicationHeader, StartMapPublication.
-/

/-! ## ScopeClosePublication -/

section

/-!
Publication of closed scope maps, from guarded/unguarded map effects to the scope geometry theorem. ScopeCloseGeometry and ScopeCloseMode retain the concrete close case.
-/

/-! ## Close Guarded Map Effect -/

section

namespace Itasca.Runtime.Compiler
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

  exact ⟨remaining, exactCode, original, closed, selected, controls, start, sourceStart, endPc, sourceEnd⟩

end Itasca.Runtime.Compiler

end

/-! ## Control Map Close Effect -/

section

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end

/-! ## Close Map Publication -/

section

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end

/-! ## Scope Close Publication -/

section

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end

end

/-! ## FinalControlMapBounds -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Exact control-map ranges required by the final publication checker. Unlike
intermediate closed-map bounds, every target is strictly inside final code. -/
def FinalControlMapBounds (function : runtime.bytecode.CompiledFunction) : Prop :=
  ∀ entry ∈ function.controls.val,
    entry.start_pc.val ≤ entry.end_pc.val ∧ entry.end_pc.val < function.code.length ∧
    function.body_start.val ≤ entry.source_start.val ∧ entry.source_end.val ≤ function.body_end.val ∧
    entry.source_start.val < entry.source_end.val

end Itasca.Runtime.Compiler

end

/-! ## RootMapPublication -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- The actual final END callback establishes every control-map range checked
at publication. Its return instruction puts all closing targets inside code. -/
theorem compiler_root_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (frame : runtime.compiler.Frame)
    (rest : alloc.vec.Vec runtime.compiler.Frame) (target : U32)
    (held : ControlMapPublication before)
    (frames : before.frames.val = rest.val ++ [frame]) (empty : rest.val = [])
    (root : frame.kind = .Body) (noIf : frame.if_pc = none)
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
    ∀ map ∈ after.function.controls.val,
      map.start_pc.val ≤ map.end_pc.val ∧ map.end_pc.val < after.function.code.length ∧
      after.function.body_start.val ≤ map.source_start.val ∧ map.source_end.val ≤ after.function.body_end.val ∧
      map.source_start.val < map.source_end.val := by
  have effect := close_unguarded_map_effect ops law before state frame rest target frames noIf
    position branches mapFits coordinateFits codeFits sourceFits emitCoordinateFits
  rw [called,WP.spec_ok] at effect
  obtain ⟨_,code,entry,closed,found,controls,startPc,startSource,endPc,endSource⟩ := effect rfl
  have bounded := (held.entries frame.map.val entry found).close_fields startPc startSource
    (endPc.trans position) endSource progress endBound
  have growth : before.function.code.length < after.function.code.length := by
    change before.function.code.val.length < after.function.code.val.length
    rw [code]
    simp only [List.length_append,patch_code_length,closeMapEpilogue,root,List.length_singleton]
    omega
  have owners : activeControlMaps before = [frame.map.val] := by
    simp [activeControlMaps,frames,empty]
  exact held.close_last_publish (compiler_end_stable_result ops law before after state .Block .Empty (.Ok ()) called)
    frame.map.val entry closed found controls owners bounded growth

end Itasca.Runtime.Compiler

end

/-! ## BranchMapOwners -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096

private theorem frame_owner_restore (vector : alloc.vec.Vec runtime.compiler.Frame) (index : Usize)
    (value : runtime.compiler.Frame) (restore : runtime.compiler.Frame → alloc.vec.Vec runtime.compiler.Frame)
    (accepted : alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice runtime.compiler.Frame)
      vector index = .ok (value,restore)) :
    ∀ replacement, replacement.map = value.map →
      (restore replacement).val.map (fun frame => frame.map.val) = vector.val.map (fun frame => frame.map.val) := by
  rw [alloc.vec.Vec.index_mut_slice_index] at accepted
  unfold alloc.vec.Vec.index_mut_usize at accepted
  obtain ⟨selected,read,accepted⟩ := bind_ok_inv _ _ _ accepted
  have selectedEq := (Prod.mk.inj (Result.ok.injEq.mp accepted)).1
  have restoreEq := (Prod.mk.inj (Result.ok.injEq.mp accepted)).2
  subst selected
  unfold alloc.vec.Vec.index_usize at read
  split at read
  · simp at read
  next found lookup =>
    have same : found = value := Result.ok.injEq.mp read
    subst found
    have bound := (List.getElem?_eq_some_iff.mp lookup).1
    have atIndex := (List.getElem?_eq_some_iff.mp lookup).2
    intro replacement owner
    rw [← restoreEq,alloc.vec.Vec.set_val_eq,List.map_set,owner,← atIndex]
    have mapped : (vector.val.map (fun frame => frame.map.val))[index.val]'(by simpa using bound) = vector.val[index.val].map.val := by
      rw [List.getElem_map]
    rw [← mapped]
    exact List.set_getElem_self (by simpa using bound)

theorem BranchPatch.map_owners {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {guard status}
    (effect : BranchPatch ops before after guard status) : activeControlMaps after = activeControlMaps before := by
  cases guard with
  | none => rw [effect.2]
  | some site =>
    obtain ⟨answer, middle, called, rest⟩ := effect
    have pc := compiler_pc ops before
    rw [called, WP.spec_ok] at pc
    obtain ⟨budget, same⟩ := pc.2.2
    change middle = {before with budget} at same
    cases answer with
    | Err error => rw [rest.2, same]; rfl
    | Ok target =>
      rcases compiler_patch_cases ops middle after site target status rest with unchanged | ⟨instruction, code, frame, contents⟩
      · rw [unchanged, same]; rfl
      · rw [frame, same]; rfl

theorem BranchJumpCall.map_owners {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {instruction guard status}
    (effect : BranchJumpCall ops before after instruction guard status) : activeControlMaps after = activeControlMaps before := by
  obtain ⟨answer, middle, called, rest⟩ := effect
  have frame := (runtime.compiler.FunctionCompiler.emit.inv ops before middle instruction answer called).1
  have head : activeControlMaps middle = activeControlMaps before := by rw [frame]; rfl
  cases answer with
  | Err error => rw [rest.2]; exact head
  | Ok value => exact rest.map_owners.trans head

theorem BranchPublication.map_owners {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {index conditional copying condition guard status}
    (effect : BranchPublication ops before after index conditional copying condition guard status) : activeControlMaps after = activeControlMaps before := by
  obtain ⟨frame, restore, read, rest⟩ := effect
  have restored := frame_owner_restore _ _ _ _ read
  split at rest
  · exact rest.map_owners.trans (restored frame rfl)
  · obtain ⟨answer, budget, fixups, _, rest⟩ := rest
    cases answer with
    | Err error => rw [rest.2]; exact restored _ rfl
    | Ok value => exact rest.map_owners.trans (restored _ rfl)

theorem BranchCopy.map_owners {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {index dst src count conditional copying condition guard status}
    (effect : BranchCopy ops before after index dst src count conditional copying condition guard status) : activeControlMaps after = activeControlMaps before := by
  unfold BranchCopy at effect
  split at effect
  · obtain ⟨answer, middle, called, rest⟩ := effect
    have frame := (runtime.compiler.FunctionCompiler.copy.inv ops before middle dst src count answer called).frame
    have head : activeControlMaps middle = activeControlMaps before := by rw [frame]; rfl
    cases answer with
    | Err error => rw [rest.2]; exact head
    | Ok value => exact rest.map_owners.trans head
  · exact effect.map_owners

theorem BranchTransfer.map_owners {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {index dst src count conditional condition status}
    (effect : BranchTransfer ops before after index dst src count conditional condition status) : activeControlMaps after = activeControlMaps before := by
  dsimp only [BranchTransfer] at effect
  split at effect
  · obtain ⟨answer, middle, called, rest⟩ := effect
    have frame := (runtime.compiler.FunctionCompiler.emit.inv ops before middle _ answer called).1
    have head : activeControlMaps middle = activeControlMaps before := by rw [frame]; rfl
    cases answer with
    | Err error => rw [rest.2]; exact head
    | Ok value => exact rest.map_owners.trans head
  · exact effect.map_owners

theorem BranchCondition.map_owners {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {index dst src count conditional status}
    (effect : BranchCondition ops before after index dst src count conditional status) : activeControlMaps after = activeControlMaps before := by
  unfold BranchCondition at effect
  split at effect
  · obtain ⟨answer, _, rest⟩ := effect
    cases answer with
    | Err error => rw [rest.2]
    | Ok value => exact rest.map_owners
  · exact effect.map_owners

theorem BranchSource.map_owners {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {index frame skip conditional status}
    (effect : BranchSource ops before after index frame skip conditional status) : activeControlMaps after = activeControlMaps before := by
  obtain ⟨sum, _, rest⟩ := effect
  cases sum with
  | none => rw [rest.2]
  | some width =>
    obtain ⟨source, _, rest⟩ := rest
    cases source with
    | none => rw [rest.2]
    | some src => exact rest.map_owners

theorem BranchEffect.map_owners {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {depth skip conditional status}
    (effect : BranchEffect ops before after depth skip conditional status) : activeControlMaps after = activeControlMaps before := by
  obtain ⟨_, _, _, _, _, _, _, _, rest⟩ := effect
  exact rest.map_owners

/-- Branches change frame flags and fixups while retaining each map owner. -/
theorem compiler_branch_map_owners {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (depth skip : U32) (conditional : Bool)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops before depth skip conditional = .ok (status,after)) :
    activeControlMaps after = activeControlMaps before := by
  exact (runtime.compiler.control.FunctionCompiler.branch.inv ops before after depth skip conditional status accepted).map_owners

end Itasca.Runtime.Compiler

end

/-! ## BranchMapPublication -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Actual branch emission preserves every control-map publication bound;
frame fixups and end-reachability updates retain their owning map indices. -/
theorem compiler_branch_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (depth skip : U32) (conditional : Bool) (held : ControlMapPublication before)
    (called : runtime.compiler.control.FunctionCompiler.branch ops before depth skip conditional = .ok (.Ok (),after)) :
    ControlMapPublication after := by
  apply held.retained (compiler_branch_stable_result ops law before after depth skip conditional (.Ok ()) called)
    (compiler_branch_controls_result ops law before after depth skip conditional (.Ok ()) called)
    (compiler_branch_map_owners ops law before after depth skip conditional (.Ok ()) called)
    (compiler_branch_code_mono ops law before after depth skip conditional (.Ok ()) called)
  rw [compiler_branch_cursor ops law before after depth skip conditional called]

end Itasca.Runtime.Compiler

end

/-! ## LoweringMapPublication -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Actual numeric lowering preserves all control-map bounds. -/
theorem compiler_numeric_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (op : SourceMachine.Numeric.Instruction)
    (called : runtime.compiler.lower.FunctionCompiler.op ops before state (integerOpcode op) 0#u32 0#u32 0#u128 = .ok (.Ok (), after))
    (held : ControlMapPublication before) (forward : before.next_source.val ≤ state.pos.val) :
    ControlMapPublication after := by
  apply held.ordinary (compiler_numeric_ordinary_result ops law before after state op (.Ok ()) called)
    (compiler_numeric_code_mono ops law before after state op called)
  rw [compiler_numeric_cursor ops law before after state op called]
  exact forward

/-- Actual float lowering preserves all control-map bounds. -/
theorem compiler_float_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (op : SourceMachine.Float.Instruction)
    (called : runtime.compiler.lower.FunctionCompiler.op ops before state (floatOpcode op) 0#u32 0#u32 0#u128 = .ok (.Ok (), after))
    (held : ControlMapPublication before) (forward : before.next_source.val ≤ state.pos.val) :
    ControlMapPublication after := by
  apply held.ordinary (compiler_float_ordinary_result ops law before after state op (.Ok ()) called)
    (compiler_float_code_mono ops law before after state op called)
  rw [compiler_float_cursor ops law before after state op called]
  exact forward

/-- Actual core lowering preserves all control-map bounds. -/
theorem compiler_core_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (op : CoreOperation)
    (called : runtime.compiler.lower.FunctionCompiler.op ops before state op.opcode op.first op.second 0#u128 = .ok ((.Ok ()), after))
    (held : ControlMapPublication before) (forward : before.next_source.val ≤ state.pos.val) :
    ControlMapPublication after := by
  apply held.ordinary (compiler_core_ordinary_result ops law before after state op (.Ok ()) called)
    (compiler_core_code_mono ops law before after state op called)
  rw [compiler_core_cursor ops law before after state op called]
  exact forward

end Itasca.Runtime.Compiler

end

/-! ## LiteralMapPublication -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- SIMD dispatch retains map bounds in live and dead code. -/
theorem compiler_lower_simd_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (opcode : U16) (a b : U32) (bits : U128)
    (lower : 512 ≤ opcode.val) (upper : opcode.val < 768)
    (called : runtime.compiler.lower.FunctionCompiler.op ops before state opcode a b bits = .ok (.Ok (),after))
    (held : ControlMapPublication before) (forward : before.next_source.val ≤ state.pos.val) :
    ControlMapPublication after := by
  obtain ⟨stable,_,cursor,_⟩ := compiler_lower_simd_effects ops law before after state opcode a b bits lower upper called
  apply held.ordinary stable (compiler_lower_simd_code_mono ops law before after state opcode a b bits lower upper called)
  rw [cursor]
  exact forward

end Itasca.Runtime.Compiler

end

/-! ## CallbackMapPublication -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts

/-- Actual br callback retains all control-map publication bounds. -/
theorem compiler_br_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (depth : U32) (types : Itasca.signature.ResultType)
    (held : ControlMapPublication before) (forward : before.next_source.val ≤ state.pos.val)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br ops before state depth types = .ok (.Ok (),after)) :
    ControlMapPublication after := by
  cases runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br.inv ops before after state depth types (.Ok ()) called with
  | dead dead observed => exact compiler_observe_map_publication ops law before after state held forward observed
  | @branched middle _ _ live branched observed =>
    have kept := compiler_branch_map_publication ops law before middle depth 0#u32 false held branched
    have cursor := compiler_branch_cursor ops law before middle depth 0#u32 false branched
    exact compiler_observe_map_publication ops law {middle with reachable := false} after state
      (kept.retained ⟨rfl, le_rfl⟩ rfl rfl le_rfl le_rfl) (by simpa only [cursor] using forward) observed

/-- Actual br_if callback retains all control-map publication bounds. -/
theorem compiler_br_if_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (depth : U32) (types : Itasca.signature.ResultType)
    (held : ControlMapPublication before) (forward : before.next_source.val ≤ state.pos.val)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if ops before state depth types = .ok (.Ok (),after)) :
    ControlMapPublication after := by
  cases runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if.inv ops before after state depth types (.Ok ()) called with
  | dead dead observed => exact compiler_observe_map_publication ops law before after state held forward observed
  | @branched middle _ _ live branched observed =>
    have kept := compiler_branch_map_publication ops law before middle depth 1#u32 true held branched
    have cursor := compiler_branch_cursor ops law before middle depth 1#u32 true branched
    exact compiler_observe_map_publication ops law middle after state
      kept (by simpa only [cursor] using forward) observed

/-- Actual unreachable callback retains all control-map publication bounds. -/
theorem compiler_unreachable_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (held : ControlMapPublication before) (forward : before.next_source.val ≤ state.pos.val)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable ops before state = .ok (.Ok (),after)) :
    ControlMapPublication after := by
  cases runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable.inv ops before after state (.Ok ()) called with
  | dead dead observed => exact compiler_observe_map_publication ops law before after state held forward observed
  | @emitted middle _ _ live emitted observed =>
    have bounds := compiler_emit_map_publication ops law before middle .Unreachable held emitted
    have cursor := compiler_emit_cursor ops before middle .Unreachable (.Ok ()) emitted
    exact compiler_observe_map_publication ops law {middle with reachable := false} after state
      (bounds.retained ⟨rfl,le_rfl⟩ rfl rfl le_rfl le_rfl) (by simpa only [cursor] using forward) observed

/-- Actual RETURN preserves maps and owners while emitting its return instruction. -/
theorem compiler_return_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (held : ControlMapPublication before)
    (forward : before.next_source.val ≤ state.pos.val)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return ops before state = .ok (.Ok (),after)) :
    ControlMapPublication after := by
  apply held.ordinary (compiler_return_ordinary_result ops law before after state (.Ok ()) called)
    (compiler_return_code_mono ops law before after state called)
  rw [compiler_return_cursor ops law before after state called]
  exact forward

end Itasca.Runtime.Compiler

end

/-! ## ElseMapPublication -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096

/-- ELSE changes the current frame's arm and fixups, preserving its map owner. -/
theorem compiler_else_map_owners {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else ops before state bt = .ok (status,after)) :
    activeControlMaps after = activeControlMaps before := by
  have effect := runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else.inv ops before after state bt status accepted
  rcases List.eq_nil_or_concat' before.frames.val with empty | ⟨prior, frame, frames⟩
  · cases effect with
    | empty noFrames => rfl
    | selected nonempty subtracted read progress => simp only [empty, List.isEmpty_nil, Bool.true_eq_false] at nonempty
  · obtain ⟨index, restore, lastIndex, restoreEq, progress⟩ := effect.last_frame frame prior frames
    obtain ⟨fixups, published⟩ := progress.frames
    unfold activeControlMaps
    rw [published, restoreEq, alloc.vec.Vec.set_val_eq]
    simp only [frames, lastIndex, Std.le_refl, List.set_append_right, tsub_self, List.set_cons_zero,
      List.map_append, List.map_cons, List.map_nil]

/-- ELSE leaves the complete control-map vector unchanged. -/
theorem compiler_else_controls_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else ops before state bt = .ok (status,after)) :
    after.function.controls = before.function.controls := by
  have frame := (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else.inv ops before after state bt status accepted).frame
  rw [frame]

/-- The actual ELSE callback retains open and already closed map ranges. -/
theorem compiler_else_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (held : ControlMapPublication before) (forward : before.next_source.val ≤ state.pos.val)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else ops before state bt = .ok (.Ok (),after)) :
    ControlMapPublication after := by
  apply held.retained (compiler_else_stable_result ops law before after state bt (.Ok ()) called)
    (compiler_else_controls_result ops law before after state bt (.Ok ()) called)
    (compiler_else_map_owners ops law before after state bt (.Ok ()) called)
    (compiler_else_code_mono ops law before after state bt called)
  rw [compiler_else_cursor ops law before after state bt called]
  exact forward

end Itasca.Runtime.Compiler

end

/-! ## FunctionPublicationRanges -/

section

/-!
Source-coordinate checks and the published ranges of a compiled function. FunctionPublicationRanges.well_formed derives final checked source ranges from bounded instruction coordinates.
-/

/-! ## Source Well Formed Acceptance -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

abbrev checkSourceCoordinate (function : runtime.bytecode.CompiledFunction) (index : Usize) : Result Bool := do
  let source ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Usize) function.source_offsets index
  if source < function.body_start then .ok false
  else if source ≥ function.body_end then .ok false
  else if index > 0#usize then do
    let prior ← index - 1#usize
    let value ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Usize) function.source_offsets prior
    if value > source then .ok false else .ok true
  else .ok true

/-- The source-coordinate gate accepts a coordinate within the body and in
nondecreasing order with its predecessor. All premises are numeric bounds. -/
theorem source_coordinate_accepts (function : runtime.bytecode.CompiledFunction) (index : Usize)
    (inside : index.val < function.source_offsets.val.length)
    (range : function.body_start.val ≤ function.source_offsets.val[index.val].val ∧
      function.source_offsets.val[index.val].val < function.body_end.val)
    (ordered : 0 < index.val →
      (function.source_offsets.val[index.val-1]'(by omega)).val ≤ function.source_offsets.val[index.val].val) :
    checkSourceCoordinate function index ⦃ result => result = true ⦄ := by
  unfold checkSourceCoordinate
  step as ⟨source,found⟩
  have beforeStart : ¬ source < function.body_start := by rw [found]; scalar_tac
  have afterEnd : ¬ source ≥ function.body_end := by rw [found]; scalar_tac
  simp only [if_neg beforeStart,if_neg afterEnd]
  split
  · rename_i positive
    step as ⟨prior,priorEq⟩
    have priorValue : prior.val = index.val - 1 := by scalar_tac
    step as ⟨value,valueEq⟩
    have comparison : ¬ value > source := by
      have sorted := ordered (by scalar_tac)
      rw [found,valueEq]
      have same : (function.source_offsets.val[prior.val]).val =
          (function.source_offsets.val[index.val-1]'(by omega)).val := by simp [priorValue]
      scalar_tac
    simp [comparison]
  · simp

/-- The ordinary-body instruction pass accepts independently bounded,
nondecreasing source coordinates and valid instruction operands. -/
theorem check_source_instructions_accepts (function : runtime.bytecode.CompiledFunction)
    (length index : Usize) (codeLength : length.val = function.code.length)
    (sourceLength : function.source_offsets.length = function.code.length)
    (inside : index.val ≤ length.val)
    (ranges : ∀ (j : Nat) (bound : j < function.source_offsets.val.length),
      function.body_start.val ≤ function.source_offsets.val[j].val ∧
      function.source_offsets.val[j].val < function.body_end.val)
    (ordered : ∀ (j : Nat) (positive : 0 < j) (bound : j < function.source_offsets.val.length),
      (function.source_offsets.val[j-1]'(by omega)).val ≤ function.source_offsets.val[j].val)
    (valid : ∀ (j : Nat) (bound : j < function.code.length),
      runtime.bytecode.CompiledFunction.instruction_valid function function.code.val[j] = .ok true) :
    checkInstructions function length false true index ⦃ result => result = true ⦄ := by
  unfold checkInstructions runtime.bytecode.CompiledFunction.well_formed_loop0
  apply loop.spec_decr_nat (fun state => length.val - state.2.val)
    (fun state => state.1 = true ∧ state.2.val ≤ length.val)
  · rintro ⟨flag,current⟩ ⟨rfl,bounded⟩
    unfold runtime.bytecode.CompiledFunction.well_formed_loop0.body
    dsimp only
    split
    · rename_i more
      have atCode : current.val < function.code.length := by scalar_tac
      have atSource : current.val < function.source_offsets.val.length := by
        change current.val < function.source_offsets.length
        omega
      simp only [↓reduceIte,Bool.false_eq_true,if_false]
      apply WP.spec_bind (source_coordinate_accepts function current atSource (ranges _ atSource)
        (fun positive => ordered _ positive atSource))
      intro checked accepted
      rw [accepted]
      step as ⟨instruction,foundInstruction⟩
      rw [foundInstruction,valid current.val atCode]
      simp only [↓reduceIte,bind_ok]
      step as ⟨next,advanced⟩
      all_goals scalar_tac
    · simp
  · exact ⟨rfl,inside⟩

end Itasca.Runtime.Compiler

end

/-! ## Sourced Well Formed Acceptance -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- The actual sourced instruction pass accepts from monotone, in-range
source coordinates and the local validity of each stored instruction. -/
theorem check_sourced_instructions_accepts (function : runtime.bytecode.CompiledFunction)
    (length index : Usize) (codeLength : length.val = function.code.length)
    (sourceLength : function.source_offsets.length = function.code.length)
    (inside : index.val ≤ length.val)
    (coordinates : ∀ (j : Nat) (bound : j < function.source_offsets.length),
      function.body_start.val ≤ function.source_offsets.val[j].val ∧
      function.source_offsets.val[j].val < function.body_end.val ∧
      (0 < j → (function.source_offsets.val[j-1]'(by have bounded : j < function.source_offsets.val.length := bound; omega)).val ≤ function.source_offsets.val[j].val))
    (valid : ∀ (j : Nat) (bound : j < function.code.length),
      runtime.bytecode.CompiledFunction.instruction_valid function function.code.val[j] = .ok true) :
    checkInstructions function length false true index ⦃ result => result = true ⦄ := by
  exact check_source_instructions_accepts function length index codeLength sourceLength inside
    (fun j bound => ⟨(coordinates j bound).1,(coordinates j bound).2.1⟩)
    (fun j positive bound => (coordinates j bound).2.2 positive) valid

/-- Acceptance direction of the complete sourced publication checker. The
premises expose the local instruction, source-coordinate, target, and control
range obligations separately, for preservation through actual compilation. -/
theorem well_formed_sourced_accepts (function : runtime.bytecode.CompiledFunction)
    (nonsynthetic : ¬ (function.body_start = 0#usize ∧ function.body_end = 0#usize))
    (nonempty : 0 < function.code.length)
    (sourceLength : function.source_offsets.length = function.code.length)
    (locals : function.local_slots.val ≤ function.slot_count.val)
    (params : function.param_slots.val ≤ function.local_slots.val)
    (returnStart returnCount : U32)
    (last : function.code.val[function.code.length-1]? = some (.Return returnStart returnCount))
    (instructions : ∀ (j : Nat) (bound : j < function.code.length),
      runtime.bytecode.CompiledFunction.instruction_valid function function.code.val[j] = .ok true)
    (coordinates : ∀ (j : Nat) (bound : j < function.source_offsets.length),
      function.body_start.val ≤ function.source_offsets.val[j].val ∧
      function.source_offsets.val[j].val < function.body_end.val ∧
      (0 < j → (function.source_offsets.val[j-1]'(by have bounded : j < function.source_offsets.val.length := bound; omega)).val ≤ function.source_offsets.val[j].val))
    (targets : ∀ entry ∈ function.jump_tables.val, entry.val < function.code.length)
    (ranges : ∀ entry ∈ function.controls.val,
      entry.start_pc.val ≤ entry.end_pc.val ∧ entry.end_pc.val < function.code.length ∧
      function.body_start.val ≤ entry.source_start.val ∧ entry.source_end.val ≤ function.body_end.val ∧
      entry.source_start.val < entry.source_end.val) :
    runtime.bytecode.CompiledFunction.well_formed function ⦃ result => result = true ⦄ := by
  have sourced : (if function.body_start = 0#usize then Result.ok (decide (function.body_end = 0#usize)) else Result.ok false : Result Bool) = Result.ok false := by
    by_cases first : function.body_start = 0#usize
    · have last : function.body_end ≠ 0#usize := by tauto
      simp [first,last]
    · simp [first]
  have notEmpty : alloc.vec.Vec.len function.code ≠ 0#usize := by scalar_tac
  have equalLength : alloc.vec.Vec.len function.source_offsets = alloc.vec.Vec.len function.code :=
    UScalar.eq_of_val_eq sourceLength
  have notLocals : ¬ function.local_slots > function.slot_count := by scalar_tac
  have notParams : ¬ function.param_slots > function.local_slots := by scalar_tac
  unfold runtime.bytecode.CompiledFunction.well_formed
  rw [sourced]
  simp [notEmpty,equalLength,notLocals,notParams]
  step as ⟨index,indexEq⟩
  have indexValue : index.val = function.code.length-1 := by scalar_tac
  have atCode : index.val < function.code.length := by omega
  step as ⟨instruction,found⟩
  have selected : instruction = .Return returnStart returnCount := by
    have atLast : function.code.val[index.val]? = some instruction := by
      simp [List.getElem?_eq_getElem atCode,found]
    rw [indexValue,last] at atLast
    exact (Option.some.inj atLast).symm
  rw [selected]
  simp only [runtime.bytecode.is_return,bind_ok,↓reduceIte]
  change (do
    let valid ← checkInstructions function (alloc.vec.Vec.len function.code) false true 0#usize
    let valid' ← runtime.bytecode.CompiledFunction.well_formed_loop1 function.jump_tables (alloc.vec.Vec.len function.code) valid 0#usize
    runtime.bytecode.CompiledFunction.well_formed_loop2 function.controls function.body_start function.body_end
      (alloc.vec.Vec.len function.code) valid' 0#usize) ⦃ result => result = true ⦄
  step with check_sourced_instructions_accepts function (alloc.vec.Vec.len function.code) 0#usize rfl sourceLength
    (by scalar_tac) coordinates instructions as ⟨checked,accepted⟩
  rw [accepted]
  step with check_jump_tables_accepts function.jump_tables (alloc.vec.Vec.len function.code) 0#usize
    (by scalar_tac) targets as ⟨checked,accepted⟩
  rw [accepted]
  apply check_control_maps_accepts function.controls function.body_start function.body_end
    (alloc.vec.Vec.len function.code) 0#usize (by scalar_tac) ranges

end Itasca.Runtime.Compiler

end

/-! ## Function Publication Ranges -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Source-coordinate and control-target obligations of the actual final
checker, separated from instruction validity and function slot metadata. -/
structure FunctionPublicationRanges (function : runtime.bytecode.CompiledFunction) : Prop where
  sourceLength : function.source_offsets.length = function.code.length
  sources : ∀ (index : Nat) (bound : index < function.source_offsets.length),
    function.body_start.val ≤ function.source_offsets.val[index].val ∧
    function.source_offsets.val[index].val < function.body_end.val ∧
    (0 < index → (function.source_offsets.val[index-1]'(by
      have bounded : index < function.source_offsets.val.length := bound; omega)).val ≤
      function.source_offsets.val[index].val)
  controls : FinalControlMapBounds function
  targets : ∀ target ∈ function.jump_tables.val, target.val < function.code.length

/-- Once local instruction and slot obligations are established, the retained
ranges discharge all remaining source and control checks in the real checker. -/
theorem FunctionPublicationRanges.well_formed {function : runtime.bytecode.CompiledFunction}
    (held : FunctionPublicationRanges function)
    (nonsynthetic : ¬ (function.body_start = 0#usize ∧ function.body_end = 0#usize))
    (nonempty : 0 < function.code.length)
    (locals : function.local_slots.val ≤ function.slot_count.val)
    (params : function.param_slots.val ≤ function.local_slots.val)
    (returnStart returnCount : U32)
    (last : function.code.val[function.code.length-1]? = some (.Return returnStart returnCount))
    (instructions : ∀ (index : Nat) (bound : index < function.code.length),
      runtime.bytecode.CompiledFunction.instruction_valid function function.code.val[index] = .ok true) :
    runtime.bytecode.CompiledFunction.well_formed function ⦃ result => result = true ⦄ :=
  well_formed_sourced_accepts function nonsynthetic nonempty held.sourceLength locals params returnStart returnCount
    last instructions held.sources held.targets held.controls

end Itasca.Runtime.Compiler

end

end

/-! ## FunctionPublicationHeader -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Non-instruction header checks required for publishing a sourced function.
These facts do not assume that the final checker accepts. -/
structure FunctionPublicationHeader (function : runtime.bytecode.CompiledFunction) : Prop where
  nonsynthetic : ¬ (function.body_start = 0#usize ∧ function.body_end = 0#usize)
  nonempty : 0 < function.code.length
  locals : function.local_slots.val ≤ function.slot_count.val
  params : function.param_slots.val ≤ function.local_slots.val
  last : ∃ start count, function.code.val[function.code.length-1]? = some (.Return start count)

/-- Header and range preservation reduce publication to the validity of each
stored instruction; successful checking is a conclusion. -/
theorem FunctionPublicationHeader.well_formed {function : runtime.bytecode.CompiledFunction}
    (header : FunctionPublicationHeader function) (ranges : FunctionPublicationRanges function)
    (instructions : ∀ (index : Nat) (bound : index < function.code.length),
      runtime.bytecode.CompiledFunction.instruction_valid function function.code.val[index] = .ok true) :
    runtime.bytecode.CompiledFunction.well_formed function = .ok true := by
  obtain ⟨start,count,last⟩ := header.last
  obtain ⟨result,called,rfl⟩ := WP.spec_imp_exists
    (ranges.well_formed header.nonsynthetic header.nonempty header.locals header.params start count last instructions)
  exact called

/-- Once the separately proved bytecode obligations hold, actual compiler
finish succeeds without allocating or changing the retained budget. -/
theorem compiler_finish_publication {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A)
    (closed : compiler.frames.val = [])
    (header : FunctionPublicationHeader compiler.function)
    (ranges : FunctionPublicationRanges compiler.function)
    (instructions : ∀ (index : Nat) (bound : index < compiler.function.code.length),
      runtime.bytecode.CompiledFunction.instruction_valid compiler.function compiler.function.code.val[index] = .ok true) :
    runtime.compiler.FunctionCompiler.finish ops compiler (.Ok ()) = .ok (.Ok compiler.function,compiler.budget) := by
  exact runtime.compiler.FunctionCompiler.finish.available ops compiler closed
    (header.well_formed ranges instructions)

end Itasca.Runtime.Compiler

end

/-! ## StartMapPublication -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Actual construction and function-start establish the initial map invariant. -/
theorem compiler_start_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (signatures : Slice runtime.compiler.Signature)
    (functionSlots : Slice U32) (budget : runtime.compiler.Budget A) (batchStart : Usize)
    (initial started : runtime.compiler.FunctionCompiler A)
    (ctx : Itasca.code.Context) (typeIndex : U32) (signature : runtime.compiler.Signature)
    (bodyBegin bodyEnd : Usize)
    (lookup : signatures.val[typeIndex.val]? = some signature)
    (beginFits : batchStart.val + bodyBegin.val ≤ Usize.max)
    (endFits : batchStart.val + bodyEnd.val ≤ Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart = .ok initial)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start
      ops initial ctx typeIndex bodyBegin bodyEnd = .ok (.Ok (), started)) :
    ControlMapPublication started := by
  have newPost := compiler_new ops signatures functionSlots budget batchStart
  rw [created, WP.spec_ok] at newPost
  obtain ⟨localLayout, emptyLocals, emptyOperands, emptyMaps, emptyFrames, emptyCode,
    reachable, sigs, functionWidths, coordinate⟩ := newPost
  have startPost := compiler_function_start ops law initial ctx typeIndex signature bodyBegin bodyEnd
    (by simpa only [sigs] using lookup) (by simpa only [coordinate] using beginFits)
    (by simpa only [coordinate] using endFits) emptyLocals localLayout emptyOperands
    (by simp [emptyMaps]; scalar_tac) (by simp [emptyFrames]; scalar_tac)
  rw [accepted, WP.spec_ok] at startPost
  obtain ⟨layout, live, capacity, localTypes, params, typeIdx, start, finish, codeEq, framesEq, mapsEq⟩ := startPost rfl
  apply ControlMapPublication.initial started
    ⟨.Body, started.function.body_start, 0#usize, 0#usize, 0#usize, 0#usize, 0#usize, signature.results⟩
    ⟨0#usize, .Body, started.function.local_slots, 0#u32, signature.result_slots,
      0#u32, none, true, false, alloc.vec.Vec.new Usize⟩
  · simpa only [emptyMaps,List.nil_append] using mapsEq
  · simpa only [emptyFrames,List.nil_append] using framesEq
  · rfl
  · rfl
  · rfl

end Itasca.Runtime.Compiler

end
