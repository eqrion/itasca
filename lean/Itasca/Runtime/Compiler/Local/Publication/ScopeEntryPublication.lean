import Itasca.Runtime.Compiler.Local.Publication.ControlMapPublication
import Itasca.Runtime.Compiler.Local.Callbacks.Control.EnterIf
import Itasca.Runtime.Compiler.Local.Callbacks.Function.EnterDead
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerEnterMetadata
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CompilerCodeMonotoneControl
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlCursor
import Itasca.Runtime.Compiler.Local.Coordinates.ControlSourceCoordinates

/-!
Publication of entered scope maps. Block, loop and if effects establish the common ScopeEntryGeometry and publication result.
-/

/-! ## Control Map Enter Effect -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Exact frame and map appends from the enter callbacks establish ownership
and the new map's bounds from its emitted position and source origin. -/
theorem ControlMapPublication.enter_effect {A : Type}
    {before after : runtime.compiler.FunctionCompiler A}
    (held : ControlMapPublication before) (stable : CompilerStable before after)
    (frame : runtime.compiler.Frame) (entry : runtime.compiler.ControlMap)
    (frames : after.frames.val = before.frames.val ++ [frame])
    (owner : frame.map.val = before.function.controls.length)
    (controls : after.function.controls.val = before.function.controls.val ++ [entry])
    (position : entry.start_pc.val ≤ after.function.code.length)
    (origin : entry.source_start.val = before.function.body_start.val+before.next_source.val)
    (code : before.function.code.length ≤ after.function.code.length)
    (cursor : before.next_source.val ≤ after.next_source.val) : ControlMapPublication after := by
  have active : activeControlMaps after = activeControlMaps before ++ [before.function.controls.length] := by
    simp [activeControlMaps,frames,owner]
  apply held.push stable entry controls active code cursor
  obtain ⟨_,_,_,_,_,_,_,start,_,_⟩ := stable.fields
  unfold OpenControlMapBounds
  rw [origin,start]
  exact ⟨position,by omega,by omega⟩

end Itasca.Runtime.Code

end

/-! ## Enter Map Publication -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Actual BLOCK entry establishes the newly owned map bounds. -/
theorem compiler_enter_block_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (ctrl : Itasca.code.Ctrl) (prior : List Itasca.code.Ctrl)
    (bt : Itasca.signature.BlockType) (signature : runtime.compiler.Signature) (pc : U32)
    (controls : state.ctrls.val = prior ++ [ctrl])
    (selected : SignatureAt compiler.signatures bt signature)
    (valuesFit : ctrl.value_stack_base.val ≤ state.vals.val.length)
    (heightFits : compiler.function.local_slots.val +
      stackWords (state.vals.val.take ctrl.value_stack_base.val) ≤ U32.max)
    (sourceFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max)
    (position : pc.val = compiler.function.code.val.length)
    (mapsFit : compiler.function.controls.val.length < Usize.max)
    (framesFit : compiler.frames.val.length < Usize.max)
    (reachable : compiler.reachable = true)
    (held : ControlMapPublication compiler) (forward : compiler.next_source.val ≤ state.pos.val)
    (after : runtime.compiler.FunctionCompiler A)
    (called : runtime.compiler.control.FunctionCompiler.enter ops compiler state .Block bt = .ok (.Ok (),after)) :
    ControlMapPublication after := by
  have effect := enter_block ops law compiler state ctrl prior bt signature pc controls selected valuesFit heightFits sourceFits position mapsFit framesFit reachable
  rw [called,WP.spec_ok] at effect
  obtain ⟨code,_,height,source,_,origin,frames,maps⟩ := effect rfl
  have stable := compiler_enter_stable_result ops law compiler after state .Block bt (.Ok ()) called
  have growth := compiler_enter_code_mono ops law compiler after state .Block bt called
  have cursor := compiler_enter_cursor ops law compiler after state .Block bt called
  have pcBound : pc.val ≤ after.function.code.val.length := by
    rw [code]
    omega
  apply held.enter_effect stable _ _ frames (by simp [alloc.vec.Vec.len]) maps
    (by change (UScalar.cast .Usize pc).val ≤ after.function.code.length; scalar_tac) origin growth
  rw [cursor]
  exact forward

/-- Actual LOOP entry establishes the newly owned map bounds. -/
theorem compiler_enter_loop_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (ctrl : Itasca.code.Ctrl) (prior : List Itasca.code.Ctrl)
    (bt : Itasca.signature.BlockType) (signature : runtime.compiler.Signature) (pc : U32)
    (controls : state.ctrls.val = prior ++ [ctrl])
    (selected : SignatureAt compiler.signatures bt signature)
    (valuesFit : ctrl.value_stack_base.val ≤ state.vals.val.length)
    (heightFits : compiler.function.local_slots.val +
      stackWords (state.vals.val.take ctrl.value_stack_base.val) ≤ U32.max)
    (sourceFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max)
    (position : pc.val = compiler.function.code.val.length)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (offsetsFit : compiler.function.source_offsets.val.length < Usize.max)
    (mapsFit : compiler.function.controls.val.length < Usize.max)
    (framesFit : compiler.frames.val.length < Usize.max)
    (reachable : compiler.reachable = true)
    (held : ControlMapPublication compiler) (forward : compiler.next_source.val ≤ state.pos.val)
    (after : runtime.compiler.FunctionCompiler A)
    (called : runtime.compiler.control.FunctionCompiler.enter ops compiler state .Loop bt = .ok (.Ok (),after)) :
    ControlMapPublication after := by
  have effect := enter_loop ops law compiler state ctrl prior bt signature pc controls selected valuesFit heightFits sourceFits position codeFits offsetsFit mapsFit framesFit reachable
  rw [called,WP.spec_ok] at effect
  obtain ⟨code,_,height,source,_,origin,frames,maps⟩ := effect rfl
  have stable := compiler_enter_stable_result ops law compiler after state .Loop bt (.Ok ()) called
  have growth := compiler_enter_code_mono ops law compiler after state .Loop bt called
  have cursor := compiler_enter_cursor ops law compiler after state .Loop bt called
  have pcBound : pc.val ≤ after.function.code.val.length := by
    rw [code]
    simp only [List.length_append,List.length_singleton]
    omega
  apply held.enter_effect stable _ _ frames (by simp [alloc.vec.Vec.len]) maps
    (by change (UScalar.cast .Usize pc).val ≤ after.function.code.length; scalar_tac) origin growth
  rw [cursor]
  exact forward

/-- Actual IF entry establishes the newly owned map bounds. -/
theorem compiler_enter_if_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (ctrl : Itasca.code.Ctrl) (prior : List Itasca.code.Ctrl)
    (bt : Itasca.signature.BlockType) (signature : runtime.compiler.Signature) (pc : U32)
    (stack : List valtype) (layout : CompilerLayout compiler (stack ++ [.I32]))
    (codeFits : compiler.function.code.val.length < Usize.max)
    (offsetsFit : compiler.function.source_offsets.val.length < Usize.max)
    (controls : state.ctrls.val = prior ++ [ctrl])
    (selected : SignatureAt compiler.signatures bt signature)
    (valuesFit : ctrl.value_stack_base.val ≤ state.vals.val.length)
    (heightFits : compiler.function.local_slots.val +
      stackWords (state.vals.val.take ctrl.value_stack_base.val) ≤ U32.max)
    (sourceFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max)
    (position : pc.val = compiler.function.code.val.length + 1)
    (mapsFit : compiler.function.controls.val.length < Usize.max)
    (framesFit : compiler.frames.val.length < Usize.max)
    (reachable : compiler.reachable = true)
    (held : ControlMapPublication compiler) (forward : compiler.next_source.val ≤ state.pos.val)
    (after : runtime.compiler.FunctionCompiler A)
    (called : runtime.compiler.control.FunctionCompiler.enter ops compiler state .Then bt = .ok (.Ok (),after)) :
    ControlMapPublication after := by
  have effect := enter_if ops law compiler state ctrl prior bt signature pc stack layout codeFits offsetsFit controls selected valuesFit heightFits sourceFits position mapsFit framesFit reachable
  rw [called,WP.spec_ok] at effect
  obtain ⟨_,condition,height,source,_,code,_,origin,frames,maps⟩ := effect rfl
  have stable := compiler_enter_stable_result ops law compiler after state .Then bt (.Ok ()) called
  have growth := compiler_enter_code_mono ops law compiler after state .Then bt called
  have cursor := compiler_enter_cursor ops law compiler after state .Then bt called
  have pcBound : pc.val ≤ after.function.code.val.length := by
    rw [code]
    simp only [List.length_append,List.length_singleton]
    omega
  apply held.enter_effect stable _ _ frames (by simp [alloc.vec.Vec.len]) maps
    (by change (UScalar.cast .Usize pc).val ≤ after.function.code.length; scalar_tac) origin growth
  rw [cursor]
  exact forward

/-- Actual DEAD entry establishes the newly owned map bounds. -/
theorem compiler_enter_dead_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (ctrl : Itasca.code.Ctrl) (prior : List Itasca.code.Ctrl)
    (kind : Itasca.code.LabelKind) (bt : Itasca.signature.BlockType) (signature : runtime.compiler.Signature) (pc : U32)
    (controls : state.ctrls.val = prior ++ [ctrl])
    (selected : SignatureAt compiler.signatures bt signature)
    (valuesFit : ctrl.value_stack_base.val ≤ state.vals.val.length)
    (heightFits : compiler.function.local_slots.val +
      stackWords (state.vals.val.take ctrl.value_stack_base.val) ≤ U32.max)
    (sourceFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max)
    (position : pc.val = compiler.function.code.val.length)
    (mapsFit : compiler.function.controls.val.length < Usize.max)
    (framesFit : compiler.frames.val.length < Usize.max)
    (reachable : compiler.reachable = false)
    (held : ControlMapPublication compiler) (forward : compiler.next_source.val ≤ state.pos.val)
    (after : runtime.compiler.FunctionCompiler A)
    (called : runtime.compiler.control.FunctionCompiler.enter ops compiler state kind bt = .ok (.Ok (),after)) :
    ControlMapPublication after := by
  have effect := enter_dead ops law compiler state ctrl prior kind bt signature pc controls selected valuesFit heightFits sourceFits position mapsFit framesFit reachable
  rw [called,WP.spec_ok] at effect
  obtain ⟨code,_,height,source,_,origin,frames,maps⟩ := effect rfl
  have stable := compiler_enter_stable_result ops law compiler after state kind bt (.Ok ()) called
  have growth := compiler_enter_code_mono ops law compiler after state kind bt called
  have cursor := compiler_enter_cursor ops law compiler after state kind bt called
  have pcBound : pc.val ≤ after.function.code.val.length := by
    rw [code]
    omega
  apply held.enter_effect stable _ _ frames (by simp [alloc.vec.Vec.len]) maps
    (by change (UScalar.cast .Usize pc).val ≤ after.function.code.length; scalar_tac) origin growth
  rw [cursor]
  exact forward

end Itasca.Runtime.Code

end

/-! ## Scope Entry Publication -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Source-reader geometry needed to open a frame. These are local stack,
signature, coordinate and reserve bounds, independent of completed code. -/
structure ScopeEntryGeometry {A : Type} (before : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType) where
  ctrl : Itasca.code.Ctrl
  prior : List Itasca.code.Ctrl
  signature : runtime.compiler.Signature
  pc : U32
  controls : state.ctrls.val = prior ++ [ctrl]
  selected : SignatureAt before.signatures bt signature
  valuesFit : ctrl.value_stack_base.val ≤ state.vals.val.length
  heightFits : before.function.local_slots.val+stackWords (state.vals.val.take ctrl.value_stack_base.val) ≤ U32.max
  sourceFits : before.function.body_start.val+before.next_source.val ≤ Usize.max
  mapsFit : before.function.controls.val.length < Usize.max
  framesFit : before.frames.val.length < Usize.max

/-- Live IF accounts for its guard, live LOOP for its hook, and dead entry
emits neither. Reachability and PC premises refer to the current prefix. -/
inductive ScopeEntryMode {A : Type} {before : runtime.compiler.FunctionCompiler A}
    {state : Itasca.code.OpIterState} {bt : Itasca.signature.BlockType}
    (geometry : ScopeEntryGeometry before state bt) : Itasca.code.LabelKind → Prop where
  | block (live : before.reachable = true)
      (position : geometry.pc.val = before.function.code.val.length) : ScopeEntryMode geometry .Block
  | loop (live : before.reachable = true)
      (position : geometry.pc.val = before.function.code.val.length)
      (codeFits : before.function.code.val.length < Usize.max)
      (offsetsFit : before.function.source_offsets.val.length < Usize.max) : ScopeEntryMode geometry .Loop
  | if_ (stack : List valtype) (layout : CompilerLayout before (stack ++ [.I32]))
      (live : before.reachable = true)
      (position : geometry.pc.val = before.function.code.val.length+1)
      (codeFits : before.function.code.val.length < Usize.max)
      (offsetsFit : before.function.source_offsets.val.length < Usize.max) : ScopeEntryMode geometry .Then
  | dead (kind : Itasca.code.LabelKind) (dormant : before.reachable = false)
      (position : geometry.pc.val = before.function.code.val.length) : ScopeEntryMode geometry kind

/-- Actual frame entry preserves source coordinates and control-map bounds
from the source reader's local geometry, in every live and dormant mode. -/
theorem compiler_scope_entry_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind) (bt : Itasca.signature.BlockType)
    (geometry : ScopeEntryGeometry before state bt) (mode : ScopeEntryMode geometry kind)
    (coordinates : SourceCoordinates before) (maps : ControlMapPublication before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (forward : before.next_source.val ≤ state.pos.val)
    (called : runtime.compiler.control.FunctionCompiler.enter ops before state kind bt = .ok (.Ok (),after)) :
    SourceCoordinates after ∧ ControlMapPublication after := by
  refine ⟨compiler_enter_source_coordinates ops law before after state kind bt coordinates inside forward called,?_⟩
  cases mode with
  | block live position =>
    exact compiler_enter_block_map_publication ops law before state geometry.ctrl geometry.prior bt geometry.signature geometry.pc
      geometry.controls geometry.selected geometry.valuesFit geometry.heightFits geometry.sourceFits position
      geometry.mapsFit geometry.framesFit live maps forward after called
  | loop live position codeFits offsetsFit =>
    exact compiler_enter_loop_map_publication ops law before state geometry.ctrl geometry.prior bt geometry.signature geometry.pc
      geometry.controls geometry.selected geometry.valuesFit geometry.heightFits geometry.sourceFits position codeFits offsetsFit
      geometry.mapsFit geometry.framesFit live maps forward after called
  | if_ stack layout live position codeFits offsetsFit =>
    exact compiler_enter_if_map_publication ops law before state geometry.ctrl geometry.prior bt geometry.signature geometry.pc
      stack layout codeFits offsetsFit geometry.controls geometry.selected geometry.valuesFit geometry.heightFits
      geometry.sourceFits position geometry.mapsFit geometry.framesFit live maps forward after called
  | dead kind dormant position =>
    exact compiler_enter_dead_map_publication ops law before state geometry.ctrl geometry.prior kind bt geometry.signature geometry.pc
      geometry.controls geometry.selected geometry.valuesFit geometry.heightFits geometry.sourceFits position
      geometry.mapsFit geometry.framesFit dormant maps forward after called

end Itasca.Runtime.Code

end
