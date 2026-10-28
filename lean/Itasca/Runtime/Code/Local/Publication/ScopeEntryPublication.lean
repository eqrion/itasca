import Itasca.Runtime.Code.Local.Publication.EnterMapPublication
import Itasca.Runtime.Code.Local.Coordinates.ControlSourceCoordinates

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
