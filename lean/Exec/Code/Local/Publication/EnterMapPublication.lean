import Exec.Code.Local.Publication.ControlMapEnterEffect
import Exec.Code.Local.Callbacks.Control.EnterIf
import Exec.Code.Local.Callbacks.Common.EnterDead
import Exec.Code.Local.Callbacks.Common.CompilerEnterMetadata
import Exec.Code.Local.Callbacks.Control.CompilerCodeMonotoneControl
import Exec.Code.Local.Relations.Control.ControlCursor

namespace Exec.Code
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

end Exec.Code
