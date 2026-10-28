import Exec.Code.Local.Relations.Control.ControlHeightSuccess
import Exec.Code.Local.Callbacks.Control.EnterBlock
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Successful entry computes its exact slot and byte coordinates before any
allocation. These bounds follow from the actual checked model's normal return,
so dormant entries need no speculative source-stack size premise. -/
theorem control_entry_coordinates {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (ctrl : Itasca.code.Ctrl) (prior : List Itasca.code.Ctrl)
    (kind : Itasca.code.LabelKind) (bt : Itasca.signature.BlockType)
    (controls : state.ctrls.val = prior ++ [ctrl])
    (valuesFit : ctrl.value_stack_base.val ≤ state.vals.val.length)
    (success : runtime.compiler.control.FunctionCompiler.enter ops before state kind bt = .ok (.Ok (), after)) :
    before.function.local_slots.val + stackWords (state.vals.val.take ctrl.value_stack_base.val) ≤ U32.max ∧
      before.function.body_start.val + before.next_source.val ≤ Usize.max := by
  have nonempty : alloc.vec.Vec.len state.ctrls ≠ 0#usize := by
    intro eq
    have same := congrArg UScalar.val eq
    simp [alloc.vec.Vec.len, controls] at same
  unfold runtime.compiler.control.FunctionCompiler.enter at success
  rw [if_neg nonempty] at success
  obtain ⟨index, subtracted, rest⟩ := initializer_bind_success success
  have subSpec : alloc.vec.Vec.len state.ctrls - 1#usize ⦃ out => out.val = prior.length ⦄ := by
    step as ⟨out, h⟩
    simp [alloc.vec.Vec.len, controls] at h
    omega
  rw [subtracted, WP.spec_ok] at subSpec
  obtain ⟨control, read, rest⟩ := initializer_bind_success rest
  have readSpec : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Itasca.code.Ctrl)
      state.ctrls index ⦃ out => out = ctrl ⦄ := by
    have bounded : index.val < state.ctrls.val.length := by simp [controls, subSpec]
    step as ⟨out, found⟩
    simpa [controls, subSpec] using found
  rw [read, WP.spec_ok] at readSpec
  subst control
  obtain ⟨signature, selected, rest⟩ := initializer_bind_success rest
  obtain ⟨height, heightCall, rest⟩ := initializer_bind_success rest
  have heightEq := control_stack_height_success state.vals.deref ctrl.value_stack_base
    before.function.local_slots height (by simpa [alloc.vec.Vec.deref] using valuesFit) heightCall
  obtain ⟨source, sourceCall, rest⟩ := initializer_bind_success rest
  have sourceEq := control_add_success sourceCall
  have heightBound : height.val ≤ U32.max := by scalar_tac
  have sourceBound : source.val ≤ Usize.max := by scalar_tac
  exact ⟨by simpa [heightEq, alloc.vec.Vec.deref] using heightBound, by omega⟩

end Itasca.Runtime.Code
