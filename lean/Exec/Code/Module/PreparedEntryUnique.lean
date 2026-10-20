import Itasca.Binary.Wasm1.EncodingUnique
import Itasca.Module.Code.ReachedEntry
import Itasca.Module.Code.LocalsComplete

namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Pure entry decoding determines all inputs to source body demand. Grouping
of declared locals does not affect the expanded context consumed by compilation. -/
theorem prepared_entry_unique {data env index start profile}
    (first second : CodeEntry.Prepared data env index start profile) :
    first.typeIdx = second.typeIdx ∧ first.ctx = second.ctx ∧ first.body = second.body ∧
      first.bodyStart = second.bodyStart ∧ first.finish = second.finish := by
  have typeEq : first.typeIdx = second.typeIdx := first.index_type.symm.trans second.index_type
  have functionEq : first.ft = second.ft := by
    have left := first.function_type
    have right := second.function_type
    simpa only [typeEq,right] using left.symm
  obtain ⟨sizeEq,contentEq⟩ := first.header.unique second.header
  have finishEq : first.finish = second.finish := UScalar.eq_of_val_eq (by
    have left := first.extent
    have right := second.extent
    rw [sizeEq,contentEq] at left
    omega)
  obtain ⟨declaredLeft,decodedLeft,valuesLeft⟩ := module.decode_locals.complete data first.content profile first.groups
    first.bodyStart first.locals_bytes first.locals_allowed first.locals_bound
  obtain ⟨declaredRight,decodedRight,valuesRight⟩ := module.decode_locals.complete data second.content profile second.groups
    second.bodyStart second.locals_bytes second.locals_allowed second.locals_bound
  rw [contentEq,decodedRight] at decodedLeft
  have localsEq : declaredLeft = declaredRight ∧ first.bodyStart = second.bodyStart := by
    simpa only [Result.ok.injEq,core.result.Result.Ok.injEq,Prod.mk.injEq] using decodedLeft.symm
  have groupsEq : ModuleLocals.declared first.groups = ModuleLocals.declared second.groups := by
    rw [localsEq.1] at valuesLeft
    exact valuesLeft.symm.trans valuesRight
  have ctxLocals : first.ctx.locals = second.ctx.locals := alloc.vec.Vec.ext _ _ (by
    rw [first.context_locals,second.context_locals,functionEq,groupsEq])
  have ctxResults : first.ctx.results = second.ctx.results := alloc.vec.Vec.ext _ _ (by
    rw [first.context_results,second.context_results,functionEq])
  have ctxEq : first.ctx = second.ctx := by
    cases left : first.ctx
    cases right : second.ctx
    simp_all
  have bodyEq : first.body = second.body := Slice.ext _ _ (by
    have left := first.body_bytes.suffix
    rw [localsEq.2,finishEq] at left
    exact List.append_cancel_right (left.symm.trans second.body_bytes.suffix))
  exact ⟨typeEq,ctxEq,bodyEq,localsEq.2,finishEq⟩

end Exec.Code
