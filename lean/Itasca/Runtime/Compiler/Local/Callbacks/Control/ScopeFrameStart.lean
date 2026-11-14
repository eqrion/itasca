import Itasca.Runtime.Compiler.Local.Lowering.Control.BranchEffects
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ElseContracts
import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.FixupPreservation
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CloseScope
import Itasca.Runtime.Compiler.Local.Relations.Function.FunctionEnvironment
import Itasca.Runtime.Compiler.Local.Source.TypedRunClosed

/-!
Sections, each formerly its own module: FixupBranchPreservation, FixupElsePreservation, ScopeFrameStart.
-/

/-! ## FixupBranchPreservation -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts

set_option maxRecDepth 4096

theorem BranchJumpCall.frames {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {instruction guard status}
    (effect : BranchJumpCall ops before after instruction guard status) : after.frames = before.frames := by
  obtain ⟨answer, middle, called, rest⟩ := effect
  have emitted := (runtime.compiler.FunctionCompiler.emit.inv ops before middle instruction answer called).1
  have head : middle.frames = before.frames := by rw [emitted]
  cases answer with
  | Err error => rw [rest.2]; exact head
  | Ok value =>
    cases guard with
    | none => rw [rest.2]; exact head
    | some site =>
      obtain ⟨answer, patched, pcCall, tail⟩ := rest
      have pc := compiler_pc ops middle
      rw [pcCall, WP.spec_ok] at pc
      obtain ⟨budget, same⟩ := pc.2.2
      change patched = {middle with budget} at same
      cases answer with
      | Err error => rw [tail.2, same]; exact head
      | Ok target =>
        rcases compiler_patch_cases ops patched after site target status tail with unchanged | ⟨instruction, code, frame, contents⟩
        · rw [unchanged, same]; exact head
        · rw [frame, same]; exact head

theorem BranchPublication.fixup_budget {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {index conditional copying condition guard}
    (effect : BranchPublication ops before after index conditional copying condition guard (.Ok ()))
    (law : Platform.AllocCorrect ops)
    (budget : FixupBudget before.frames.val before.function.code.val.length) :
    FixupBudget after.frames.val after.function.code.val.length := by
  obtain ⟨frame, restore, read, tail⟩ := effect
  fixup_effect read using ops, law
  have readSpec : before.frames.val[index.val]? = some frame := by assumption
  obtain ⟨ready, frames, readyEq, update, jump⟩ :=
    (show BranchPublication ops before after index conditional copying condition guard (.Ok ()) from
      ⟨frame, restore, read, tail⟩).success law frame readSpec
  have growth := jump.code_strict law
  rw [jump.frames]
  unfold BranchFrameUpdate at update
  split at update
  · rw [update]
    apply budget.mono
    rw [readyEq] at growth
    change before.function.code.val.length < after.function.code.val.length at growth
    omega
  · obtain ⟨fixups, changed, appended⟩ := update
    rw [changed]
    apply budget.branch index.val frame fixups readSpec
    · simp only [appended, List.length_append, List.length_singleton]
    · rw [readyEq] at growth
      exact growth

theorem BranchCopy.fixup_budget {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {index dst src count conditional copying condition guard}
    (effect : BranchCopy ops before after index dst src count conditional copying condition guard (.Ok ()))
    (law : Platform.AllocCorrect ops)
    (budget : FixupBudget before.frames.val before.function.code.val.length) :
    FixupBudget after.frames.val after.function.code.val.length := by
  unfold BranchCopy at effect
  split at effect
  · obtain ⟨answer, middle, called, rest⟩ := effect
    cases answer with
    | Err error => cases rest.1
    | Ok value =>
      cases value
      apply rest.fixup_budget law
      exact budget.ordinary (compiler_copy_ordinary_result ops before middle dst src count (.Ok ()) called)
        (compiler_copy_code_mono ops law before middle dst src count (.Ok ()) called)
  · exact effect.fixup_budget law budget

theorem BranchTransfer.fixup_budget {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {index dst src count conditional condition}
    (effect : BranchTransfer ops before after index dst src count conditional condition (.Ok ()))
    (law : Platform.AllocCorrect ops)
    (budget : FixupBudget before.frames.val before.function.code.val.length) :
    FixupBudget after.frames.val after.function.code.val.length := by
  dsimp only [BranchTransfer] at effect
  split at effect
  · obtain ⟨answer, middle, called, rest⟩ := effect
    cases answer with
    | Err error => cases rest.1
    | Ok value =>
      cases value
      apply rest.fixup_budget law
      exact budget.ordinary (compiler_emit_ordinary_result ops before middle _ (.Ok ()) called)
        (compiler_emit_code_mono ops law before middle _ (.Ok ()) called)
  · exact effect.fixup_budget law budget

theorem BranchCondition.fixup_budget {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {index dst src count conditional}
    (effect : BranchCondition ops before after index dst src count conditional (.Ok ()))
    (law : Platform.AllocCorrect ops)
    (budget : FixupBudget before.frames.val before.function.code.val.length) :
    FixupBudget after.frames.val after.function.code.val.length := by
  unfold BranchCondition at effect
  split at effect
  · obtain ⟨answer, _, rest⟩ := effect
    cases answer with
    | Err error => cases rest.1
    | Ok value => exact rest.fixup_budget law budget
  · exact effect.fixup_budget law budget

theorem BranchSource.fixup_budget {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {index frame skip conditional}
    (effect : BranchSource ops before after index frame skip conditional (.Ok ()))
    (law : Platform.AllocCorrect ops)
    (budget : FixupBudget before.frames.val before.function.code.val.length) :
    FixupBudget after.frames.val after.function.code.val.length := by
  obtain ⟨sum, _, rest⟩ := effect
  cases sum with
  | none => cases rest.1
  | some width =>
    obtain ⟨source, _, rest⟩ := rest
    cases source with
    | none => cases rest.1
    | some src => exact rest.fixup_budget law budget

theorem BranchEffect.fixup_budget {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {depth skip conditional}
    (effect : BranchEffect ops before after depth skip conditional (.Ok ()))
    (law : Platform.AllocCorrect ops)
    (budget : FixupBudget before.frames.val before.function.code.val.length) :
    FixupBudget after.frames.val after.function.code.val.length := by
  obtain ⟨_, _, _, _, _, _, _, _, rest⟩ := effect
  exact rest.fixup_budget law budget

theorem compiler_branch_fixup_budget {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (depth skip : U32) (conditional : Bool)
    (budget : FixupBudget before.frames.val before.function.code.val.length)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops before depth skip conditional = .ok (.Ok (), after)) :
    FixupBudget after.frames.val after.function.code.val.length := by
  exact (runtime.compiler.control.FunctionCompiler.branch.inv ops before after depth skip conditional
    (.Ok ()) accepted).fixup_budget law budget


end Itasca.Runtime.Compiler

end

/-! ## FixupElsePreservation -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts

set_option maxRecDepth 4096

/-- ELSE either keeps the current fixup vector or appends one site while
emitting its corresponding skip jump. -/
theorem compiler_else_fixup_budget {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (budget : FixupBudget before.frames.val before.function.code.val.length)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else
      ops before state bt = .ok (.Ok (), after)) :
    FixupBudget after.frames.val after.function.code.val.length := by
  have effect := runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else.inv ops before after state bt (.Ok ()) accepted
  rcases List.eq_nil_or_concat' before.frames.val with empty | ⟨prior, frame, frames⟩
  · cases effect with
    | selected nonempty subtracted read progress => simp only [empty, List.isEmpty_nil, Bool.true_eq_false] at nonempty
  · obtain ⟨index, restore, lastIndex, restoreEq, progress⟩ := effect.last_frame frame prior frames
    obtain ⟨fixups, appended, published, reachable, codeLength, sources, cursor⟩ := progress.success_fields law
    have finalFrames : after.frames.val = prior ++ [{frame with kind := .Else, if_pc := none, end_reachable := frame.end_reachable || before.reachable, fixups}] := by
      rw [published, restoreEq, alloc.vec.Vec.set_val_eq]
      simp only [frames, lastIndex, Std.le_refl, List.set_append_right, tsub_self, List.set_cons_zero]
    have selectedBudget := budget frame (by rw [frames]; exact List.mem_append_right _ (List.mem_cons_self))
    intro updated member
    rw [finalFrames] at member
    rcases List.mem_append.mp member with old | last
    · have bounded := budget updated (by rw [frames]; exact List.mem_append_left _ old)
      omega
    · simp only [List.mem_singleton] at last
      subst updated
      cases live : before.reachable <;> simp only [live, Bool.false_eq_true, ite_false, ite_true] at appended codeLength
      · rw [appended]
        exact selectedBudget.trans (by omega)
      · change fixups.val.length ≤ _
        rw [appended, List.length_append, List.length_singleton]
        omega

end Itasca.Runtime.Compiler

end

/-! ## ScopeFrameStart -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Actual compiler construction and function-start establish the root physical
frame, empty universally planned prefix, and initial source byte budget. -/
theorem compiler_function_start_scope {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (signatures : Slice runtime.compiler.Signature)
    (functionSlots : Slice U32) (budget : runtime.compiler.Budget A) (batchStart : Usize)
    (initial started : runtime.compiler.FunctionCompiler A)
    (ctx : Itasca.code.Context) (typeIndex : U32) (signature : runtime.compiler.Signature)
    (bodyBegin bodyEnd : Usize) (types functions : List functype) (returns : List valtype)
    (lookup : signatures.val[typeIndex.val]? = some signature)
    (resultWidth : signature.result_slots.val = slots returns)
    (beginFits : batchStart.val + bodyBegin.val ≤ Usize.max)
    (endFits : batchStart.val + bodyEnd.val ≤ Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart = .ok initial)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start
      ops initial ctx typeIndex bodyBegin bodyEnd = .ok (.Ok (), started)) :
    ∃ frame, started.frames.val = [frame] ∧
      FrameScope (ctx.locals.val.map Itasca.Translate.valueType) started (SourceScope.initial returns) frame ∧
      UniversalPrefix started types functions returns (ctx.locals.val.map Itasca.Translate.valueType)
        [] (SourceScope.initial returns) [] ∧
      UniversalElse started types functions returns (ctx.locals.val.map Itasca.Translate.valueType)
        [] (SourceScope.initial returns) ∧
      SourceCodeBudget started 0 ∧ SourceControlBudget started 0 ∧
      ScopeFrameStack (ctx.locals.val.map Itasca.Translate.valueType) started [] (SourceScope.initial returns) ∧
      started.reachable = true := by
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
  let frame : runtime.compiler.Frame :=
    ⟨0#usize, .Body, started.function.local_slots, 0#u32, signature.result_slots,
      0#u32, none, true, false, alloc.vec.Vec.new Usize⟩
  have frameEq : started.frames.val = [frame] := by simpa [emptyFrames, frame] using framesEq
  have localEq : compilerLocals started = ctx.locals.val.map Itasca.Translate.valueType := by
    simp only [compilerLocals, localTypes]
  have codeEmpty : started.function.code.val = [] := by rw [codeEq, emptyCode]
  have mapPresent : 0 < started.function.controls.val.length := by simp [mapsEq]
  have frameShape : FrameScope (ctx.locals.val.map Itasca.Translate.valueType) started
      (SourceScope.initial returns) frame :=
    FrameScope.initial _ _ started _ _ (by simpa only [localEq] using layout.localSlots)
      resultWidth mapPresent
  refine ⟨frame, frameEq, frameShape, ?_, UniversalElse.initial _ _ _ _ _,
    SourceCodeBudget.initial codeEmpty, ?_, .initial frame frameEq frameShape, live.trans reachable⟩
  · exact UniversalPrefix.initial started types functions returns _ frame codeEmpty frameEq rfl
      (by simp [frame, alloc.vec.Vec.new]) localEq layout
  · exact SourceControlBudget.initial (by simp [mapsEq, emptyMaps]) (by simp [frameEq])
end Itasca.Runtime.Compiler

end
