import Exec.Code.Local.Callbacks.Control.ScopeFrameStack
import Exec.Code.Local.Relations.Common.FunctionEntry
import Exec.Code.Local.Source.SourceControlBudget
namespace Itasca.Runtime.Code
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
end Itasca.Runtime.Code
