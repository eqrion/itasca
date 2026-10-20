import Exec.Code.Local.Relations.Common.FunctionEntry
import Exec.Code.Local.Publication.ControlMapPublication

namespace Exec.Code
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

end Exec.Code
