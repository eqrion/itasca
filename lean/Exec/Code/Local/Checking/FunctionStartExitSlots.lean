import Exec.Code.Local.Checking.FrameExitSlotBounds

namespace Exec.Code
open Aeneas Aeneas.Std

/-- Actual fresh construction and function-start introduce only the root frame,
whose forward-exit flag is initially clear. -/
theorem compiler_start_exit_slots {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (signatures : Slice runtime.compiler.Signature)
    (functionSlots : Slice U32) (budget : runtime.compiler.Budget A) (batchStart : Usize)
    (initial started : runtime.compiler.FunctionCompiler A)
    (ctx : Itasca.code.Context) (typeIndex : U32) (signature : runtime.compiler.Signature)
    (bodyBegin bodyEnd : Usize)
    (lookup : signatures.val[typeIndex.val]? = some signature)
    (beginFits : batchStart.val+bodyBegin.val ≤ Usize.max)
    (endFits : batchStart.val+bodyEnd.val ≤ Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart = .ok initial)
    (begun : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start
      ops initial ctx typeIndex bodyBegin bodyEnd = .ok (.Ok (),started)) : FrameExitSlotBounds started := by
  have newPost := compiler_new ops signatures functionSlots budget batchStart
  rw [created,WP.spec_ok] at newPost
  obtain ⟨layout,emptyLocals,emptyOperands,emptyMaps,emptyFrames,emptyCode,reachable,sigs,widths,coordinate⟩ := newPost
  have startPost := compiler_function_start_raw ops law initial ctx typeIndex signature bodyBegin bodyEnd
    (by simpa only [sigs] using lookup) (by simpa only [coordinate] using beginFits)
    (by simpa only [coordinate] using endFits) emptyLocals layout emptyOperands
    (by simp [emptyMaps]; scalar_tac) (by simp [emptyFrames]; scalar_tac)
  rw [begun,WP.spec_ok] at startPost
  obtain ⟨_,_,frames,_⟩ := startPost rfl
  intro frame member live
  rw [frames,emptyFrames,List.nil_append] at member
  have same := List.mem_singleton.mp member
  subst frame
  simp at live

end Exec.Code
