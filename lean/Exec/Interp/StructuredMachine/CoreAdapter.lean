import Exec.Code.Local.Control.Table.StructuredCodeTableExclusion
import Exec.Interp.StructuredMachine.Embedding
import Exec.Interp.Core.Execution
namespace Exec.Interp.StructuredMachine.CoreAdapter
open Aeneas.Std

theorem point_iff {s raw source compiled C targets next output} :
    CoreFramePoint s raw source compiled C targets next output ↔
    FramePoint (fun _ => Code.CoreEmission) s raw source compiled C targets next output := by
  constructor
  · rintro ⟨a,b,c,d⟩
    exact ⟨a,b,c,d.with_tables compiled.jump_tables.val (fun _ _ _ _ h => h.not_branchTable)⟩
  · rintro ⟨a,b,c,d⟩
    exact ⟨a,b,c,d.to_old (fun _ depths fallback _ _ _ h => h.not_branchTable depths fallback rfl)⟩

theorem suspended_iff {s raw source compiled C targets next output waiting} :
    CoreSuspendedFramePoint s raw source compiled C targets next output waiting ↔
    SuspendedFramePoint (fun _ => Code.CoreEmission) s raw source compiled C targets next output waiting := by
  constructor
  · rintro ⟨a,b,c,d⟩
    exact ⟨a,b,c,d.with_tables compiled.jump_tables.val (fun _ _ _ _ h => h.not_branchTable)⟩
  · rintro ⟨a,b,c,d⟩
    exact ⟨a,b,c,d.to_old (fun _ depths fallback _ _ _ h => h.not_branchTable depths fallback rfl)⟩

theorem control_iff {s raw source compiled C targets next output pending} :
    CoreControlPoint s raw source compiled C targets next output pending ↔
    ControlPoint (fun _ => Code.CoreEmission) s raw source compiled C targets next output pending := by
  constructor
  · intro h; cases h with
    | ready h => exact .ready (point_iff.mp h)
    | jump target fetched h => exact .jump target fetched (point_iff.mp h)
  · intro h; cases h with
    | ready h => exact .ready (point_iff.mpr h)
    | jump target fetched h => exact .jump target fetched (point_iff.mpr h)

theorem saved_frame_iff {M : Type} {store : runtime.store.Store M} {s exec raw source waiting base} :
    CoreSavedFrame store s exec raw source waiting base ↔
    SavedFrame (fun _ => Code.CoreEmission) store s exec raw source waiting base := by
  constructor
  · rintro ⟨binding,slots,destination,compiled,C,targets,next,output,program,point⟩
    exact ⟨binding,slots,destination,compiled,C,targets,next,output,program,suspended_iff.mp point⟩
  · rintro ⟨binding,slots,destination,compiled,C,targets,next,output,program,point⟩
    exact ⟨binding,slots,destination,compiled,C,targets,next,output,program,suspended_iff.mpr point⟩

theorem saved_iff {M : Type} {store : runtime.store.Store M} {s exec raws sources waiting base} :
    CoreSavedFrames store s exec raws sources waiting base ↔
    SavedFrames (fun _ => Code.CoreEmission) store s exec raws sources waiting base := by
  constructor
  · intro h; induction h with
    | nil => exact .nil _
    | cons head tail ih => exact .cons (saved_frame_iff.mp head) ih
  · intro h; induction h with
    | nil => exact .nil _
    | cons head tail ih => exact .cons (saved_frame_iff.mpr head) ih

theorem active_iff {M : Type} {store : runtime.store.Store M} {s exec raw source} :
    CoreActiveFrame store s exec raw source ↔ ActiveFrame (fun _ => Code.CoreEmission) store s exec raw source := by
  constructor
  · rintro ⟨binding,slots,compiled,C,targets,next,output,pending,program,point⟩
    exact ⟨binding,slots,compiled,C,targets,next,output,pending,program,control_iff.mp point⟩
  · rintro ⟨binding,slots,compiled,C,targets,next,output,pending,program,point⟩
    exact ⟨binding,slots,compiled,C,targets,next,output,pending,program,control_iff.mpr point⟩

theorem stack_iff {M : Type} {store : runtime.store.Store M} {s exec sources} :
    CoreFrameStackRel store s exec sources ↔ FrameStackRel (fun _ => Code.CoreEmission) store s exec sources := by
  constructor
  · intro h; cases h with
    | empty frames => exact .empty frames
    | active frames top saved => exact .active frames (active_iff.mp top) (saved_iff.mp saved)
  · intro h; cases h with
    | empty frames => exact .empty frames
    | active frames top saved => exact .active frames (active_iff.mpr top) (saved_iff.mpr saved)

theorem cursor_iff {M : Type} {store : runtime.store.Store M} {exec source pc pending} :
    CoreExecutionCursor store exec source pc pending ↔ ExecutionCursor (fun _ => Code.CoreEmission) store exec source pc pending := by
  cases frames : source.frames with
  | nil => simp only [CoreExecutionCursor,ExecutionCursor,frames]
  | cons frame rest =>
    simp only [CoreExecutionCursor,ExecutionCursor,frames,CoreControlTop,ControlTop]
    constructor
    · rintro ⟨raw,compiled,C,targets,next,output,top,position,program,point⟩
      exact ⟨raw,compiled,C,targets,next,output,top,position,program,control_iff.mp point⟩
    · rintro ⟨raw,compiled,C,targets,next,output,top,position,program,point⟩
      exact ⟨raw,compiled,C,targets,next,output,top,position,program,control_iff.mpr point⟩

theorem execution_iff {M : Type} {view : M → Slice U8} {code : Store.CodeInterpretation}
    {store : runtime.store.Store M} {exec source expected pc pending} :
    CoreExecution view code store exec source expected pc pending ↔
    Execution (fun _ => Code.CoreEmission) Abs.CoreState view code store exec source expected pc pending := by
  constructor
  · rintro ⟨same,typed,covered,result,stack,cursor⟩
    exact ⟨same,typed,covered,result,stack_iff.mp stack,cursor_iff.mp cursor⟩
  · rintro ⟨same,typed,covered,result,stack,cursor⟩
    exact ⟨same,typed,covered,result,stack_iff.mpr stack,cursor_iff.mpr cursor⟩
end Exec.Interp.StructuredMachine.CoreAdapter
