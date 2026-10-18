import Exec.Interp.StructuredMachine.Execution
namespace Exec.Interp.StructuredMachine
open Aeneas.Std

/-- Checked inclusion of emitted syntax retains every static context unchanged. -/
def EmissionEmbedding (before after : FunctionEmission) : Prop :=
  ∀ compiled C input instruction emitted output, before compiled C input instruction emitted output → after compiled C input instruction emitted output

variable {before after : FunctionEmission}

theorem FramePoint.map_emission (embed : EmissionEmbedding before after)
    {sourceStore raw source compiled C targets next output}
    (point : FramePoint before sourceStore raw source compiled C targets next output) :
    FramePoint after sourceStore raw source compiled C targets next output :=
  ⟨point.bindings,point.locals,point.labels,point.code.map_emission (embed compiled C)⟩

theorem SuspendedFramePoint.map_emission (embed : EmissionEmbedding before after)
    {sourceStore raw source compiled C targets next output waiting}
    (point : SuspendedFramePoint before sourceStore raw source compiled C targets next output waiting) :
    SuspendedFramePoint after sourceStore raw source compiled C targets next output waiting :=
  ⟨point.bindings,point.locals,point.labels,point.code.map_emission (embed compiled C)⟩

theorem ControlPoint.map_emission (embed : EmissionEmbedding before after)
    {sourceStore raw source compiled C targets next output pending}
    (point : ControlPoint before sourceStore raw source compiled C targets next output pending) :
    ControlPoint after sourceStore raw source compiled C targets next output pending := by
  cases point with
  | ready point => exact .ready (point.map_emission embed)
  | jump target fetched point => exact .jump target fetched (point.map_emission embed)

theorem SavedFrame.map_emission (embed : EmissionEmbedding before after)
    {M : Type} {store : runtime.store.Store M} {sourceStore exec raw source waiting base}
    (saved : SavedFrame before store sourceStore exec raw source waiting base) :
    SavedFrame after store sourceStore exec raw source waiting base := by
  refine ⟨saved.binding,saved.slots,saved.destination,?_⟩
  obtain ⟨compiled,C,targets,next,output,program,point⟩ := saved.continuation
  exact ⟨compiled,C,targets,next,output,program,point.map_emission embed⟩

theorem SavedFrames.map_emission (embed : EmissionEmbedding before after)
    {M : Type} {store : runtime.store.Store M} {sourceStore exec raws sources waiting base}
    (saved : SavedFrames before store sourceStore exec raws sources waiting base) :
    SavedFrames after store sourceStore exec raws sources waiting base := by
  induction saved with
  | nil => exact .nil _
  | cons head tail ih => exact .cons (head.map_emission embed) ih

theorem ActiveFrame.map_emission (embed : EmissionEmbedding before after)
    {M : Type} {store : runtime.store.Store M} {sourceStore exec raw source}
    (active : ActiveFrame before store sourceStore exec raw source) :
    ActiveFrame after store sourceStore exec raw source := by
  refine ⟨active.binding,active.slots,?_⟩
  obtain ⟨compiled,C,targets,next,output,pending,program,point⟩ := active.continuation
  exact ⟨compiled,C,targets,next,output,pending,program,point.map_emission embed⟩

theorem FrameStackRel.map_emission (embed : EmissionEmbedding before after)
    {M : Type} {store : runtime.store.Store M} {sourceStore exec sources}
    (stack : FrameStackRel before store sourceStore exec sources) :
    FrameStackRel after store sourceStore exec sources := by
  cases stack with
  | empty frames => exact .empty frames
  | active frames top saved => exact .active frames (top.map_emission embed) (saved.map_emission embed)

theorem ExecutionCursor.map_emission (embed : EmissionEmbedding before after)
    {M : Type} {store : runtime.store.Store M} {exec source pc pending}
    (cursor : ExecutionCursor before store exec source pc pending) :
    ExecutionCursor after store exec source pc pending := by
  cases frames : source.frames with
  | nil => simpa only [ExecutionCursor,frames] using cursor
  | cons frame rest =>
    simp only [ExecutionCursor,frames] at cursor ⊢
    obtain ⟨raw,compiled,C,targets,next,output,top,position,program,point⟩ := cursor
    exact ⟨raw,compiled,C,targets,next,output,top,position,program,point.map_emission embed⟩

theorem Execution.map_emission (embed : EmissionEmbedding before after)
    {oldSupported newSupported : Abs.AState → Prop}
    (covered : ∀ source, oldSupported source → newSupported source)
    {M : Type} {view : M → Slice U8} {code : Store.CodeInterpretation}
    {store : runtime.store.Store M} {exec source expected pc pending}
    (machine : Execution before oldSupported view code store exec source expected pc pending) :
    Execution after newSupported view code store exec source expected pc pending :=
  ⟨machine.storeEq,machine.typed,covered source machine.core,machine.result,
    machine.stack.map_emission embed,machine.cursor.map_emission embed⟩
end Exec.Interp.StructuredMachine
