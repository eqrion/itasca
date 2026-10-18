import Exec.Interp.Relations.StackRelation
import Exec.Abs.Results

namespace Exec.Interp
open Aeneas Aeneas.Std

/-- The execution cursor identifies the actual top frame and distinguishes
an instruction boundary from the pending jump after a branch transfer. -/
def ControlTop {M : Type} (store : runtime.store.Store M) (exec : runtime.interp.Execution)
    (source : Abs.AFrame) (pc : Nat) (pending : Bool) : Prop :=
  ∃ raw compiled functions targets next output,
    exec.frames.val.getLast? = some raw ∧ raw.pc.val = pc ∧
    FrameProgram store raw compiled (source.locals.map Code.valueType) source.resultTypes functions ∧
    ControlPoint raw source compiled functions targets next output pending

/-- At completion, slot zero retains the returned values. At an active source
frame, the cursor is attached to that frame's actual concrete program counter. -/
def ExecutionCursor {M : Type} (store : runtime.store.Store M) (exec : runtime.interp.Execution)
    (source : Abs.AState) (pc : Nat) (pending : Bool) : Prop :=
  match source.frames with
  | [] => pc = 0 ∧ pending = false ∧ ValuesAt exec.slots.val 0 source.results
  | frame :: _ => ControlTop store exec frame pc pending

structure SliceExecution {M : Type} (store : runtime.store.Store M) (exec : runtime.interp.Execution)
    (source : Abs.AState) (expected : List valtype) (pc : Nat) (pending : Bool) : Prop where
  typed : Abs.ATyped source
  slice : Abs.SliceState source
  result : Abs.InvocationResult expected source
  stack : FrameStackRel store exec source.frames
  cursor : ExecutionCursor store exec source pc pending

theorem FrameStackRel.top {M : Type} {store : runtime.store.Store M}
    {exec : runtime.interp.Execution} {source : Abs.AFrame} {rest : List Abs.AFrame}
    (relation : FrameStackRel store exec (source :: rest))
    (raw : runtime.interp.Frame) (top : exec.frames.val.getLast? = some raw) :
    ActiveFrame store exec raw source := by
  cases relation with
  | active frames active saved =>
    have same := top
    simp only [frames, List.getLast?_concat, Option.some.injEq] at same
    subst raw
    exact active

theorem FrameMetadata.result {before after : Abs.AFrame} (metadata : FrameMetadata before after)
    (s : _root_.store) (ambient : frame) (rest : List Abs.AFrame) (expected : List valtype)
    (result : Abs.InvocationResult expected ⟨s, ambient, before :: rest, []⟩) :
    Abs.InvocationResult expected ⟨s, ambient, after :: rest, []⟩ :=
  Abs.FramesReturn.replace result metadata.results

theorem ControlTop.pc {M : Type} {store : runtime.store.Store M}
    {exec : runtime.interp.Execution} {source : Abs.AFrame} {pc : Nat} {pending : Bool}
    (cursor : ControlTop store exec source pc pending) :
    (exec.frames.val.getLast?).map (fun raw => raw.pc.val) = some pc := by
  obtain ⟨raw, compiled, functions, targets, next, output, top, same, program, point⟩ := cursor
  simp only [top, Option.map_some, same]

theorem FrameProgram.reposition {M : Type} {store : runtime.store.Store M}
    {raw : runtime.interp.Frame} {compiled : runtime.bytecode.CompiledFunction}
    {before after : Abs.AFrame} {functions : List functype}
    (program : FrameProgram store raw compiled (before.locals.map Code.valueType) before.resultTypes functions)
    (pc : U32) (metadata : FrameMetadata before after) :
    FrameProgram store { raw with pc := pc } compiled (after.locals.map Code.valueType) after.resultTypes functions := by
  exact ⟨program.lookup, program.checked, program.fetchBound,
    program.localSlots.trans (congrArg Code.slots metadata.locals).symm,
    by simpa only [metadata.results] using program.epilogue⟩

theorem ControlTop.updated {M : Type} {store : runtime.store.Store M}
    {exec : runtime.interp.Execution} {raw : runtime.interp.Frame}
    {compiled : runtime.bytecode.CompiledFunction} {functions : List functype}
    {before after : Abs.AFrame} {pc : U32} {pending : Bool}
    (top : exec.frames.val.getLast? = some { raw with pc := pc })
    (program : FrameProgram store raw compiled (before.locals.map Code.valueType) before.resultTypes functions)
    (metadata : FrameMetadata before after)
    (point : ∃ targets next output, ControlPoint { raw with pc := pc } after compiled functions targets next output pending) :
    ControlTop store exec after pc.val pending := by
  obtain ⟨targets, next, output, point⟩ := point
  exact ⟨{ raw with pc := pc }, compiled, functions, targets, next, output, top, rfl,
    program.reposition pc metadata, point⟩

theorem ReadyTop.cursor {M : Type} {store : runtime.store.Store M}
    {exec : runtime.interp.Execution} {source : Abs.AFrame}
    (ready : ReadyTop store exec source) : ∃ pc, ControlTop store exec source pc false := by
  obtain ⟨raw, compiled, functions, targets, next, output, top, program, point⟩ := ready
  exact ⟨raw.pc.val, raw, compiled, functions, targets, next, output, top, rfl, program, .ready point⟩

theorem ReadyState.cursor {M : Type} {store : runtime.store.Store M}
    {exec : runtime.interp.Execution} {source : Abs.AState}
    (ready : ReadyState store exec source) : ∃ pc, ExecutionCursor store exec source pc false := by
  cases frames : source.frames with
  | nil => exact ⟨0, by simpa only [ExecutionCursor, ReadyState, frames, true_and] using ready⟩
  | cons f rest =>
    simp only [ReadyState, frames] at ready
    obtain ⟨pc, cursor⟩ := ready.cursor
    exact ⟨pc, by simpa only [ExecutionCursor, frames] using cursor⟩

theorem ReadyTop.cursor_at {M : Type} {store : runtime.store.Store M}
    {exec : runtime.interp.Execution} {source : Abs.AFrame} {pc : U32}
    (ready : ReadyTop store exec source)
    (position : (exec.frames.val.getLast?).map (fun raw => raw.pc) = some pc) :
    ControlTop store exec source pc.val false := by
  obtain ⟨raw, compiled, functions, targets, next, output, top, program, point⟩ := ready
  have same : raw.pc = pc := by simpa only [top, Option.map_some, Option.some.injEq] using position
  exact ⟨raw, compiled, functions, targets, next, output, top, congrArg UScalar.val same, program, .ready point⟩

theorem ReadyState.cursor_at {M : Type} {store : runtime.store.Store M}
    {exec : runtime.interp.Execution} {source : Abs.AState} {pc : U32}
    (ready : ReadyState store exec source) (stack : FrameStackRel store exec source.frames)
    (position : (exec.frames.val.getLast?).map (fun raw => raw.pc) = some pc) :
    ExecutionCursor store exec source pc.val false := by
  cases frames : source.frames with
  | nil =>
    rw [frames] at stack
    cases stack with
    | empty empty => simp [empty] at position
  | cons f rest =>
    simp only [ReadyState, frames] at ready
    simpa only [ExecutionCursor, frames] using ready.cursor_at position

end Exec.Interp
