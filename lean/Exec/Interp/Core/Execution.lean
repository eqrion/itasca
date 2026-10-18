import Exec.Interp.Core.FrameStack
import Exec.Interp.Machines.Slice.SliceExecution
import Exec.Abs.Core.Typing
import Exec.Abs.Core
namespace Exec.Interp
open Aeneas Aeneas.Std

def CoreControlTop {M : Type} (store : runtime.store.Store M) (sourceStore : _root_.store)
    (exec : runtime.interp.Execution) (source : Abs.AFrame) (pc : Nat) (pending : Bool) : Prop :=
  ∃ raw compiled C targets next output,
    exec.frames.val.getLast? = some raw ∧ raw.pc.val = pc ∧
    FrameProgram store raw compiled (source.locals.map Code.valueType) source.resultTypes C.FUNCS ∧
    CoreControlPoint sourceStore raw source compiled C targets next output pending

def CoreExecutionCursor {M : Type} (store : runtime.store.Store M) (exec : runtime.interp.Execution)
    (source : Abs.AState) (pc : Nat) (pending : Bool) : Prop :=
  match source.frames with
  | [] => pc = 0 ∧ pending = false ∧ ValuesAt exec.slots.val 0 source.results
  | frame :: _ => CoreControlTop store source.store exec frame pc pending

/-- The mutable machine relates the current concrete store, complete source
state and all active/suspended compiled frames. Store identity is not confused
with equality of the changing object payloads. -/
structure CoreExecution {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (exec : runtime.interp.Execution)
    (source : Abs.AState) (expected : List valtype) (pc : Nat) (pending : Bool) : Prop where
  storeEq : source.store = Store.decodeStore view code store
  typed : Abs.CoreTyped source
  core : Abs.CoreState source
  result : Abs.InvocationResult expected source
  stack : CoreFrameStackRel store source.store exec source.frames
  cursor : CoreExecutionCursor store exec source pc pending

theorem CoreFrameStackRel.top {M : Type} {store : runtime.store.Store M} {sourceStore : _root_.store}
    {exec : runtime.interp.Execution} {source : Abs.AFrame} {rest : List Abs.AFrame}
    (relation : CoreFrameStackRel store sourceStore exec (source :: rest))
    (raw : runtime.interp.Frame) (top : exec.frames.val.getLast? = some raw) :
    CoreActiveFrame store sourceStore exec raw source := by
  cases relation with
  | active frames active saved =>
    have same := top
    simp only [frames,List.getLast?_concat,Option.some.injEq] at same
    subst raw
    exact active

theorem CoreControlTop.pc {M : Type} {store : runtime.store.Store M} {sourceStore : _root_.store}
    {exec : runtime.interp.Execution} {source : Abs.AFrame} {pc : Nat} {pending : Bool}
    (cursor : CoreControlTop store sourceStore exec source pc pending) :
    (exec.frames.val.getLast?).map (fun raw => raw.pc.val) = some pc := by
  obtain ⟨raw,compiled,C,targets,next,output,top,same,program,point⟩ := cursor
  simp only [top,Option.map_some,same]

theorem CoreControlTop.updated {M : Type} {store : runtime.store.Store M} {sourceStore : _root_.store}
    {exec : runtime.interp.Execution} {raw : runtime.interp.Frame}
    {compiled : runtime.bytecode.CompiledFunction} {C : context}
    {before after : Abs.AFrame} {pc : U32} {pending : Bool}
    (top : exec.frames.val.getLast? = some {raw with pc := pc})
    (program : FrameProgram store raw compiled (before.locals.map Code.valueType) before.resultTypes C.FUNCS)
    (metadata : FrameMetadata before after)
    (point : ∃ targets next output, CoreControlPoint sourceStore {raw with pc := pc} after compiled C targets next output pending) :
    CoreControlTop store sourceStore exec after pc.val pending := by
  obtain ⟨targets,next,output,point⟩ := point
  exact ⟨{raw with pc := pc},compiled,C,targets,next,output,top,rfl,program.reposition pc metadata,point⟩

theorem CoreReadyTop.cursor {M : Type} {store : runtime.store.Store M} {sourceStore : _root_.store}
    {exec : runtime.interp.Execution} {source : Abs.AFrame}
    (ready : CoreReadyTop store sourceStore exec source) : ∃ pc, CoreControlTop store sourceStore exec source pc false := by
  obtain ⟨raw,compiled,C,targets,next,output,top,program,point⟩ := ready
  exact ⟨raw.pc.val,raw,compiled,C,targets,next,output,top,rfl,program,.ready point⟩

theorem CoreReadyState.cursor {M : Type} {store : runtime.store.Store M}
    {exec : runtime.interp.Execution} {source : Abs.AState}
    (ready : CoreReadyState store exec source) : ∃ pc, CoreExecutionCursor store exec source pc false := by
  cases frames : source.frames with
  | nil => exact ⟨0,by simpa only [CoreExecutionCursor,CoreReadyState,frames,true_and] using ready⟩
  | cons frame rest =>
    simp only [CoreReadyState,frames] at ready
    obtain ⟨pc,cursor⟩ := ready.cursor
    exact ⟨pc,by simpa only [CoreExecutionCursor,frames] using cursor⟩
end Exec.Interp
