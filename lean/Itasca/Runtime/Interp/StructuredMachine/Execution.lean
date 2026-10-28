import Itasca.Runtime.Interp.StructuredMachine.FrameStack
import Itasca.Runtime.Interp.Machines.Slice.SliceExecution
import Itasca.Runtime.Abs.Core.Typing
import Itasca.Runtime.Abs.SupportedState
namespace Itasca.Runtime.Interp.StructuredMachine
open Aeneas Aeneas.Std

def ControlTop {M : Type} (store : runtime.store.Store M) (sourceStore : _root_.store)
    (exec : runtime.interp.Execution) (source : Abs.AFrame) (pc : Nat) (pending : Bool) : Prop :=
  ∃ raw compiled C targets next output,
    exec.frames.val.getLast? = some raw ∧ raw.pc.val = pc ∧
    FrameProgram store raw compiled (source.locals.map Code.valueType) source.resultTypes C.FUNCS ∧
    ControlPoint sourceStore raw source compiled C targets next output pending

def ExecutionCursor {M : Type} (store : runtime.store.Store M) (exec : runtime.interp.Execution)
    (source : Abs.AState) (pc : Nat) (pending : Bool) : Prop :=
  match source.frames with
  | [] => pc = 0 ∧ pending = false ∧ ValuesAt exec.slots.val 0 source.results
  | frame :: _ => ControlTop store source.store exec frame pc pending

/-- The mutable machine relates the current concrete store, complete source
state and all active/suspended compiled frames. Store identity is not confused
with equality of the changing object payloads. -/
structure Execution {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (exec : runtime.interp.Execution)
    (source : Abs.AState) (expected : List valtype) (pc : Nat) (pending : Bool) : Prop where
  storeEq : source.store = Store.decodeStore view code store
  typed : Abs.CoreTyped source
  core : Abs.SupportedState source
  result : Abs.InvocationResult expected source
  stack : FrameStackRel store source.store exec source.frames
  cursor : ExecutionCursor store exec source pc pending

theorem FrameStackRel.top {M : Type} {store : runtime.store.Store M} {sourceStore : _root_.store}
    {exec : runtime.interp.Execution} {source : Abs.AFrame} {rest : List Abs.AFrame}
    (relation : FrameStackRel store sourceStore exec (source :: rest))
    (raw : runtime.interp.Frame) (top : exec.frames.val.getLast? = some raw) :
    ActiveFrame store sourceStore exec raw source := by
  cases relation with
  | active frames active saved =>
    have same := top
    simp only [frames,List.getLast?_concat,Option.some.injEq] at same
    subst raw
    exact active

theorem ControlTop.pc {M : Type} {store : runtime.store.Store M} {sourceStore : _root_.store}
    {exec : runtime.interp.Execution} {source : Abs.AFrame} {pc : Nat} {pending : Bool}
    (cursor : ControlTop store sourceStore exec source pc pending) :
    (exec.frames.val.getLast?).map (fun raw => raw.pc.val) = some pc := by
  obtain ⟨raw,compiled,C,targets,next,output,top,same,program,point⟩ := cursor
  simp only [top,Option.map_some,same]

theorem ControlTop.updated {M : Type} {store : runtime.store.Store M} {sourceStore : _root_.store}
    {exec : runtime.interp.Execution} {raw : runtime.interp.Frame}
    {compiled : runtime.bytecode.CompiledFunction} {C : context}
    {before after : Abs.AFrame} {pc : U32} {pending : Bool}
    (top : exec.frames.val.getLast? = some {raw with pc := pc})
    (program : FrameProgram store raw compiled (before.locals.map Code.valueType) before.resultTypes C.FUNCS)
    (metadata : FrameMetadata before after)
    (point : ∃ targets next output, ControlPoint sourceStore {raw with pc := pc} after compiled C targets next output pending) :
    ControlTop store sourceStore exec after pc.val pending := by
  obtain ⟨targets,next,output,point⟩ := point
  exact ⟨{raw with pc := pc},compiled,C,targets,next,output,top,rfl,program.reposition pc metadata,point⟩

theorem ReadyTop.cursor {M : Type} {store : runtime.store.Store M} {sourceStore : _root_.store}
    {exec : runtime.interp.Execution} {source : Abs.AFrame}
    (ready : ReadyTop store sourceStore exec source) : ∃ pc, ControlTop store sourceStore exec source pc false := by
  obtain ⟨raw,compiled,C,targets,next,output,top,program,point⟩ := ready
  exact ⟨raw.pc.val,raw,compiled,C,targets,next,output,top,rfl,program,.ready point⟩

theorem ReadyState.cursor {M : Type} {store : runtime.store.Store M}
    {exec : runtime.interp.Execution} {source : Abs.AState}
    (ready : ReadyState store exec source) : ∃ pc, ExecutionCursor store exec source pc false := by
  cases frames : source.frames with
  | nil => exact ⟨0,by simpa only [ExecutionCursor,ReadyState,frames,true_and] using ready⟩
  | cons frame rest =>
    simp only [ReadyState,frames] at ready
    obtain ⟨pc,cursor⟩ := ready.cursor
    exact ⟨pc,by simpa only [ExecutionCursor,frames] using cursor⟩
end Itasca.Runtime.Interp.StructuredMachine
