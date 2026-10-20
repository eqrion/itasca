import Exec.Theorems.Host.Open.Source.State.SavedCaller
import Exec.Theorems.Host.Open.Source.Control.Actions
import Exec.Theorems.Host.Open.Driver.DriverGuard
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std Exec.Interp

/-- Saved host control keeps immutable code and copied owned arguments. Saved
Wasm control keeps its particular source request and native continuation. -/
inductive SourceFrame {M : Type} (memory : runtime.platform.MemoryBuffer M) (view : M → Slice U8)
    (code : Store.CodeInterpretation) (store : runtime.store.Store M) :
    Continuation → Spec.OpenExecution.Continuation SourceControl → Prop
  | host (raw : HostState) (next : Nat) (source : SourceHostState)
      (represented : HostStateRepresents store.id source raw) :
      SourceFrame memory view code store (.host raw next) (.host (.active {source with pc:=next}))
  | wasm (exec : runtime.interp.Execution) (address : runtime.FuncAddr) (base : Usize)
      (root : runtime.FuncAddr) (results : alloc.vec.Vec runtime.Value) (suspended : Spec.OpenExecution.Suspension)
      (saved : SourceSavedCaller memory view code store exec address base root suspended) :
      SourceFrame memory view code store (.wasm exec address base root results) (.wasm suspended)

theorem SourceFrame.extend {M : Type} {memory : runtime.platform.MemoryBuffer M} {view : M → Slice U8}
    {code afterCode : Store.CodeInterpretation} {store after : runtime.store.Store M}
    {native : Continuation} {source : Spec.OpenExecution.Continuation SourceControl}
    (frame : SourceFrame memory view code store native source)
    (effect : ReentrantCallbacks.Effect view code store afterCode after) :
    SourceFrame memory view afterCode after native source := by
  cases frame with
  | host raw next source represented=>
    apply SourceFrame.host
    have identical : after.id=store.id:=effect.metadata.identity
    rw [identical]
    exact represented
  | wasm exec address base root results suspended saved=>exact .wasm exec address base root results suspended (saved.extend effect)

inductive SourceStack {M : Type} (memory : runtime.platform.MemoryBuffer M) (view : M → Slice U8)
    (code : Store.CodeInterpretation) (store : runtime.store.Store M) :
    List Continuation → List (Spec.OpenExecution.Continuation SourceControl) → Prop
  | nil : SourceStack memory view code store [] []
  | cons {native source rest tail}
      (head : SourceFrame memory view code store native source)
      (more : SourceStack memory view code store rest tail) :
      SourceStack memory view code store (native::rest) (source::tail)

theorem SourceStack.extend {M : Type} {memory : runtime.platform.MemoryBuffer M} {view : M → Slice U8}
    {code afterCode : Store.CodeInterpretation} {store after : runtime.store.Store M}
    {native : List Continuation} {source : List (Spec.OpenExecution.Continuation SourceControl)}
    (stack : SourceStack memory view code store native source)
    (effect : ReentrantCallbacks.Effect view code store afterCode after) :
    SourceStack memory view afterCode after native source := by
  induction stack with
  | nil=>exact .nil
  | cons head more ih=>exact .cons (head.extend effect) ih

theorem SourceStack.native {M : Type} {memory : runtime.platform.MemoryBuffer M} {view : M → Slice U8}
    {code : Store.CodeInterpretation} {store : runtime.store.Store M}
    {native : List Continuation} {source : List (Spec.OpenExecution.Continuation SourceControl)}
    (stack : SourceStack memory view code store native source) : StackGuard memory view code store native := by
  induction stack with
  | nil=>trivial
  | cons head more ih=>
    cases head with
    | host raw next source represented=>exact ih
    | wasm exec address base root results suspended saved=>
      obtain ⟨signature,metadata,expected,task⟩ := saved.task
      exact ⟨⟨signature,task⟩,ih⟩

theorem SourceStack.typed {M : Type} {memory : runtime.platform.MemoryBuffer M} {view : M → Slice U8}
    {code : Store.CodeInterpretation} {store : runtime.store.Store M}
    {native : List Continuation} {source : List (Spec.OpenExecution.Continuation SourceControl)}
    (stack : SourceStack memory view code store native source) :
    Spec.OpenExecution.StackTyped (Store.decodeStore view code store) source := by
  induction stack with
  | nil=>trivial
  | cons head more ih=>
    cases head with
    | host raw next source represented=>exact ih
    | wasm exec address base root results suspended saved=>exact ⟨saved.source_extension,ih⟩
end Exec.Theorems.OpenReentrantControl
