import Exec.Theorems.Host.Open.Source.State.Stack
import Exec.Theorems.Host.Open.Source.State.RootInvoke
import Exec.Theorems.Host.Open.Source.State.Metadata
import Exec.Theorems.Host.Open.Source.State.Observations
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall

/-- Each active native mode keeps its particular source control/configuration.
The rank counts only administrative work that may leave the source unchanged. -/
inductive SourceMode {M A : Type} (memory : runtime.platform.MemoryBuffer M) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) : Store.CodeInterpretation → runtime.store.Store M → Mode M →
      Spec.OpenExecution.Mode SourceControl → Nat → Prop
  | host {code store} (raw : HostState) (source : SourceHostState)
      (represented : HostStateRepresents store.id source raw) :
      SourceMode memory allocator view code store (.host raw) (.host (.active source)) 0
  | draft {code store} (status : HostStatus) (values : Slice runtime.Value)
      (owned : ∀value∈values.val,Store.ValueInStore store value) :
      SourceMode memory allocator view code store (.hostReturn status values) (.host (.draft (sourceReply status values))) 0
  | preparing {code store} (exec : runtime.interp.Execution) (address : runtime.FuncAddr)
      (signature : Itasca.types.FuncType) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
      (phase : InvokePhase M Unit) (metadata : RootMetadata store address signature)
      (ready : SourceRootInvokeReady allocator (inert memory) view code exec store () Spec.invocationFrame address signature args results phase) :
      SourceMode memory allocator view code store (.preparing phase)
        (.invokeRequest address.index.val (args.val.map sourceValue)
          (signature.params.val.map sourceType) (signature.results.val.map sourceType)) 0
  | wasm (signature : Itasca.types.FuncType)
      (world : EventfulWorld M Unit view (signature.results.val.map sourceType))
      (root : runtime.FuncAddr) (results : alloc.vec.Vec runtime.Value)
      (metadata : RootMetadata world.machine.store root signature)
      (typed : Config_ok (Abs.decode world.machine.source) (.mk_list (signature.results.val.map sourceType))) :
      SourceMode memory allocator view world.code world.machine.store (.wasm world.machine.exec (.Ok ()) root results)
        (.wasm (Abs.decode world.machine.source).1.2 (Abs.decode world.machine.source).2 (.mk_list (signature.results.val.map sourceType)))
        (2+dispatchMeasure world.machine.pending U32.max world.machine.pc world.machine.source)
  | finishing {code store} (exec : runtime.interp.Execution) (error : runtime.ExecError)
      (root : runtime.FuncAddr) (results : alloc.vec.Vec runtime.Value) (signature : Itasca.types.FuncType)
      (metadata : RootMetadata store root signature) :
      SourceMode memory allocator view code store (.wasm exec (.Err error) root results)
        (.invokeReturn (sourceInvocationResult (.Err error) results)) 1
  | returned {code store} (answer : InvokeAnswer M Unit) (sameStore : answer.2.2.1=store)
      (issued : answer.1=.Ok () → ∀value∈answer.2.2.2.2.val,Store.IssuedValue answer.2.2.1 value) :
      SourceMode memory allocator view code store (.invokeReturn answer)
        (.invokeReturn (sourceInvocationResult answer.1 answer.2.2.2.2)) 0

theorem SourceMode.native {M A : Type} {memory : runtime.platform.MemoryBuffer M} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation} {store : runtime.store.Store M}
    {native : Mode M} {source : Spec.OpenExecution.Mode SourceControl} {rank : Nat}
    (mode : SourceMode memory allocator view code store native source rank) (held : ExecutableInv view code store) :
    ModeGuard memory view code store native := by
  cases mode with
  | host raw source represented=>trivial
  | draft status values owned=>exact fun value member=>(owned value member).issued
  | preparing exec address signature args results phase metadata ready=>
    exact ready.forget.task memory held Spec.empty_frame_wf metadata
  | wasm signature world root results metadata typed=>
    exact ⟨signature,metadata,fun _=>⟨world.machine.source,world.machine.pc,world.machine.pending,world.machine.invariant,world.machine.owned⟩⟩
  | finishing exec error root results signature metadata=>
    exact ⟨signature,metadata,by intro impossible; cases impossible⟩
  | returned answer sameStore issued=>exact ⟨sameStore,by simpa only [sameStore] using issued⟩

theorem SourceMode.typed {M A : Type} {memory : runtime.platform.MemoryBuffer M} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation} {store : runtime.store.Store M}
    {native : Mode M} {source : Spec.OpenExecution.Mode SourceControl} {rank : Nat}
    (mode : SourceMode memory allocator view code store native source rank) :
    Spec.OpenExecution.ModeTyped (Store.decodeStore view code store) source := by
  cases mode with
  | host raw source represented | draft status values owned | finishing exec error root results signature metadata | returned answer sameStore issued=>trivial
  | preparing exec address signature args results phase metadata ready=>
    obtain ⟨owner,function,functionAt,signatureAt⟩ := metadata
    exact source_function_signature view code store address.index function signature functionAt signatureAt
  | wasm signature world root results metadata typed=>
    change Config_ok ⟨⟨Store.decodeStore view world.code world.machine.store,(Abs.decode world.machine.source).1.2⟩,
      (Abs.decode world.machine.source).2⟩ (.mk_list (signature.results.val.map sourceType))
    have same : (Abs.decode world.machine.source).1.1=Store.decodeStore view world.code world.machine.store := by
      simpa only [Abs.decode] using world.machine.invariant.storeEq
    generalize configurationEq : Abs.decode world.machine.source=configuration at same typed ⊢
    rcases configuration with ⟨⟨s,f⟩,body⟩
    dsimp only at same
    subst s
    exact typed
/-- Local control refinement plus checked native results constructs either an
active host mode or a draft reply without assuming callback termination. -/
theorem SourceMode.of_control {M A : Type} {memory : runtime.platform.MemoryBuffer M}
    {allocator : runtime.platform.Alloc A} {view : M → Slice U8} {code otherCode : Store.CodeInterpretation}
    {store : runtime.store.Store M} {mode : Mode M} {control : SourceControl}
    (represented : SourceControlRepresents store.id control mode)
    (native : ModeGuard memory view otherCode store mode) :
    SourceMode memory allocator view code store mode (.host control) 0 := by
  cases mode with
  | host raw=>
    cases control with
    | active source=>exact .host raw source represented
    | draft result=>cases represented
  | hostReturn status values=>
    cases control with
    | active source=>cases represented
    | draft result=>
      obtain ⟨same,owned⟩ := represented
      subst result
      exact .draft status values (fun value member=>(native value member).in_store (owned value member))
  | preparing phase=>cases control <;> cases represented
  | wasm exec status root results=>cases control <;> cases represented
  | invokeReturn answer=>cases control <;> cases represented
end Exec.Theorems.OpenReentrantControl
