import Exec.Theorems.Host.Open.Source.State.StateGuard
import Exec.Theorems.Host.Open.Source.Control.Publication
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall

/-- A nested request constructs its fresh native root guard and corresponding
source request together, retaining the parent's saved immutable control. -/
theorem source_invoke_step {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (view : M → Slice U8)
    (select : Selector) (owner : Usize) (stop : Spec.OpenExecution.StopReason → config → Prop)
    (code : Store.CodeInterpretation) (native : State M) (source : Spec.OpenExecution.State SourceControl) (rank : Nat)
    (guard : SourceStateGuard memory allocator view code native source rank)
    (host : HostState) (hostSource : SourceHostState) (mode : native.mode=.host host)
    (sourceMode : source.mode=.host (.active hostSource))
    (represented : HostStateRepresents native.store.id hostSource host)
    (index : Usize) (values : Slice PureCallbacks.Literal) (nextPC : Nat)
    (selected : host.code[host.pc]?=some (.invoke index values nextPC)) (inside : index.val<native.store.funcs.length) :
    tick memory floats allocator select native ⦃out=>∃next nextSource,out=.cont next ∧
      SourceStateGuard memory allocator view code next nextSource 0 ∧
      Spec.OpenExecution.Transition (sourceModel view (sourcePublication allocator view) select owner stop)
        source [.invokeEnter index.val ((OpenHostControl.literalValues values).val.map sourceValue)] nextSource ∧
      sourceHistory next.history=sourceHistory native.history++[.invokeEnter index.val ((OpenHostControl.literalValues values).val.map sourceValue)]⦄ := by
  let function:=native.store.funcs.val[index.val]
  have functionAt : native.store.funcs.val[index.val]?=some function:=List.getElem?_eq_getElem inside
  have signatureBound := (guard.invariant.shape.functions function (List.getElem_mem inside)).1
  let signature:=native.store.types.val[function.signature.val]'signatureBound
  have signatureAt : native.store.types.val[function.signature.val]?=some signature:=List.getElem?_eq_getElem signatureBound
  have sourceSignature := source_function_signature view code native.store index function signature functionAt signatureAt
  have sourceSelected : hostSource.code[hostSource.pc]?=some (.invoke index values nextPC) := by
    simpa only [represented.1,represented.2.1] using selected
  let exec : runtime.interp.Execution:=⟨0#usize,alloc.vec.Vec.new _,alloc.vec.Vec.new _,alloc.vec.Vec.new _,alloc.vec.Vec.new _⟩
  let address : runtime.FuncAddr:=⟨native.store.id,index⟩
  let args:=OpenHostControl.literalValues values
  let results : alloc.vec.Vec runtime.Value:=alloc.vec.Vec.new _
  obtain ⟨phase,prepared,ready⟩ := WP.spec_imp_exists (prepare_source_root_input memory (inert memory) floats allocator allocation
    (fun _=>WP.spec.ret trivial) view code exec native.store () guard.invariant Spec.invocationFrame Spec.empty_frame_wf
    address function signature args results rfl ((PureCallbacks.Program.returned values).in_store native.store) functionAt signatureAt)
  let next : State M:={native with
    mode:=.preparing phase
    stack:=.host host nextPC::native.stack
    history:=native.history++[Observation.invokeEnter address args]}
  let nextSource : Spec.OpenExecution.State SourceControl:=⟨source.store,
    .invokeRequest index.val (args.val.map sourceValue) (signature.params.val.map sourceType) (signature.results.val.map sourceType),
    .host (.active {hostSource with pc:=nextPC})::source.stack⟩
  have actual : tick memory floats allocator select native=.ok (.cont next) := by
    simp only [tick,mode,selected,if_pos inside,runtime.interp.Execution.new,bind_ok]
    change (do let phase←prepareInvoke memory (inert memory) floats allocator exec native.store () address args results
               .ok (.cont {native with
                 mode:=.preparing phase
                 stack:=.host host nextPC::native.stack
                 history:=native.history++[Observation.invokeEnter address args]}))=(.ok (.cont next) : Result (ControlFlow (State M) (Outcome M)))
    simp only [prepared,bind_tc_eq,bind_ok,next]
  rw [actual]
  have sourceGuard : SourceStateGuard memory allocator view code next nextSource 0 :=
    ⟨guard.invariant,.preparing exec address signature args results phase ⟨rfl,function,functionAt,signatureAt⟩ ready,
      .cons (.host host nextPC hostSource represented) guard.stack,guard.storeEq⟩
  have step : Spec.OpenExecution.Transition (sourceModel view (sourcePublication allocator view) select owner stop)
      source [.invokeEnter index.val (args.val.map sourceValue)] nextSource := by
    rcases source with ⟨s,sourceControl,stack⟩
    dsimp only at sourceMode
    subst sourceControl
    have sameStore : s=Store.decodeStore view code native.store:=guard.storeEq
    subst s
    exact .requestInvoke (.invoke sourceSelected) sourceSignature.1 sourceSignature.2
  refine WP.spec.ret ⟨next,nextSource,rfl,sourceGuard,step,?_⟩
  simp only [next,sourceHistory,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,sourceObservation,List.append_nil,address,args]
end Exec.Theorems.OpenReentrantControl
