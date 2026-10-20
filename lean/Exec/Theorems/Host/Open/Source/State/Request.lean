import Exec.Theorems.Host.Open.Source.Control.Actions
import Exec.Theorems.Host.Open.Driver.HostInvoke
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall

/-- Nested invocation exposes a source request before argument validation.
The request signature is decoded from the same issued function/type metadata
used by native setup, and the host continuation retains its immutable code. -/
theorem source_invoke_request {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (view : M → Slice U8) (code : Store.CodeInterpretation)
    (publication : SourcePublication) (select : Selector) (stop : Spec.OpenExecution.StopReason → config → Prop)
    (state : State M) (held : ExecutableInv view code state.store)
    (host : HostState) (mode : state.mode=.host host) (source : SourceHostState)
    (represented : HostStateRepresents state.store.id source host) (index : Usize)
    (values : Slice PureCallbacks.Literal) (next : Nat)
    (selected : host.code[host.pc]?=some (.invoke index values next)) (inside : index.val<state.store.funcs.length)
    (sourceStack : List (Spec.OpenExecution.Continuation SourceControl)) :
    tick memory floats allocator select state ⦃out=>∃phase signature,
      RootInvokeReady view code state.store default ⟨state.store.id,index⟩ signature
        ((OpenHostControl.literalValues values).val.map sourceValue) phase ∧
      out=.cont {state with
        mode:=.preparing phase
        stack:=.host host next::state.stack
        history:=state.history++[.invokeEnter ⟨state.store.id,index⟩ (OpenHostControl.literalValues values)]} ∧
      Spec.OpenExecution.Transition (sourceModel view publication select state.store.id stop)
        ⟨Store.decodeStore view code state.store,.host (.active source),sourceStack⟩
        [.invokeEnter index.val ((OpenHostControl.literalValues values).val.map sourceValue)]
        ⟨Store.decodeStore view code state.store,
          .invokeRequest index.val ((OpenHostControl.literalValues values).val.map sourceValue)
            (signature.params.val.map sourceType) (signature.results.val.map sourceType),
          .host (.active {source with pc:=next})::sourceStack⟩⦄ := by
  let function:=state.store.funcs.val[index.val]
  have functionAt : state.store.funcs.val[index.val]?=some function:=List.getElem?_eq_getElem inside
  have signatureBound := (held.shape.functions function (List.getElem_mem inside)).1
  let signature:=state.store.types.val[function.signature.val]'signatureBound
  have signatureAt : state.store.types.val[function.signature.val]?=some signature:=List.getElem?_eq_getElem signatureBound
  have sourceBound : index.val<(Store.decodeStore view code state.store).FUNCS.length := by
    simpa only [Store.decodeStore,List.length_map] using inside
  have sourceAt : (Store.decodeStore view code state.store).FUNCS[index.val]?=some (Store.decodeFunction code state.store function) := by
    simp only [Store.decodeStore,List.getElem?_map,functionAt,Option.map_some]
  have sourceSignature : (Store.decodeStore view code state.store).FUNCS[index.val]!.TYPE=
      .mk_functype (.mk_list (signature.params.val.map sourceType)) (.mk_list (signature.results.val.map sourceType)) := by
    rw [getElem!_pos (Store.decodeStore view code state.store).FUNCS index.val sourceBound,(List.getElem?_eq_some_iff.mp sourceAt).2,Store.decodeFunction_type code state.store function signatureBound]
    change Store.decodeFuncType signature=_
    rfl
  have sourceSelected : source.code[source.pc]?=some (.invoke index values next) := by
    simpa only [represented.1,represented.2.1] using selected
  have request : Spec.OpenExecution.Transition (sourceModel view publication select state.store.id stop)
      ⟨Store.decodeStore view code state.store,.host (.active source),sourceStack⟩
      [.invokeEnter index.val ((OpenHostControl.literalValues values).val.map sourceValue)]
      ⟨Store.decodeStore view code state.store,
        .invokeRequest index.val ((OpenHostControl.literalValues values).val.map sourceValue)
          (signature.params.val.map sourceType) (signature.results.val.map sourceType),
        .host (.active {source with pc:=next})::sourceStack⟩ :=
    .requestInvoke (.invoke sourceSelected) sourceBound sourceSignature
  unfold tick
  rw [mode]
  dsimp only
  rw [selected]
  simp only [if_pos inside,runtime.interp.Execution.new,bind_ok]
  obtain ⟨phase,actual,guard⟩ := WP.spec_imp_exists (prepare_root_input memory (inert memory) floats allocator allocation
    (fun _=>WP.spec.ret trivial) view code _ state.store () held default Spec.empty_frame_wf ⟨state.store.id,index⟩
    function signature (OpenHostControl.literalValues values) (alloc.vec.Vec.new _) rfl
    ((PureCallbacks.Program.returned values).issued state.store) functionAt signatureAt)
  rw [actual,bind_ok]
  exact WP.spec.ret ⟨phase,signature,guard,rfl,request⟩

/-- An absent function traps before any nested-invocation entry is emitted. -/
theorem source_missing_invoke {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : Store.CodeInterpretation) (publication : SourcePublication) (select : Selector)
    (state : State M) (host : HostState) (mode : state.mode=.host host) (source : SourceHostState)
    (represented : HostStateRepresents state.store.id source host) (index : Usize)
    (values : Slice PureCallbacks.Literal) (next : Nat)
    (selected : host.code[host.pc]?=some (.invoke index values next)) (outside : ¬index.val<state.store.funcs.length) :
    tick memory floats allocator select state=.ok (.cont {state with mode:=.hostReturn (.Err .Trap) (Slice.new _)}) ∧
    SourceAction view publication (Store.decodeStore view code state.store) (.active source)
      (Store.decodeStore view code state.store) (.draft none) := by
  constructor
  · simp only [tick,mode,selected,if_neg outside]
  · apply SourceAction.missingFunction
    · simpa only [represented.1,represented.2.1] using selected
    · simpa only [Store.decodeStore,List.length_map] using outside
end Exec.Theorems.OpenReentrantControl
