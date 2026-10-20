import Exec.Theorems.Host.Open.Driver.ReentrantControl
import Exec.Theorems.Host.Open.Driver.RootInput
import Exec.Spec.Typing.EmptyFrameTyping
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall

/-- A checked host invocation request prepares a fresh execution normally.
Its guard is derived from the current certified function/type tables, including
ordinary rejection of mismatched literal arguments. -/
theorem host_invoke_setup {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (view : M → Slice U8) (code : Store.CodeInterpretation)
    (select : Selector) (state : State M) (held : ExecutableInv view code state.store)
    (host : HostState) (mode : state.mode=.host host) (index : Usize)
    (values : Slice PureCallbacks.Literal) (next : Nat)
    (selected : host.code[host.pc]?=some (.invoke index values next)) (inside : index.val<state.store.funcs.length) :
    tick memory floats allocator select state ⦃out=>∃phase signature,
      RootInvokeReady view code state.store default ⟨state.store.id,index⟩ signature
        ((OpenHostControl.literalValues values).val.map sourceValue) phase ∧
      out=.cont {state with
        mode:=.preparing phase,stack:=.host host next::state.stack,
        history:=state.history++[.invokeEnter ⟨state.store.id,index⟩ (OpenHostControl.literalValues values)]} ⦄ := by
  let function := state.store.funcs.val[index.val]
  have functionAt : state.store.funcs.val[index.val]?=some function := List.getElem?_eq_getElem inside
  have shape := held.shape.functions function (List.getElem_mem inside)
  let signature := state.store.types.val[function.signature.val]'shape.1
  have signatureAt : state.store.types.val[function.signature.val]?=some signature := List.getElem?_eq_getElem shape.1
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
  exact WP.spec.ret ⟨phase,signature,guard,rfl⟩
end Exec.Theorems.OpenReentrantControl
