import Exec.Theorems.Host.Open.Native.NativeLoopPartial
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std Exec.Interp Exec.Interp.OpenCall

/-- Synchronous loop/readback execution is partially safe for the concrete
combined callback implementation, retaining every committed checked effect. -/
theorem native_execute_partial {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (select : Selector)
    (code : Store.CodeInterpretation) (state : ExecutionState M Unit)
    (held : ExecutableInv view code state.2.1) (root : runtime.FuncAddr) (signature : Itasca.types.FuncType)
    (task : WasmTask view code state.2.1 state.1 state.2.2.2 root signature)
    (results : alloc.vec.Vec runtime.Value) :
    executeAndReadback memory (platform memory floats allocator select) floats allocator root results state ⦃out=>∃afterCode,
      ReentrantCallbacks.Effect view code state.2.1 afterCode out.2.2.1 ∧
      (out.1=.Ok () → ∀value∈out.2.2.2.2.val,Store.IssuedValue out.2.2.1 value)⦄div := by
  have safe:=native_loop_partial memory floats allocator correct allocation view laws select code state root signature held task
  simp only [executeAndReadback]
  generalize loopResult : runtime.interp.invoke_with_loop1 memory (platform memory floats allocator select) floats allocator
    state.1 state.2.1 state.2.2.1 state.2.2.2=result at safe ⊢
  cases safe with
  | div=>simp only [bind_div];exact WP.dspec.div _
  | ret post=>
    rename_i finished
    obtain ⟨count,trace,last,valid,stopped,finishEq⟩ := post
    obtain ⟨afterCode,effect,lastTask⟩ := valid
    obtain ⟨answer,read,execEq,storeEq,tokenEq,issued⟩ := WP.spec_imp_exists (lastTask.readback memory allocator allocation results stopped)
    simp only [bind_ok,finishEq,read]
    apply WP.dspec.ret
    refine ⟨afterCode,?_,?_⟩
    · simpa only [storeEq] using effect
    · simpa only [storeEq] using issued
end Exec.Theorems.OpenReentrantControl
