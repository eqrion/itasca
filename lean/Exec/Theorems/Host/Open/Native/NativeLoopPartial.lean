import Exec.Theorems.Host.Open.Native.NativeBodyPartial
import Exec.Interp.Control.LoopPartialTrace
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std Exec.Interp Exec.Interp.OpenCall

/-- Native loop prefixes retain the entered world across partial callbacks. -/
def NativeRunningFrom {M : Type} (view : M → Slice U8) (original : Store.CodeInterpretation)
    (before : runtime.store.Store M) (root : runtime.FuncAddr) (signature : Itasca.types.FuncType)
    (state : ExecutionState M Unit) : Prop :=
  ∃code,ReentrantCallbacks.Effect view original before code state.2.1 ∧
    WasmTask view code state.2.1 state.1 state.2.2.2 root signature

/-- Native synchronous execution permits blocked callback divergence. Any
normal loop return has an actual finite body trace and retains the typed task
and all committed effects at its exact stopped configuration. -/
theorem native_loop_partial {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (select : Selector)
    (code : Store.CodeInterpretation) (state : ExecutionState M Unit)
    (root : runtime.FuncAddr) (signature : Itasca.types.FuncType)
    (held : ExecutableInv view code state.2.1) (task : WasmTask view code state.2.1 state.1 state.2.2.2 root signature) :
    runtime.interp.invoke_with_loop2 memory (platform memory floats allocator select) floats allocator state.1 state.2.1 state.2.2.1 state.2.2.2
      ⦃finished=>∃count,NormalTrace (executionBody memory (platform memory floats allocator select) floats allocator) count state finished ∧
        ∃last,NativeRunningFrom view code state.2.1 root signature last ∧ ¬ActiveExecution last ∧ finished=finishExecution last⦄div := by
  let invariant:=NativeRunningFrom view code state.2.1 root signature
  let post:=fun finished=>∃last,invariant last ∧ ¬ActiveExecution last ∧ finished=finishExecution last
  have safe : ∀current,invariant current → executionBody memory (platform memory floats allocator select) floats allocator current
      ⦃out=>match out with | .cont next=>invariant next | .done finished=>post finished⦄div := by
    intro current valid
    obtain ⟨currentCode,effect,guard⟩ := valid
    apply WP.dspec_mono (native_body_partial memory floats allocator correct allocation view laws select currentCode current root signature effect.invariant guard)
    intro out result
    cases out with
    | cont next=>
      obtain ⟨afterCode,more,fresh⟩ := result
      exact ⟨afterCode,effect.trans more,fresh⟩
    | done finished=>
      obtain ⟨rfl,stopped⟩ := result
      exact ⟨current,⟨currentCode,effect,guard⟩,stopped,rfl⟩
  exact loop_partial_trace (executionBody memory (platform memory floats allocator select) floats allocator) invariant post
    (fun current valid=>WP.dspec_mono (safe current valid) (by intro out result;cases out <;> exact result)) state
    ⟨code,.refl held,task⟩
end Exec.Theorems.OpenReentrantControl
