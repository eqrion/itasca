import Exec.Theorems.Host.Open.Native.NativeTraceLift
import Exec.Theorems.Host.Open.Native.NativeLoopPartial
namespace Exec.Theorems.OpenReentrantControl.Erased
open Aeneas Aeneas.Std Exec.Interp Exec.Interp.OpenCall

/-- A particular returned native loop/readback computation expands to an
actual finite combined invocation, including every child callback trace. -/
theorem native_execute_lift {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (select : Selector)
    (code : Store.CodeInterpretation) (state : ExecutionState M Unit)
    (held : ExecutableInv view code state.2.1) (root : runtime.FuncAddr) (signature : Itasca.types.FuncType)
    (task : WasmTask view code state.2.1 state.1 state.2.2.2 root signature)
    (results : alloc.vec.Vec runtime.Value) (answer : InvokeAnswer M Unit)
    (actual : executeAndReadback memory (platform memory floats allocator select) floats allocator root results state=.ok answer) :
    ∃total,NormalTrace (tick memory floats allocator select) total
      ⟨state.2.1,.wasm state.1 state.2.2.2 root results,[]⟩ (.invocation answer) := by
  simp only [executeAndReadback] at actual
  obtain ⟨finished,returned,read⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ actual
  have safe:=native_loop_partial memory floats allocator correct allocation view laws select code state root signature held task
  rw [returned,WP.dspec_ok] at safe
  obtain ⟨count,trace,rest⟩ := safe
  exact native_trace_lift memory floats allocator correct allocation view laws select trace code held root signature task results answer read
end Exec.Theorems.OpenReentrantControl.Erased
