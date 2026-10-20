import Exec.Theorems.Host.Open.Native.NativePreparation
import Exec.Theorems.Host.Open.Native.NativeCallLift
import Exec.Theorems.Host.Open.Erasure.EraseNativeTicks
noncomputable section
namespace Exec.Theorems.OpenReentrantControl.Erased
open Aeneas Aeneas.Std Exec.Interp Exec.Interp.OpenCall

/-- A finite native execution trace expands every returned callback into its
actual combined subtree and resumes the exact saved Wasm continuation. -/
theorem native_trace_lift {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (select : Selector)
    {count : Nat} {first : ExecutionState M Unit} {finished : ExecutionResult M Unit}
    (trace : NormalTrace (executionBody memory (platform memory floats allocator select) floats allocator) count first finished)
    (code : Store.CodeInterpretation) (held : ExecutableInv view code first.2.1)
    (root : runtime.FuncAddr) (signature : Itasca.types.FuncType)
    (task : WasmTask view code first.2.1 first.1 first.2.2.2 root signature)
    (results : alloc.vec.Vec runtime.Value) (answer : InvokeAnswer M Unit)
    (read : readback memory allocator root results finished=.ok answer) :
    ∃total,NormalTrace (tick memory floats allocator select) total
      ⟨first.2.1,.wasm first.1 first.2.2.2 root results,[]⟩ (.invocation answer) := by
  induction trace generalizing code with
  | @done current finished actual=>
    obtain ⟨phase,prepared,ready⟩ := WP.spec_imp_exists (task.prepare_loop memory floats allocator correct allocation view laws held)
    have graph:=erase_loop_body memory (platform memory floats allocator select) floats allocator current
    rw [prepareLoop_independent memory (platform memory floats allocator select) (inert memory) floats allocator current (fun _=>rfl),prepared,bind_ok] at graph
    rw [←graph] at actual
    cases phase with
    | finished returned=>
      have same : returned=finished := by simpa [resumeLoop] using actual
      subst finished
      rcases current with ⟨exec,store,token,status⟩
      cases token
      have enter:=wasm_tick_finished memory floats allocator select exec store status root results returned prepared answer read
      exact ⟨1,.next enter (.done (invocation_return_tick memory floats allocator select answer.2.2.1 answer))⟩
    | executing phase=>
      simp only [resumeLoop] at actual
      obtain ⟨out,resumed,impossible⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ actual
      rcases out with ⟨status,exec,store,token⟩
      simp [Std.uncurry] at impossible
  | @next count current next finished actual rest ih=>
    obtain ⟨phase,prepared,ready⟩ := WP.spec_imp_exists (task.prepare_loop memory floats allocator correct allocation view laws held)
    have graph:=erase_loop_body memory (platform memory floats allocator select) floats allocator current
    rw [prepareLoop_independent memory (platform memory floats allocator select) (inert memory) floats allocator current (fun _=>rfl),prepared,bind_ok] at graph
    rw [←graph] at actual
    cases phase with
    | finished returned=>simp [resumeLoop] at actual
    | executing phase=>
      change CallTask memory view code current.2.1 root signature phase at ready
      simp only [resumeLoop] at actual
      obtain ⟨out,resumed,packed⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ actual
      have nextEq : next=(out.2.1,out.2.2.1,out.2.2.2,out.1) := by simpa [Std.uncurry] using packed.symm
      have safe:=ready.resume_partial memory floats allocator correct allocation view laws select held
      rw [resumed,WP.dspec_ok] at safe
      obtain ⟨afterCode,effect,afterTask⟩ := safe
      have nextHeld : ExecutableInv view afterCode next.2.1 := by rw [nextEq];exact effect.invariant
      have nextTask : WasmTask view afterCode next.2.1 next.1 next.2.2.2 root signature := by rw [nextEq];exact afterTask
      obtain ⟨suffixCount,suffix⟩ := ih afterCode nextHeld nextTask read
      have physicalSuffix : NormalTrace (tick memory floats allocator select) suffixCount
          ⟨out.2.2.1,.wasm out.2.1 out.1 root results,[]⟩ (.invocation answer) := by simpa only [nextEq] using suffix
      obtain ⟨bodyCount,body⟩ := call_phase_lift memory floats allocator correct allocation view laws select code current.2.1 held root signature results phase ready out resumed physicalSuffix
      rcases current with ⟨exec,store,token,status⟩
      cases token
      have enter:=wasm_tick_executing memory floats allocator select exec store status root results phase prepared
      exact ⟨bodyCount+1,.next enter body⟩
end Exec.Theorems.OpenReentrantControl.Erased
