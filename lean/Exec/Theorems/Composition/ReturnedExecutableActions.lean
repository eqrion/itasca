import Exec.Theorems.Host.HostReturnedActions
import Exec.Theorems.Invocation.PublicExecutableWorldSafety
import Exec.Theorems.Instantiation.InstantiateExecutableWorldCompiled
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp
/-- A returned nested invocation supplies one concrete action. The callback
law here must already be justified; this lemma does not establish that same
law by invoking itself or infer normality from finite nesting. -/
theorem invoke_returned_world_action {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀p,hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (sound : HostWorldSound hooks view (ExecutableInv view))
    (preserve : ∀c store,ExecutableInv view c store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → FrameStorePrefix store answer.2.2.1)
    (externs : ∀c store,ExecutableInv view c store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → store.externs.length≤answer.2.2.1.externs.length)
    (issuedResults : ∀c store,ExecutableInv view c store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : ExecutableInv view code store)
    (address : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (issued : Store.ExternalIssued store (.Func address))
    (argumentIssued : ∀value∈args.val,Store.IssuedValue store value)
    (answer : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P × alloc.vec.Vec runtime.Value)
    (actual : runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results = .ok answer) :
    ∃afterCode, ReturnedWorldAction view (ExecutableInv view) code store afterCode answer.2.2.1 := by
  apply ReturnedWorldAction.of_return _ answer (fun out => out.2.2.1) ?_ actual
  apply WP.dspec_mono (invoke_executable_world_safe memory hooks floats allocator correct allocation interrupts
    view laws code sound preserve externs issuedResults exec store platform valid address args results issued argumentIssued)
  intro out post
  obtain ⟨afterCode,agrees,fresh,kept,extension⟩ := post
  exact ⟨afterCode,agrees,fresh,kept,extension⟩

/-- Actual returned instantiation, including a returned start-call error, is
one action. The canonical compiled package is obtained from accepted compile;
its callback contract is still an independently supplied premise. -/
theorem instantiate_returned_world_action {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (before : runtime.store.Store M)
    (module : runtime.compiler.ExecutableModule) (imports : Slice runtime.Extern)
    (platform : P) (code : Store.CodeInterpretation) (bytes : Slice U8)
    (profile : Itasca.ValidationProfile)
    (package : CompiledWorldInstantiation memory hooks floats allocator view before module imports platform code bytes profile)
    (sound : HostWorldSound hooks view (ExecutableInv view))
    (preserve : ∀c store,ExecutableInv view c store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → FrameStorePrefix store answer.2.2.1)
    (externs : ∀c store,ExecutableInv view c store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → store.externs.length≤answer.2.2.1.externs.length)
    (issuedResults : ∀c store,ExecutableInv view c store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value)
    (answer : core.result.Result runtime.InstanceAddr runtime.ExecError × runtime.store.Store M × P)
    (actual : runtime.store.instantiate.Store.instantiate_with memory hooks floats allocator before module imports platform = .ok answer) :
    ∃afterCode, ReturnedWorldAction view (ExecutableInv view) code before afterCode answer.2.1 := by
  obtain ⟨raw,encoded,typed,safe⟩ := package
  apply ReturnedWorldAction.of_return _ answer (fun out => out.2.1) ?_ actual
  apply WP.dspec_mono (safe sound preserve externs issuedResults)
  intro out post
  obtain ⟨afterCode,agrees,fresh,kept,extension,source⟩ := post
  exact ⟨afterCode,agrees,fresh,kept,extension⟩
end Exec.Theorems
