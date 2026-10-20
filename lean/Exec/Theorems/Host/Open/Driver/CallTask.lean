import Exec.Theorems.Host.Open.Driver.TaskGuard
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall

/-- A prepared task either completes one native step with checked effects or
exposes a saved continuation whose future dynamic resumption is certified. -/
def CallTask {M : Type} (memory : runtime.platform.MemoryBuffer M) (view : M → Slice U8)
    (code : Store.CodeInterpretation) (store : runtime.store.Store M)
    (root : runtime.FuncAddr) (signature : Itasca.types.FuncType) : CallPhase M Unit → Prop
  | .done out => ∃afterCode,ReentrantCallbacks.Effect view code store afterCode out.2.2.1 ∧
      WasmTask view afterCode out.2.2.1 out.2.1 out.1 root signature
  | .pending exec after _ address base _ _ _ => after=store ∧ SavedWasm memory view code store exec address base root signature

/-- Typed active tasks prepare normally and construct both branches of the
combined driver guard from the actual complete-profile native proof. -/
theorem WasmTask.prepare {M F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator) (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    {code : Store.CodeInterpretation} {store : runtime.store.Store M} {exec : runtime.interp.Execution}
    {root : runtime.FuncAddr} {signature : Itasca.types.FuncType}
    (held : ExecutableInv view code store) (guard : WasmTask view code store exec (.Ok ()) root signature)
    (active : 0<exec.frames.length) :
    prepareStep memory (inert memory) floats allocator exec store () ⦃phase=>CallTask memory view code store root signature phase⦄ := by
  obtain ⟨source,pc,pending,machine,owned⟩ := guard.2 rfl
  let world : EventfulWorld Executable.emission Abs.ExecutableInstr M Unit view (signature.results.val.map sourceType) :=
    ⟨code,⟨store,exec,(),source,pc,pending,machine,held.toCertifiedApiStore.toCertifiedSupportedStore,owned⟩⟩
  obtain ⟨phase,actual,post⟩ := WP.spec_imp_exists (prepare_world_step memory floats allocator correct allocation view laws world held active)
  rw [actual,WP.spec_ok]
  cases phase with
  | done out => exact post.task guard.1
  | pending ready after token address base identity args defaults =>
    have same : after=store := post
    subst after
    cases token
    exact ⟨rfl,suspended_world_task memory floats allocator correct allocation view laws world held active root guard.1
      ready address base identity args defaults actual⟩

/-- Checked initial call preparation establishes the same task guard used by
ordinary native steps. Root hosts and Wasm bodies share the later driver. -/
theorem RootCallReady.task {M : Type} (memory : runtime.platform.MemoryBuffer M)
    {view : M → Slice U8} {code : Store.CodeInterpretation} {store : runtime.store.Store M}
    {ambient : frame} {root : runtime.FuncAddr} {signature : Itasca.types.FuncType} {args : List val}
    {phase : CallPhase M Unit} (held : ExecutableInv view code store) (ambientWf : wf_frame ambient)
    (metadata : RootMetadata store root signature) (guard : RootCallReady view code store ambient root signature args phase) :
    CallTask memory view code store root signature phase := by
  cases guard with
  | rejected answer error status sameStore =>
    refine ⟨code,?_,?_⟩
    · rw [sameStore]; exact .refl held
    · rw [sameStore]
      exact ⟨metadata,by intro impossible; rw [status] at impossible; cases impossible⟩
  | defined answer entry status sameStore machine owned ambientEq source =>
    refine ⟨code,?_,?_⟩
    · rw [sameStore]; exact .refl held
    · rw [sameStore]
      exact ⟨metadata,fun _=>⟨entry,0,false,machine,owned⟩⟩
  | host ready token identity args defaults function functionAt host signatureAt empty capacity argsEq typed =>
    exact ⟨rfl,suspended_root_host_task memory view code store ready empty root function identity signature metadata
      functionAt host signatureAt ambient ambientWf _ typed capacity⟩
end Exec.Theorems.OpenReentrantControl
