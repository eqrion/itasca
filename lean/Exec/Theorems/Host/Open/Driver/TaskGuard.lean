import Exec.Theorems.Host.Open.Driver.WorldPreparation
import Exec.Theorems.Host.Open.Driver.ResumptionAt
import Exec.Theorems.Host.Open.Driver.Readback
import Exec.Theorems.Host.Open.Driver.RootHost
import Exec.Theorems.Host.Open.Driver.RootPreparation
import Exec.Theorems.Host.Reentrant.FiniteReentrantCallbacks
import Exec.Store.Invariant.IssuedArguments
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall

/-- The root signature is retained by raw metadata prefixes, independently
of effects on mutable objects or publication of additional instances. -/
def RootMetadata {M : Type} (store : runtime.store.Store M) (address : runtime.FuncAddr)
    (signature : Itasca.types.FuncType) : Prop :=
  address.store=store.id ∧ ∃function,store.funcs.val[address.index.val]?=some function ∧
    store.types.val[function.signature.val]?=some signature

theorem RootMetadata.prefix {M : Type} {before after : runtime.store.Store M} {address : runtime.FuncAddr}
    {signature : Itasca.types.FuncType} (held : RootMetadata before address signature) (retained : FrameStorePrefix before after) :
    RootMetadata after address signature := by
  obtain ⟨owner,function,found,typed⟩ := held
  exact ⟨owner.trans retained.identity.symm,function,retained.function_lookup found,retained.type_lookup typed⟩

/-- The active native execution has a checked source machine whenever its
status permits another Wasm step. Error statuses proceed directly to readback. -/
def WasmTask {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (exec : runtime.interp.Execution) (status : Status)
    (root : runtime.FuncAddr) (signature : Itasca.types.FuncType) : Prop :=
  RootMetadata store root signature ∧ (status=.Ok () → ∃source pc pending,
    StructuredMachine.Execution Executable.emission (Abs.SupportedState Abs.ExecutableInstr)
      view code store exec source (signature.results.val.map sourceType) pc pending ∧
    Abs.Ownership.StatefulOwned (Store.ownershipBounds store) source)

/-- The complete-profile native step theorem constructs the next task guard
and its cumulative effect. This is an actual opcode proof, not a step law
imposed on host implementations. -/
theorem ResumedWorldResult.task {M : Type} {view : M → Slice U8} {signature : Itasca.types.FuncType}
    {world : EventfulWorld Executable.emission Abs.ExecutableInstr M Unit view (signature.results.val.map sourceType)}
    {out : Answer M Unit} {root : runtime.FuncAddr} (post : ResumedWorldResult world out)
    (metadata : RootMetadata world.machine.store root signature) :
    ∃afterCode,ReentrantCallbacks.Effect view world.code world.machine.store afterCode out.2.2.1 ∧
      WasmTask view afterCode out.2.2.1 out.2.1 out.1 root signature := by
  cases kind : out.1 with
  | Ok unit =>
    cases unit
    simp only [ResumedWorldResult,kind] at post
    obtain ⟨next,held,same,simulation,extension,retained,externs,ambient,agrees⟩ := post
    subst out
    refine ⟨next.code,⟨⟨agrees,held,retained,extension⟩,externs⟩,metadata.prefix retained,?_⟩
    intro _
    exact ⟨next.machine.source,next.machine.pc,next.machine.pending,next.machine.invariant,next.machine.owned⟩
  | Err error =>
    simp only [ResumedWorldResult,kind] at post
    obtain ⟨afterCode,held,retained,externs,agrees,extension,source⟩ := post
    exact ⟨afterCode,⟨⟨agrees,held,retained,extension⟩,externs⟩,metadata.prefix retained,by intro impossible; simp [kind] at impossible⟩

/-- The same guard is available at the exact post-callback interpretation,
so newly published code is never forgotten when a saved caller resumes. -/
theorem ResumedWorldResultAt.task {M : Type} {view : M → Slice U8} {signature : Itasca.types.FuncType}
    {world : EventfulWorld Executable.emission Abs.ExecutableInstr M Unit view (signature.results.val.map sourceType)}
    {target : Store.CodeInterpretation} {out : Answer M Unit} {root : runtime.FuncAddr}
    (post : ResumedWorldResultAt world target out) (metadata : RootMetadata world.machine.store root signature) :
    WasmTask view target out.2.2.1 out.2.1 out.1 root signature := by
  cases kind : out.1 with
  | Ok unit =>
    cases unit
    simp only [ResumedWorldResultAt,kind] at post
    obtain ⟨next,held,same,simulation,extension,retained,externs,ambient,agrees⟩ := post
    subst out
    exact ⟨metadata.prefix retained,fun _=>⟨next.source,next.pc,next.pending,next.invariant,next.owned⟩⟩
  | Err error =>
    simp only [ResumedWorldResultAt,kind] at post
    exact ⟨metadata.prefix post.2.1,by intro impossible; simp [kind] at impossible⟩

/-- A saved continuation accepts any future checked effect and issued reply.
This is a native resumption law, not a requirement that host control returns. -/
def SavedWasm {M : Type} (memory : runtime.platform.MemoryBuffer M) (view : M → Slice U8)
    (code : Store.CodeInterpretation) (store : runtime.store.Store M)
    (exec : runtime.interp.Execution) (address : runtime.FuncAddr) (base : Usize)
    (root : runtime.FuncAddr) (signature : Itasca.types.FuncType) : Prop :=
  ∀afterCode after,ReentrantCallbacks.Effect view code store afterCode after →
    ∀status values,(∀value∈values.val,Store.IssuedValue after value) →
      hostResume memory exec after address base ⟨values⟩ status
        ⦃out=>WasmTask view afterCode after out.2 out.1 root signature⦄

theorem SavedWasm.extend {M : Type} {memory : runtime.platform.MemoryBuffer M} {view : M → Slice U8}
    {beforeCode afterCode : Store.CodeInterpretation} {before after : runtime.store.Store M}
    {exec : runtime.interp.Execution} {address root : runtime.FuncAddr} {base : Usize} {signature : Itasca.types.FuncType}
    (saved : SavedWasm memory view beforeCode before exec address base root signature)
    (effect : ReentrantCallbacks.Effect view beforeCode before afterCode after) :
    SavedWasm memory view afterCode after exec address base root signature := by
  intro finalCode final more status values issued
  exact saved finalCode final (effect.trans more) status values issued

/-- Every actual suspended Wasm step constructs the saved-continuation law
from complete-profile native simulation and checked dynamic host resumption. -/
theorem suspended_world_task {M F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator) (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    {signature : Itasca.types.FuncType}
    (world : EventfulWorld Executable.emission Abs.ExecutableInstr M Unit view (signature.results.val.map sourceType))
    (held : ExecutableInv view world.code world.machine.store) (active : 0<world.machine.exec.frames.length)
    (root : runtime.FuncAddr) (metadata : RootMetadata world.machine.store root signature)
    (ready : runtime.interp.Execution) (address : runtime.FuncAddr) (base : Usize) (identity : U64)
    (args defaults : alloc.vec.Vec runtime.Value)
    (pending : prepareStep memory (inert memory) floats allocator world.machine.exec world.machine.store world.machine.platform=
      .ok (.pending ready world.machine.store world.machine.platform address base identity args defaults)) :
    SavedWasm memory view world.code world.machine.store ready address base root signature := by
  intro afterCode after effect status values issued
  obtain ⟨answer,actual,post⟩ := WP.spec_imp_exists (resume_world_at memory floats allocator correct allocation view laws world
    held active ready address base identity args defaults pending afterCode after status values effect.toReturnedWorldEffect effect.externs issued)
  obtain ⟨pair,resumed,same⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ actual
  rcases pair with ⟨result,finished⟩
  have answerEq : answer=(result,finished,after,world.machine.platform) := by simpa using same.symm
  subst answer
  rw [resumed,WP.spec_ok]
  exact post.task metadata

/-- Root host preparation supplies the same saved-continuation law. Accepted
results create a terminal source machine; rejected results retain a trap. -/
theorem suspended_root_host_task {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : Store.CodeInterpretation) (store : runtime.store.Store M)
    (ready : runtime.interp.Execution) (empty : ready.frames.val=[])
    (address : runtime.FuncAddr) (function : runtime.store.Function) (identity : U64)
    (signature : Itasca.types.FuncType) (metadata : RootMetadata store address signature)
    (functionAt : store.funcs.val[address.index.val]?=some function)
    (host : function.code=.Host identity) (signatureAt : store.types.val[function.signature.val]?=some signature)
    (ambient : frame) (ambientWf : wf_frame ambient) (args : List val)
    (typed : ResultsTyped (Store.decodeStore view code store) (signature.params.val.map sourceType) args)
    (capacity : Code.slots (signature.results.val.map sourceType)≤ready.slots.length) :
    SavedWasm memory view code store ready address 0#usize address signature := by
  intro afterCode after effect status values issued
  apply WP.spec_mono (root_host_resume memory view code afterCode store after effect.toReturnedWorldEffect ready empty address
    function identity signature functionAt host signatureAt ambient ambientWf args typed values issued status capacity)
  rintro ⟨result,finished⟩ ⟨frames,owner,success|failure⟩
  · obtain ⟨ok,source,machine,owned⟩ := success
    exact ⟨metadata.prefix effect.metadata,fun _=>⟨_,0,false,machine,owned⟩⟩
  · exact ⟨metadata.prefix effect.metadata,by intro impossible; rcases failure.1 with trapped|exhausted <;> simp_all⟩

/-- A stopped task reads back normally and retains the exact store. Any
successful API results are issued; allocator refusal stays an ordinary error. -/
theorem WasmTask.readback {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    {view : M → Slice U8} {code : Store.CodeInterpretation} {store : runtime.store.Store M}
    {exec : runtime.interp.Execution} {status : Status} {root : runtime.FuncAddr} {signature : Itasca.types.FuncType}
    (guard : WasmTask view code store exec status root signature) (results : alloc.vec.Vec runtime.Value)
    (stopped : ¬(0<exec.frames.length ∧ status=.Ok ())) :
    readback memory allocator root results (finishExecution (exec,store,(),status)) ⦃answer=>
      answer.2.1=exec ∧ answer.2.2.1=store ∧ answer.2.2.2.1=() ∧
      (answer.1=.Ok () → ∀value∈answer.2.2.2.2.val,Store.IssuedValue store value)⦄ := by
  cases status with
  | Err error =>
    simp [Exec.Interp.OpenCall.readback,finishExecution,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,core.convert.FromSame.from,bind_ok]
  | Ok unit =>
    cases unit
    obtain ⟨source,pc,pending,machine,owned⟩ := guard.2 rfl
    have empty : exec.frames.val=[] := by
      have length : exec.frames.length=0 := by simp only [and_true,not_lt] at stopped; omega
      exact List.length_eq_zero_iff.mp length
    obtain ⟨sourceEmpty,typed,words⟩ := machine.finished empty
    have typedValues : ResultsTyped (Store.decodeStore view code store) (signature.results.val.map sourceType) source.results := by
      simpa only [machine.storeEq] using typed
    obtain ⟨owner,function,hf,hs⟩ := guard.1
    apply WP.spec_mono (readback_values memory allocator allocation view code store exec () root owner function signature hf hs
      results source.results typedValues owned.values.1 words)
    rintro answer ⟨execEq,storeEq,tokenEq,success|failure⟩
    · exact ⟨execEq,storeEq,tokenEq,fun _ value member=>(success.2.2 value member).issued⟩
    · exact ⟨execEq,storeEq,tokenEq,by intro impossible; rw [failure.1] at impossible; cases impossible⟩
end Exec.Theorems.OpenReentrantControl
