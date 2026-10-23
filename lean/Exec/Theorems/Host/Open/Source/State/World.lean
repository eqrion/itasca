import Exec.Theorems.Host.Open.Driver.SiteSource
import Exec.Theorems.Host.Open.Driver.WorldPreparation
import Exec.Theorems.Host.Open.Source.State.Selector
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall

/-- A selected source request retains its context, source typing and exact
immutable host-code selection together. Completed native phases require no
host entry. -/
def SelectedSourceHost {M P : Type} (memory : runtime.platform.MemoryBuffer M) (view : M → Slice U8) (code : Store.CodeInterpretation)
    (select : Selector) (store : runtime.store.Store M) (source : config) (expected : resulttype) : CallPhase M P → Prop
  | .done _=>True
  | .pending ready _ _ address base identity args _=>ready.host_args=args ∧ ∃pending : Spec.OpenHost.Pending,
      pending.before=Store.decodeStore view code store ∧ pending.address=address.index.val ∧
      pending.identity=identity.val ∧ pending.arguments=args.val.map sourceValue ∧
      StepsH source [] pending.initial ∧ Config_ok pending.initial expected ∧
      Spec.UniversalQuietPrefix source pending.initial ∧
      SourceContinuation memory view code store ready address base pending
        (match expected with | .mk_list types=>types) ∧
      HostStateRepresents store.id (sourceHostEntry select store.id pending.identity pending.arguments)
        ⟨0,select identity args.slice,identity,args.slice⟩

theorem PreparedSourceHost.select {M P : Type} {memory : runtime.platform.MemoryBuffer M} {exec : runtime.interp.Execution} {view : M → Slice U8} {code : Store.CodeInterpretation}
    (select : Selector) {store : runtime.store.Store M} {source : config} {expected : resulttype} {phase : CallPhase M P}
    (held : PreparedSourceHost memory view code store exec source expected phase) :
    SelectedSourceHost memory view code select store source expected phase := by
  cases phase with
  | done answer=>trivial
  | pending ready after token address base identity args defaults=>
    obtain ⟨scratch,owned,pending,beforeEq,addressEq,identityEq,argsEq,path,typed,completion,chosen,saved⟩ := held
    refine ⟨scratch,pending,beforeEq,addressEq,identityEq,argsEq,path,typed,chosen,saved,?_⟩
    rw [identityEq,argsEq]
    exact sourceHostEntry_represents select store.id identity args.slice owned

/-- Native preparation constructs both the completed-step source certificate
and the selected typed source suspension. This keeps the particular source
configuration rather than projecting it away into an existential task guard. -/
theorem prepare_source_world_step {M F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator) (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (select : Selector) {expected : List valtype}
    (world : EventfulWorld M Unit view expected)
    (held : ExecutableInv view world.code world.machine.store) (active : 0<world.machine.exec.frames.length)
    (configurationTyped : Config_ok (Abs.decode world.machine.source) (.mk_list expected)) :
    prepareStep memory (inert memory) floats allocator world.machine.exec world.machine.store world.machine.platform
      ⦃phase=>PreparedWorldResult world phase ∧
        SelectedSourceHost memory view world.code select world.machine.store (Abs.decode world.machine.source) (.mk_list expected) phase⦄ := by
  obtain ⟨phase,actual,post⟩ := WP.spec_imp_exists (prepare_world_step memory floats allocator correct allocation view laws world held active)
  rw [actual,WP.spec_ok]
  refine ⟨post,?_⟩
  cases phase with
  | done answer=>trivial
  | pending ready after token address base identity args defaults=>
    exact (pending_source memory floats allocator correct allocation view laws world held active configurationTyped
      ready after token address base identity args defaults actual).select select
end Exec.Theorems.OpenReentrantControl
