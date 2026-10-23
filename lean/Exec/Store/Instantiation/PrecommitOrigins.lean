import Exec.Store.Initialization.PrecheckWitness
import Exec.Store.Instantiation.LinkedPreparedRun
namespace Exec.Store
open Aeneas Aeneas.Std

/-- A Link rejection originates at the public import-count gate or the actual
import loop, starting from the fresh instance's empty address maps. -/
def PrecommitLinkEvidence {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (before : runtime.store.Store M) (module : runtime.compiler.ExecutableModule)
    (imports : Slice runtime.Extern) (error : runtime.ExecError) : Prop :=
  ∀ link, error = .Link link →
    (link = .MissingImport ∧ imports.length ≠ module.module.env.imports.length) ∨
    ∃ inst, runtime.store.instantiate.Store.prepare_instance_loop2 memory before imports
      (.Ok ()) 0#usize (emptyInstance module) = .ok (before, .Err (.Link link), inst)

/-- A completed preflight state is structurally valid after charging its already
bounded item count. This ghost counter update does not change decoded state. -/
def PrecommitStageEvidence {M : Type} (view : M → Slice U8)
    (before staged : runtime.store.Store M) (module : runtime.compiler.ExecutableModule)
    (error : runtime.ExecError) : Prop :=
  ∀ trap, error = .Trap trap → ∃ (charged : Usize) (inst : runtime.store.ModuleInst),
    Shape view {staged with instance_items := charged} ∧
    staged.instances.length = before.instances.length + 1 ∧
    staged.instances.val[before.instances.length]? = some inst ∧ inst.module = module ∧
    PrecheckCause view staged inst error

/-- Source bounds and linking provenance of an actual precommit rejection. -/
structure PrecommitOrigins {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (before staged : runtime.store.Store M)
    (module : runtime.compiler.ExecutableModule) (imports : Slice runtime.Extern)
    (error : runtime.ExecError) : Prop where
  bounds : PrecommitBoundsEvidence view staged module error
  linking : PrecommitLinkEvidence memory before module imports error
  staging : PrecommitStageEvidence view before staged module error

theorem PrecommitOrigins.resource {M : Type} {memory : runtime.platform.MemoryBuffer M}
    {view : M → Slice U8} {before staged : runtime.store.Store M} {module imports error}
    (resource : ResourceError error) : PrecommitOrigins memory view before staged module imports error := by
  cases error <;> simp_all only [ResourceError]
  constructor
  · intro trap impossible; cases impossible
  · intro link impossible; cases impossible
  · intro trap impossible; cases impossible

theorem PrecommitOrigins.linked {M : Type} {memory : runtime.platform.MemoryBuffer M}
    {view : M → Slice U8} {before staged : runtime.store.Store M} {module imports error}
    (inst : runtime.store.ModuleInst)
    (linked : runtime.store.instantiate.Store.prepare_instance_loop2 memory before imports
      (.Ok ()) 0#usize (emptyInstance module) = .ok (before, .Err error, inst))
    (cause : PrecommitError .Wasm2 error) :
    PrecommitOrigins memory view before staged module imports error := by
  constructor
  · intro trap same
    subst error
    cases trap <;> simp_all [PrecommitError]
  · intro link same
    exact Or.inr ⟨inst, same ▸ linked⟩
  · intro trap same
    subst error
    cases trap <;> simp_all [PrecommitError]

theorem PrecommitOrigins.precheck {M : Type} {memory : runtime.platform.MemoryBuffer M}
    {view : M → Slice U8} {before staged : runtime.store.Store M} {module imports error}
    (index : Usize) (inst : runtime.store.ModuleInst)
    (found : staged.instances.val[index.val]? = some inst) (source : inst.module = module)
    (cause : PrecheckCause view staged inst error)
    (staging : PrecommitStageEvidence view before staged module error) :
    PrecommitOrigins memory view before staged module imports error := by
  constructor
  · intro trap same
    exact ⟨index, inst, found, source, cause⟩
  · intro link same
    subst error
    rcases cause with resource | ⟨impossible, _⟩ | ⟨impossible, _⟩
    · cases resource
    · cases impossible
    · cases impossible
  · exact staging

end Exec.Store
