import Itasca.Runtime.Store.Invariant.PrecommitError
import Itasca.Runtime.Store.Instantiation.LinkedPreparedRun
namespace Itasca.Runtime.Store
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

/-- Linking provenance of an actual precommit rejection. -/
structure PrecommitOrigins {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (before staged : runtime.store.Store M)
    (module : runtime.compiler.ExecutableModule) (imports : Slice runtime.Extern)
    (error : runtime.ExecError) : Prop where
  linking : PrecommitLinkEvidence memory before module imports error

theorem PrecommitOrigins.resource {M : Type} {memory : runtime.platform.MemoryBuffer M}
    {view : M → Slice U8} {before staged : runtime.store.Store M} {module imports error}
    (resource : ResourceError error) : PrecommitOrigins memory view before staged module imports error := by
  cases error <;> simp_all only [ResourceError]
  constructor
  intro link impossible
  cases impossible

theorem PrecommitOrigins.linked {M : Type} {memory : runtime.platform.MemoryBuffer M}
    {view : M → Slice U8} {before staged : runtime.store.Store M} {module imports error}
    (inst : runtime.store.ModuleInst)
    (linked : runtime.store.instantiate.Store.prepare_instance_loop2 memory before imports
      (.Ok ()) 0#usize (emptyInstance module) = .ok (before, .Err error, inst))
    : PrecommitOrigins memory view before staged module imports error := by
  constructor
  intro link same
  exact Or.inr ⟨inst, same ▸ linked⟩

end Itasca.Runtime.Store
