import Exec.Store.Linking.LinkRawTypes
import Exec.Store.Instantiation.PrecommitOrigins
namespace Exec.Store
open Aeneas Aeneas.Std Itasca

/-- The two actual origins of a precommit Link rejection are impossible when
the canonical source import list is externally well typed. -/
theorem precommit_link_impossible {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (store : runtime.store.Store M) (shape : Shape view store)
    (code : CodeInterpretation) (module : runtime.compiler.ExecutableModule)
    (raw : ModuleBinary.Module) (matched : ModuleElaboration.Matches module.module.env module.module.tail raw)
    (imports : Slice runtime.Extern)
    (typed : List.Forall₂ (Externaddr_ok (decodeStore view code store))
      (imports.val.map decodeExternal)
      (raw.imports.map (fun entry => ModuleElaboration.importType raw.types entry.desc)))
    (handles : ∀ external ∈ imports.val, ExternalIssued store external)
    (link : runtime.LinkError)
    (origin : PrecommitLinkEvidence memory store module imports (.Link link)) : False := by
  rcases origin link rfl with ⟨missing, different⟩ | ⟨inst, returned⟩
  · obtain ⟨_, _, _, same⟩ := raw_imports_resolve_typed view code store module raw matched imports typed
    exact different same
  · have maps : LinkedMaps view store module [] (emptyInstance module) :=
      linked_maps_empty view store (emptyInstance module) rfl rfl rfl rfl rfl rfl rfl
    have complete := link_imports_raw_typed memory view laws store shape code module raw matched imports typed
      handles (emptyInstance module) maps
    rw [returned, WP.spec_ok] at complete
    simpa using complete.2.2.1
end Exec.Store
