import Exec.Store.Linking.LinkLoopComplete
import Itasca.Module.Elab.Metadata
namespace Exec.Store
open Aeneas Aeneas.Std Itasca
/-- Canonical source import typing supplies the exact raw types used by the
extracted linker, including equal import counts. -/
theorem raw_imports_resolve_typed {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (module : runtime.compiler.ExecutableModule)
    (raw : ModuleBinary.Module) (matched : ModuleElaboration.Matches module.module.env module.module.tail raw)
    (imports : Slice runtime.Extern)
    (typed : List.Forall₂ (Externaddr_ok (decodeStore view code store))
      (imports.val.map decodeExternal)
      (raw.imports.map (fun entry => ModuleElaboration.importType raw.types entry.desc))) :
    ∃ requiredTypes, List.Forall₂ (ModuleExternals.ImportResolves module.module.env)
        module.module.env.imports.val requiredTypes ∧
      List.Forall₂ (fun external required =>
        Externaddr_ok (decodeStore view code store) (decodeExternal external)
          (ModuleExternals.externalType required)) imports.val requiredTypes ∧
      imports.length = module.module.env.imports.length := by
  obtain ⟨requiredTypes, resolved⟩ := matched.2.imports_resolve
  have translated : requiredTypes.map ModuleExternals.externalType =
      raw.imports.map (fun entry => ModuleElaboration.importType raw.types entry.desc) := by
    have rawImports := congrArg ModuleBinary.Module.imports matched.1
    have rawTypes := congrArg ModuleBinary.Module.types matched.1
    simp only [ModuleElaboration.fromEnv] at rawImports rawTypes
    rw [rawImports, rawTypes]
    simpa [ModuleEnv.rawImport, List.map_map, Function.comp_def] using
      ModuleElaboration.import_types_resolved resolved
  rw [← translated] at typed
  have related : List.Forall₂ (fun external required =>
      Externaddr_ok (decodeStore view code store) (decodeExternal external)
        (ModuleExternals.externalType required)) imports.val requiredTypes := by
    simpa only [List.forall₂_map_left_iff, List.forall₂_map_right_iff] using typed
  refine ⟨requiredTypes, resolved, related, ?_⟩
  exact related.length_eq.trans resolved.length_eq.symm
/-- The complete extracted import loop accepts every canonically source-typed
same-store handle; foreign handles retain the explicit WrongStore result. -/
theorem link_imports_raw_typed {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (store : runtime.store.Store M) (shape : Shape view store)
    (code : CodeInterpretation) (module : runtime.compiler.ExecutableModule)
    (raw : ModuleBinary.Module) (matched : ModuleElaboration.Matches module.module.env module.module.tail raw)
    (imports : Slice runtime.Extern)
    (typed : List.Forall₂ (Externaddr_ok (decodeStore view code store))
      (imports.val.map decodeExternal)
      (raw.imports.map (fun entry => ModuleElaboration.importType raw.types entry.desc)))
    (handles : ∀ external ∈ imports.val, ExternalIssued store external)
    (inst : runtime.store.ModuleInst) (maps : LinkedMaps view store module [] inst) :
    runtime.store.instantiate.Store.instantiate_inner_loop2 memory store imports (.Ok ()) 0#usize inst
      ⦃ out => out.1 = store ∧ out.2.2.module = module ∧
        (out.2.1 = .Ok () ∨ out.2.1 = .Err .WrongStore) ∧
        (out.2.1 = .Ok () → LinkedMaps view store module module.module.env.imports.val out.2.2) ⦄ := by
  obtain ⟨required, resolved, typedImports, lengths⟩ :=
    raw_imports_resolve_typed view code store module raw matched imports typed
  exact link_imports_source_typed memory view laws store shape module imports code required resolved typedImports
    lengths handles matched.2 inst 0#usize (by simp) (by simpa using maps)
end Exec.Store
