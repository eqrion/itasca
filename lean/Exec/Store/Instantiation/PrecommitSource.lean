import Exec.Store.Instantiation.PrecommitOrigins
import Exec.Store.Initialization.PrecheckSource
namespace Exec.Store
open Aeneas Aeneas.Std Itasca

/-- The ghost item charge affects neither source objects nor source instance
maps. It is used only to discharge the complete structural store invariant. -/
theorem decodeStore_instance_items {M : Type} (view : M → Slice U8)
    (code : CodeInterpretation) (store : runtime.store.Store M) (charged : Usize) :
    decodeStore view code {store with instance_items := charged} = decodeStore view code store := by
  rfl

/-- Exact preflight provenance supplies source bounds failure without adding
well-formedness or evaluation assumptions about the provisional state. -/
theorem PrecommitOrigins.source_bounds {M : Type} {memory : runtime.platform.MemoryBuffer M}
    {view : M → Slice U8} {before staged : runtime.store.Store M}
    {module : runtime.compiler.ExecutableModule} {imports : Slice runtime.Extern}
    {trap : runtime.Trap}
    (origins : PrecommitOrigins memory view before staged module imports (.Trap trap))
    (retained : StagedPrefix before staged)
    (code : CodeInterpretation) (oldSyntax : StoreSyntax code before)
    (raw : ModuleBinary.Module)
    (elaborated : ModuleElaboration.Elaborates raw (ModuleElaboration.moduleOf raw))
    (typed : Module_ok (ModuleElaboration.moduleOf raw))
    (matched : ModuleElaboration.Matches module.module.env module.module.tail raw) :
    ∃ inst, staged.instances.val[before.instances.length]? = some inst ∧ inst.module = module ∧
      SpecExt.Wasm1.SegmentBoundsFailure
        (decodeStore view (installCode code before.instances.length (Code.sourceFunctions raw)) staged)
        (decodeInstance staged inst) (raw.elements.map ModuleElaboration.element)
        (raw.data.map ModuleData.translate) := by
  obtain ⟨charged, inst, shape, count, found, source, cause⟩ := origins.staging trap rfl
  have instMatched : ModuleElaboration.Matches inst.module.module.env inst.module.module.tail raw := by
    simpa only [source] using matched
  have fresh := instance_syntax_source code before.instances.length inst raw elaborated typed instMatched
  have allSyntax : StoreSyntax (installCode code before.instances.length (Code.sourceFunctions raw)) staged := by
    apply oldSyntax.staged (installCode_agrees before code (Code.sourceFunctions raw)) retained (Nat.le_of_eq count)
    intro actual lookup
    have equal : actual = inst := Option.some.inj (lookup.symm.trans found)
    exact equal ▸ fresh
  have storeWf : wf_store (decodeStore view (installCode code before.instances.length (Code.sourceFunctions raw)) staged) := by
    rw [← decodeStore_instance_items view _ staged charged]
    exact decodeStore_wf view _ _ shape (allSyntax.instances_eq rfl)
  have frameWf : wf_frame ⟨[], decodeInstance staged inst⟩ := by
    constructor
    · simp [Forall]
    · exact decodeInstance_wf _ _ _ _ fresh
  have failure := cause.source view _ staged inst trap storeWf frameWf
  obtain ⟨elements, datas⟩ := source_segments_raw inst raw instMatched
  exact ⟨inst, found, source, by simpa only [elements, datas] using failure⟩
end Exec.Store
