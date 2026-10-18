import Exec.Code.Local.Source.SourceFunctionTyping
import Exec.Spec.SegmentPrograms
import Itasca.Module.Elab.SectionInversion
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- The generated data-mode typing rule fixes active memory indices to zero. -/
theorem source_data_single_memory {C : context} (segment : ModuleBinary.Data)
    (typed : Data_ok C (ModuleData.translate segment)) :
    Spec.Segment.singleMemoryData (ModuleData.translate segment) := by
  have mode := ModuleElaboration.data_mode_typed typed
  cases equal : segment.mode with
  | Passive => simp [Spec.Segment.singleMemoryData, ModuleData.translate, ModuleSegments.dataMode, equal]
  | Active index offset =>
    change Datamode_ok C (ModuleSegments.dataMode segment.mode) at mode
    rw [equal] at mode
    have bound := (ModuleElaboration.datamode_active_properties mode).1
    simpa only [Spec.Segment.singleMemoryData, ModuleData.translate, equal, ModuleSegments.dataMode] using bound

theorem source_datas_single_memory (raw : ModuleBinary.Module)
    (elaborates : ModuleElaboration.Elaborates raw (ModuleElaboration.moduleOf raw))
    (typed : Module_ok (ModuleElaboration.moduleOf raw)) :
    ∀ segment ∈ raw.data.map ModuleData.translate, Spec.Segment.singleMemoryData segment := by
  intro segment member
  obtain ⟨rawSegment, present, rfl⟩ := List.mem_map.mp member
  exact source_data_single_memory rawSegment ((ModuleElaboration.sections_of_typing elaborates typed).data rawSegment present)
end Exec.Code
