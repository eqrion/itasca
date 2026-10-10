import Itasca.ModuleTraceDefs
import Itasca.ModuleCustomObservation

open Aeneas Aeneas.Std

namespace Itasca.ModuleTrace

/-- A concrete accepting recorder for all custom-section arguments. -/
def customRecorder : module.ModuleVisitor (List Event) where
  on_custom_section events chunk := .ok (.Ok (), events ++ [.custom chunk])

theorem customRecorder_records : RecordsCustom customRecorder id := by
  intro v chunk v' h
  simpa [customRecorder, Eq.comm] using h

theorem customRecorder_accepts : ModuleTail.HooksAccept customRecorder := by
  intro events chunk
  exact ⟨events ++ [.custom chunk], rfl⟩

end Itasca.ModuleTrace
