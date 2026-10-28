import Exec.Store.Initialization.SegmentSyntheticSource
import Exec.Store.Initialization.SegmentInitializeShape
import Exec.Code.Local.Relations.Common.SegmentFlowSource

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std SpecExt

/-- Ordered source instructions for the retained element and data initialization programs. -/
def segmentModuleSource (module : runtime.compiler.ExecutableModule) : List admininstr :=
  (Spec.Segment.elementPrograms (module.module.env.elements.val.map (fun entry =>
    Itasca.ModuleElaboration.element (Itasca.ModuleEnv.rawElement entry)))).flatten.map admininstr_instr ++
  (Spec.Segment.dataPrograms (module.module.tail.data.val.map (fun entry =>
    Itasca.ModuleData.translate (Itasca.ModuleData.raw entry)))).flatten.map admininstr_instr

/-- Source program indexed by the independent binary module witness. -/
def segmentRawSource (raw : Itasca.ModuleBinary.Module) : List admininstr :=
  (Spec.Segment.elementPrograms (raw.elements.map Itasca.ModuleElaboration.element)).flatten.map admininstr_instr ++
  (Spec.Segment.dataPrograms (raw.data.map Itasca.ModuleData.translate)).flatten.map admininstr_instr

theorem segmentModuleSource_raw (module : runtime.compiler.ExecutableModule)
    (raw : Itasca.ModuleBinary.Module)
    (matched : Itasca.ModuleElaboration.Matches module.module.env module.module.tail raw) :
    segmentModuleSource module = segmentRawSource raw := by
  have elements := congrArg Itasca.ModuleBinary.Module.elements matched.1
  have datas := congrArg Itasca.ModuleBinary.Module.data matched.1
  simp only [segmentRawSource, elements, datas, Itasca.ModuleElaboration.fromEnv,
    List.map_map, Function.comp_def,segmentModuleSource]

end Itasca.Runtime.Store
