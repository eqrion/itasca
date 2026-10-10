import Itasca.ModuleValidation
import Itasca.StreamSliceCompleteness

open Aeneas Aeneas.Std

namespace Itasca

open ModuleBinary ModuleElaboration

/-- Every independently encoded and elaborated Wasm 1.0 module satisfying the
implementation's limits and generated typing is accepted. The returned metadata
represents that same input module, without parser-success or cache assumptions. -/
theorem module.validate_module.wasm_complete (data : Slice U8) (raw : ModuleBinary.Module)
    (hb : ModuleEncodingWithinLimits raw data.val)
    (he : Elaborates raw (moduleOf raw))
    (ht : Module_ok (moduleOf raw)) (hp : Profile raw) :
    ∃ decoded, module.validate_module data = .ok (.Ok decoded) ∧
      Matches decoded.env decoded.tail raw :=
  stream.validate_module_slice.wasm_complete data raw hb he ht hp

/-- The successful public type accessors describe the same independently
specified module as the accepted declarations and data. -/
theorem module.validate_module.wasm_complete_with_metadata
    (data : Slice U8) (raw : ModuleBinary.Module)
    (hb : ModuleEncodingWithinLimits raw data.val)
    (he : Elaborates raw (moduleOf raw))
    (ht : Module_ok (moduleOf raw)) (hp : Profile raw) :
    ∃ decoded, module.validate_module data = .ok (.Ok decoded) ∧
      Matches decoded.env decoded.tail raw ∧ AccessorTypes decoded.env raw :=
  stream.validate_module_slice.wasm_complete_with_metadata data raw hb he ht hp

end Itasca
