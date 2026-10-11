import Itasca.Module.ModuleValidation
import Itasca.Stream.StreamSliceCompleteness

open Aeneas Aeneas.Std

namespace Itasca

open ModuleBinary ModuleElaboration

/-- Independently encoded, typed modules are accepted under either supported
profile; signature allocation caps remain separate from language validity. -/
theorem module.validate_module.profile_complete (data : Slice U8) (raw : ModuleBinary.Module)
    (profile : ValidationProfile)
    (hb : ModuleEncodingWithinLimits raw data.val profile)
    (hsignatures : ModuleSignaturesWithinLimits raw profile)
    (he : Elaborates raw (moduleOf raw))
    (ht : Module_ok (moduleOf raw)) (hp : Profile raw profile) :
    ∃ decoded, module.validate_module data profile = .ok (.Ok decoded) ∧
      Matches decoded.env decoded.tail raw :=
  stream.validate_module_slice.profile_complete data raw profile hb hsignatures he ht hp

theorem module.validate_module.profile_complete_with_metadata
    (data : Slice U8) (raw : ModuleBinary.Module) (profile : ValidationProfile)
    (hb : ModuleEncodingWithinLimits raw data.val profile)
    (hsignatures : ModuleSignaturesWithinLimits raw profile)
    (he : Elaborates raw (moduleOf raw))
    (ht : Module_ok (moduleOf raw)) (hp : Profile raw profile) :
    ∃ decoded, module.validate_module data profile = .ok (.Ok decoded) ∧
      Matches decoded.env decoded.tail raw ∧ AccessorTypes decoded.env raw :=
  stream.validate_module_slice.profile_complete_with_metadata data raw profile hb hsignatures he ht hp

/-- Every independently encoded and elaborated Wasm 1.0 module satisfying the
implementation's limits and generated typing is accepted. The returned metadata
represents that same input module, without parser-success or cache assumptions. -/
theorem module.validate_module.wasm_complete (data : Slice U8) (raw : ModuleBinary.Module)
    (hb : ModuleEncodingWithinLimits raw data.val)
    (he : Elaborates raw (moduleOf raw))
    (ht : Module_ok (moduleOf raw)) (hp : Profile raw) :
    ∃ decoded, module.validate_module data .Wasm1 = .ok (.Ok decoded) ∧
      Matches decoded.env decoded.tail raw :=
  module.validate_module.profile_complete data raw .Wasm1 hb (fun _ _ => trivial) he ht hp

/-- The successful public type accessors describe the same independently
specified module as the accepted declarations and data. -/
theorem module.validate_module.wasm_complete_with_metadata
    (data : Slice U8) (raw : ModuleBinary.Module)
    (hb : ModuleEncodingWithinLimits raw data.val)
    (he : Elaborates raw (moduleOf raw))
    (ht : Module_ok (moduleOf raw)) (hp : Profile raw) :
    ∃ decoded, module.validate_module data .Wasm1 = .ok (.Ok decoded) ∧
      Matches decoded.env decoded.tail raw ∧ AccessorTypes decoded.env raw :=
  module.validate_module.profile_complete_with_metadata data raw .Wasm1 hb
    (fun _ _ => trivial) he ht hp

end Itasca
