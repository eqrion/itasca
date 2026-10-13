import Itasca.Module.Validation
import Itasca.Stream.SliceComplete

/-!
# Public completeness of `validate_module`

Acceptance of independently encoded, elaborated and typed modules by `module.validate_module`
(`profile_complete`, `profile_complete_with_metadata`) and their Wasm 1.0 specializations
(`wasm_complete`, `wasm_complete_with_metadata`). The premises are the independent encoding
within the implementation limits, elaboration, `Module_ok` and the profile restrictions. Parser
success and cache validity are not assumed. Soundness is in `Module/Validation`.
-/

open Aeneas Aeneas.Std

namespace Itasca

open ModuleBinary ModuleElaboration

/-- Independently encoded, elaborated and typed modules within the limits are accepted under either
profile, and the returned environment and tail match the raw module. The signature caps
(`ModuleSignaturesWithinLimits`) are separate premises from language validity. -/
theorem module.validate_module.profile_complete (data : Slice U8) (raw : ModuleBinary.Module)
    (profile : ValidationProfile)
    (hb : ModuleEncodingWithinLimits raw data.val profile)
    (hsignatures : ModuleSignaturesWithinLimits raw profile)
    (he : Elaborates raw (moduleOf raw))
    (ht : Module_ok (moduleOf raw)) (hp : Profile raw profile) :
    ∃ decoded, module.validate_module data profile = .ok (.Ok decoded) ∧
      Matches decoded.env decoded.tail raw :=
  stream.validate_module_slice.profile_complete data raw profile hb hsignatures he ht hp

/-- `profile_complete` together with `AccessorTypes`: `module.import_types` and
`module.export_types` on the returned environment give the types SpecTec assigns to the raw
module's imports and exports. -/
theorem module.validate_module.profile_complete_with_metadata
    (data : Slice U8) (raw : ModuleBinary.Module) (profile : ValidationProfile)
    (hb : ModuleEncodingWithinLimits raw data.val profile)
    (hsignatures : ModuleSignaturesWithinLimits raw profile)
    (he : Elaborates raw (moduleOf raw))
    (ht : Module_ok (moduleOf raw)) (hp : Profile raw profile) :
    ∃ decoded, module.validate_module data profile = .ok (.Ok decoded) ∧
      Matches decoded.env decoded.tail raw ∧ AccessorTypes decoded.env raw :=
  stream.validate_module_slice.profile_complete_with_metadata data raw profile hb hsignatures he ht hp

/-- Wasm 1.0 specialization of `profile_complete`. Every independently encoded and elaborated module
satisfying the implementation limits and `Module_ok` is accepted, and the returned metadata
represents that same module. Signature caps do not apply to Wasm 1.0. -/
theorem module.validate_module.wasm_complete (data : Slice U8) (raw : ModuleBinary.Module)
    (hb : ModuleEncodingWithinLimits raw data.val)
    (he : Elaborates raw (moduleOf raw))
    (ht : Module_ok (moduleOf raw)) (hp : Profile raw) :
    ∃ decoded, module.validate_module data .Wasm1 = .ok (.Ok decoded) ∧
      Matches decoded.env decoded.tail raw :=
  module.validate_module.profile_complete data raw .Wasm1 hb (fun _ _ => trivial) he ht hp

/-- Wasm 1.0 specialization of `profile_complete_with_metadata`. -/
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
