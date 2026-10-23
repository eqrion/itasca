import Itasca.Stream.SliceSound
import Itasca.Stream.SliceComplete

/-!
# Whole-module validation

Termination, soundness and completeness of `module.validate_module` for both profiles, with Wasm
1.0 specializations (`wasm_*`). They are inherited from the streaming pipeline through the
contiguous-slice adapter (`Stream/SliceSound`, `Stream/SliceComplete`).

Acceptance yields `ModuleSound.Validated`. Completeness assumes the independent encoding within
the implementation limits, elaboration, `Module_ok` and the profile restrictions; parser success
and cache validity are not assumed.
-/

open Aeneas Aeneas.Std

namespace Itasca

open ModuleBinary ModuleElaboration

/-- For every input and profile, `module.validate_module` returns normally, and an accepted result
satisfies `ModuleSound.Validated`. Rejection carries no further guarantee. -/
theorem module.validate_module.profile_spec (data : Slice U8) (profile : ValidationProfile) :
    module.validate_module data profile ⦃ r => match r with
      | .Ok decoded => ModuleSound.Validated data decoded profile
      | .Err _ => True ⦄ :=
  stream.validate_module_slice.profile_spec data profile

/-- For every input and profile, `module.validate_module` returns `.ok` without a modeled panic,
overflow or out-of-bounds access. The result may be either `.Ok` or `.Err`. -/
theorem module.validate_module.profile_total (data : Slice U8) (profile : ValidationProfile) :
    ∃ r, module.validate_module data profile = .ok r :=
  stream.validate_module_slice.profile_total data profile

/-- Acceptance under the selected profile certifies `ModuleSound.Validated` for the returned
module. -/
theorem module.validate_module.profile_sound (data : Slice U8) (decoded : module.Module)
    (profile : ValidationProfile)
    (h : module.validate_module data profile = .ok (.Ok decoded)) :
    ModuleSound.Validated data decoded profile :=
  stream.validate_module_slice.profile_sound data decoded profile h

/-- Independently encoded, elaborated and typed modules within the limits are accepted under either
profile, and the returned environment and tail match the raw module. The signature caps
(`ModuleSignaturesWithinLimits`) are separate premises from language validity. -/
theorem module.validate_module.profile_complete (data : Slice U8) (raw : ModuleBinary.Module)
    (profile : ValidationProfile)
    (hb : ModuleEncodingWithinLimits raw data.val profile)
    (hsignatures : ModuleSignaturesWithinLimits raw)
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
    (hsignatures : ModuleSignaturesWithinLimits raw)
    (he : Elaborates raw (moduleOf raw))
    (ht : Module_ok (moduleOf raw)) (hp : Profile raw profile) :
    ∃ decoded, module.validate_module data profile = .ok (.Ok decoded) ∧
      Matches decoded.env decoded.tail raw ∧ AccessorTypes decoded.env raw :=
  stream.validate_module_slice.profile_complete_with_metadata data raw profile hb hsignatures he ht hp

/-- Wasm 1.0 specialization of `profile_spec`. Arbitrary bytes return normally, and accepted
metadata and typing describe the same independently encoded module. -/
theorem module.validate_module.wasm_spec (data : Slice U8) :
    module.validate_module data .Wasm1 ⦃ r => match r with
      | .Ok decoded => ModuleSound.Validated data decoded
      | .Err _ => True ⦄ :=
  module.validate_module.profile_spec data .Wasm1

/-- Wasm 1.0 specialization of `profile_total`. No well-formedness or environment hypothesis is
needed. -/
theorem module.validate_module.wasm_total (data : Slice U8) :
    ∃ r, module.validate_module data .Wasm1 = .ok r :=
  module.validate_module.profile_total data .Wasm1

/-- Wasm 1.0 specialization of `profile_sound`. Acceptance certifies one independently encoded,
elaborated and typed module, including the profile restrictions and the external-type metadata. -/
theorem module.validate_module.wasm_sound (data : Slice U8) (decoded : module.Module)
    (h : module.validate_module data .Wasm1 = .ok (.Ok decoded)) :
    ModuleSound.Validated data decoded :=
  module.validate_module.profile_sound data decoded .Wasm1 h

/-- Wasm 1.0 specialization of `profile_complete`. Every independently encoded and elaborated module
satisfying the implementation limits and `Module_ok` is accepted, and the returned metadata
represents that same module. -/
theorem module.validate_module.wasm_complete (data : Slice U8) (raw : ModuleBinary.Module)
    (hb : ModuleEncodingWithinLimits raw data.val)
    (hsignatures : ModuleSignaturesWithinLimits raw)
    (he : Elaborates raw (moduleOf raw))
    (ht : Module_ok (moduleOf raw)) (hp : Profile raw) :
    ∃ decoded, module.validate_module data .Wasm1 = .ok (.Ok decoded) ∧
      Matches decoded.env decoded.tail raw :=
  module.validate_module.profile_complete data raw .Wasm1 hb hsignatures he ht hp

/-- Wasm 1.0 specialization of `profile_complete_with_metadata`. -/
theorem module.validate_module.wasm_complete_with_metadata
    (data : Slice U8) (raw : ModuleBinary.Module)
    (hb : ModuleEncodingWithinLimits raw data.val)
    (hsignatures : ModuleSignaturesWithinLimits raw)
    (he : Elaborates raw (moduleOf raw))
    (ht : Module_ok (moduleOf raw)) (hp : Profile raw) :
    ∃ decoded, module.validate_module data .Wasm1 = .ok (.Ok decoded) ∧
      Matches decoded.env decoded.tail raw ∧ AccessorTypes decoded.env raw :=
  module.validate_module.profile_complete_with_metadata data raw .Wasm1 hb hsignatures he ht hp

end Itasca
