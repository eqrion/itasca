import Itasca.Stream.SliceSound
import Itasca.Stream.SliceComplete

/-!
# Whole-module validation

Termination, soundness and completeness of `metadata.validate_module` for both profiles. These are inherited from the streaming pipeline through the
contiguous-slice adapter (`Stream/SliceSound`, `Stream/SliceComplete`).

Acceptance yields `ModuleSound.Validated`. Completeness assumes the independent encoding within
the implementation limits, elaboration, `Module_ok` and the profile restrictions; parser success
and cache validity are not assumed.
-/

open Aeneas Aeneas.Std

namespace Itasca

open ModuleBinary ModuleElaboration

/-- For every input and profile, `metadata.validate_module` returns normally, and an accepted result
satisfies `ModuleSound.Validated`. Rejection carries no further guarantee. -/
theorem metadata.validate_module.profile_spec (data : Slice U8) (profile : ValidationProfile) :
    metadata.validate_module data profile ⦃ r => match r with
      | .Ok decoded => ModuleSound.Validated data decoded profile
      | .Err _ => True ⦄ :=
  stream.validate_module_slice.profile_spec data profile

/-- For every input and profile, `metadata.validate_module` returns `.ok` without a modeled panic,
overflow or out-of-bounds access. The result may be either `.Ok` or `.Err`. -/
theorem metadata.validate_module.profile_total (data : Slice U8) (profile : ValidationProfile) :
    ∃ r, metadata.validate_module data profile = .ok r :=
  stream.validate_module_slice.profile_total data profile

/-- Acceptance under the selected profile certifies `ModuleSound.Validated` for the returned
module. -/
theorem metadata.validate_module.profile_sound (data : Slice U8) (decoded : metadata.Module)
    (profile : ValidationProfile)
    (h : metadata.validate_module data profile = .ok (.Ok decoded)) :
    ModuleSound.Validated data decoded profile :=
  stream.validate_module_slice.profile_sound data decoded profile h

/-- Independently encoded, elaborated and typed modules within the limits are accepted under either
profile, and the returned environment and tail match the raw module. The signature caps
(`ModuleSignaturesWithinLimits`) are separate premises from language validity. -/
theorem metadata.validate_module.profile_complete (data : Slice U8) (raw : ModuleBinary.Module)
    (profile : ValidationProfile)
    (hb : ModuleEncodingWithinLimits raw data.val profile)
    (hsignatures : ModuleSignaturesWithinLimits raw)
    (he : Elaborates raw (moduleOf raw))
    (ht : Module_ok (moduleOf raw)) (hp : Profile raw profile) :
    ∃ decoded, metadata.validate_module data profile = .ok (.Ok decoded) ∧
      Matches decoded.env decoded.tail raw :=
  stream.validate_module_slice.profile_complete data raw profile hb hsignatures he ht hp

/-- `profile_complete` together with `AccessorTypes`: `metadata.import_types` and
`metadata.export_types` on the returned environment give the types SpecTec assigns to the raw
module's imports and exports. -/
theorem metadata.validate_module.profile_complete_with_metadata
    (data : Slice U8) (raw : ModuleBinary.Module) (profile : ValidationProfile)
    (hb : ModuleEncodingWithinLimits raw data.val profile)
    (hsignatures : ModuleSignaturesWithinLimits raw)
    (he : Elaborates raw (moduleOf raw))
    (ht : Module_ok (moduleOf raw)) (hp : Profile raw profile) :
    ∃ decoded, metadata.validate_module data profile = .ok (.Ok decoded) ∧
      Matches decoded.env decoded.tail raw ∧ AccessorTypes decoded.env raw :=
  stream.validate_module_slice.profile_complete_with_metadata data raw profile hb hsignatures he ht hp

end Itasca
