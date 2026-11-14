import Itasca.Stream.SyncComplete
import Itasca.Stream.SliceComplete

/-!
# Whole-module validation

Termination, soundness and completeness of `metadata.validate_module` for Wasm 2.0. These are inherited from the streaming pipeline through the
contiguous-slice adapter (`Stream/SliceSound`, `Stream/SliceComplete`).

Acceptance yields `ModuleSound.Validated`. Completeness assumes the independent encoding within
the implementation limits, elaboration, `Module_ok` and the module restrictions; parser success
and cache validity are not assumed.
-/

open Aeneas Aeneas.Std

namespace Itasca

open ModuleBinary ModuleElaboration

/-- For every input, `metadata.validate_module` returns normally, and an accepted result
satisfies `ModuleSound.Validated`. Rejection carries no further guarantee. -/
theorem metadata.validate_module.spec (data : Slice U8) :
    metadata.validate_module data ⦃ r => match r with
      | .Ok decoded => ModuleSound.Validated data decoded
      | .Err _ => True ⦄ :=
  stream.validate_module_slice.profile_spec data

/-- For every input, `metadata.validate_module` returns `.ok` without a modeled panic,
overflow or out-of-bounds access. The result may be either `.Ok` or `.Err`. -/
theorem metadata.validate_module.total (data : Slice U8) :
    ∃ r, metadata.validate_module data = .ok r :=
  stream.validate_module_slice.profile_total data

/-- Acceptance certifies `ModuleSound.Validated` for the returned
module. -/
theorem metadata.validate_module.sound (data : Slice U8) (decoded : metadata.Module)
    (h : metadata.validate_module data = .ok (.Ok decoded)) :
    ModuleSound.Validated data decoded :=
  stream.validate_module_slice.profile_sound data decoded h

/-- Independently encoded, elaborated and typed modules within the limits are accepted, and the returned environment and tail match the raw module. The signature caps
(`ModuleSignaturesWithinLimits`) are separate premises from language validity. -/
theorem metadata.validate_module.complete (data : Slice U8) (raw : ModuleBinary.Module)
    (hb : ModuleEncodingWithinLimits raw data.val)
    (hsignatures : ModuleSignaturesWithinLimits raw)
    (he : Elaborates raw (moduleOf raw))
    (ht : Module_ok (moduleOf raw)) (hp : Restrictions raw) :
    ∃ decoded, metadata.validate_module data = .ok (.Ok decoded) ∧
      Matches decoded.env decoded.tail raw :=
  stream.validate_module_slice.profile_complete data raw hb hsignatures he ht hp

/-- `complete` together with `AccessorTypes`: `metadata.import_types` and
`metadata.export_types` on the returned environment give the types SpecTec assigns to the raw
module's imports and exports. -/
theorem metadata.validate_module.complete_with_metadata
    (data : Slice U8) (raw : ModuleBinary.Module)
    (hb : ModuleEncodingWithinLimits raw data.val)
    (hsignatures : ModuleSignaturesWithinLimits raw)
    (he : Elaborates raw (moduleOf raw))
    (ht : Module_ok (moduleOf raw)) (hp : Restrictions raw) :
    ∃ decoded, metadata.validate_module data = .ok (.Ok decoded) ∧
      Matches decoded.env decoded.tail raw ∧ AccessorTypes decoded.env raw :=
  stream.validate_module_slice.profile_complete_with_metadata data raw hb hsignatures he ht hp

end Itasca
