import Itasca.Module.Definitions
import Itasca.Results.Definitions.Validation
import Itasca.Stream.Completeness

open WebAssembly

/-!
# Whole-module validation

Termination, soundness and completeness of `metadata.validate_module` for Wasm 2.0. These are inherited from the streaming pipeline through the
contiguous-slice adapter (`Stream/Completeness`, `Stream/SliceComplete`).

Acceptance yields `Module.Sound.Validated`. Completeness assumes the independent encoding within
the implementation limits, elaboration, `Module_ok` and the module restrictions; parser success
and cache validity are not assumed.
-/

open Aeneas Aeneas.Std

namespace Itasca

open Binary Module.Elaboration

/-- For every input, `metadata.validate_module` returns normally, and an accepted result
satisfies `Module.Sound.Validated`. Rejection carries no further guarantee. -/
theorem metadata.validate_module.spec (data : Slice U8) :
    metadata.validate_module data ⦃ result =>
      RustResult.Post result
        (onSuccess := fun decoded => Module.Sound.Validated data decoded) (onError := fun _ => True) ⦄ := by
  apply Aeneas.Std.WP.spec_mono (stream.validate_module_slice.spec data)
  intro result held
  cases result <;> exact held

/-- For every input, `metadata.validate_module` returns `.ok` without a modeled panic,
overflow or out-of-bounds access. The result may be either `.Ok` or `.Err`. -/
theorem metadata.validate_module.total (data : Slice U8) :
    ∃ r, metadata.validate_module data = .ok r :=
  stream.validate_module_slice.total data

/-- Acceptance certifies `Module.Sound.Validated` for the returned
module. -/
theorem metadata.validate_module.sound (data : Slice U8) (decoded : metadata.ModuleMetadata (alloc.sync.Arc metadata.CodeMetadata))
    (accepted : metadata.validate_module data = .ok (.Ok decoded)) :
    Module.Sound.Validated data decoded :=
  stream.validate_module_slice.sound data decoded accepted

/-- Independently encoded, elaborated and typed modules within the limits are accepted, and the returned environment and tail match the raw module. The signature caps
(`ModuleSignaturesWithinLimits`) are separate premises from language validity. -/
theorem metadata.validate_module.complete (data : Slice U8) (raw : Binary.Module)
    (encoded : ModuleEncodingWithinLimits raw data.val)
    (signatures : ModuleSignaturesWithinLimits raw)
    (elaborated : Elaborates raw (moduleOf raw))
    (typed : Module_ok (moduleOf raw)) (restricted : Restrictions raw) :
    ∃ decoded, metadata.validate_module data = .ok (.Ok decoded) ∧
      Matches decoded raw :=
  stream.validate_module_slice.complete data raw encoded signatures elaborated typed restricted

/-- `complete` together with `AccessorTypes`: `metadata.ModuleMetadataArcCodeMetadata.import_types` and
`metadata.ModuleMetadataArcCodeMetadata.export_types` on the returned environment give the types SpecTec assigns to the raw
module's imports and exports. -/
theorem metadata.validate_module.complete_with_metadata
    (data : Slice U8) (raw : Binary.Module)
    (encoded : ModuleEncodingWithinLimits raw data.val)
    (signatures : ModuleSignaturesWithinLimits raw)
    (elaborated : Elaborates raw (moduleOf raw))
    (typed : Module_ok (moduleOf raw)) (restricted : Restrictions raw) :
    ∃ decoded, metadata.validate_module data = .ok (.Ok decoded) ∧
      Matches decoded raw ∧ AccessorTypes decoded raw :=
  stream.validate_module_slice.complete_with_metadata data raw encoded signatures elaborated typed restricted

end Itasca
