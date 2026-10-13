import Itasca.Stream.SliceSound

/-!
# Public soundness and termination of `validate_module`

Termination and soundness of `module.validate_module` for both profiles, with Wasm 1.0
specializations (`wasm_*`). They are inherited from the streaming pipeline through the
contiguous-slice adapter (`Stream/SliceSound`). Acceptance yields `ModuleSound.Validated`;
completeness is in `Module/Completeness`.
-/

open Aeneas Aeneas.Std

namespace Itasca

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

end Itasca
