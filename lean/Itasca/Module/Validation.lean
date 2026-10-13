import Itasca.Stream.SliceSound

open Aeneas Aeneas.Std

namespace Itasca

/-- The selected profile shares the complete module validation pipeline. -/
theorem module.validate_module.profile_spec (data : Slice U8) (profile : ValidationProfile) :
    module.validate_module data profile ⦃ r => match r with
      | .Ok decoded => ModuleSound.Validated data decoded profile
      | .Err _ => True ⦄ :=
  stream.validate_module_slice.profile_spec data profile

theorem module.validate_module.profile_total (data : Slice U8) (profile : ValidationProfile) :
    ∃ r, module.validate_module data profile = .ok r :=
  stream.validate_module_slice.profile_total data profile

theorem module.validate_module.profile_sound (data : Slice U8) (decoded : module.Module)
    (profile : ValidationProfile)
    (h : module.validate_module data profile = .ok (.Ok decoded)) :
    ModuleSound.Validated data decoded profile :=
  stream.validate_module_slice.profile_sound data decoded profile h

/-- The public whole-module API uses the proved synchronous streaming adapter.
Arbitrary bytes return normally; accepted metadata and typing describe the
same independently encoded module. -/
theorem module.validate_module.wasm_spec (data : Slice U8) :
    module.validate_module data .Wasm1 ⦃ r => match r with
      | .Ok decoded => ModuleSound.Validated data decoded
      | .Err _ => True ⦄ :=
  module.validate_module.profile_spec data .Wasm1

/-- No well-formed-input or environment hypothesis is needed for termination. -/
theorem module.validate_module.wasm_total (data : Slice U8) :
    ∃ r, module.validate_module data .Wasm1 = .ok r :=
  module.validate_module.profile_total data .Wasm1

/-- Acceptance certifies one independently encoded, elaborated and typed
module, including the complete version profile and external-type metadata. -/
theorem module.validate_module.wasm_sound (data : Slice U8) (decoded : module.Module)
    (h : module.validate_module data .Wasm1 = .ok (.Ok decoded)) :
    ModuleSound.Validated data decoded :=
  module.validate_module.profile_sound data decoded .Wasm1 h

end Itasca
