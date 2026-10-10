import Itasca.StreamSlice

open Aeneas Aeneas.Std

namespace Itasca

/-- The public whole-module API uses the proved synchronous streaming adapter.
Arbitrary bytes return normally; accepted metadata and typing describe the
same independently encoded module. -/
theorem module.validate_module.wasm_spec (data : Slice U8) :
    module.validate_module data ⦃ r => match r with
      | .Ok decoded => ModuleSound.Validated data decoded
      | .Err _ => True ⦄ :=
  stream.validate_module_slice.wasm_spec data

/-- No well-formed-input or environment hypothesis is needed for termination. -/
theorem module.validate_module.wasm_total (data : Slice U8) :
    ∃ r, module.validate_module data = .ok r :=
  stream.validate_module_slice.wasm_total data

/-- Acceptance certifies one independently encoded, elaborated and typed
module, including the complete version profile and external-type metadata. -/
theorem module.validate_module.wasm_sound (data : Slice U8) (decoded : module.Module)
    (h : module.validate_module data = .ok (.Ok decoded)) :
    ModuleSound.Validated data decoded :=
  stream.validate_module_slice.wasm_sound data decoded h

end Itasca
