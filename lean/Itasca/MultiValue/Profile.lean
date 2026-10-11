import Itasca.Generated.Funs

open Aeneas Aeneas.Std

namespace Itasca

/-- Explicit Wasm 1.0 selection is definitionally the established validator,
    so its existing soundness, totality and completeness contracts transfer. -/
theorem validate_module_with_profile.wasm1_eq (data : Slice U8) :
    validate_module_with_profile data .Wasm1 = module.validate_module data .Wasm1 := rfl

/-- Both spellings use the same profile-aware streaming adapter. -/
theorem validate_module_with_profile.eq (data : Slice U8) (profile : ValidationProfile) :
    validate_module_with_profile data profile = module.validate_module data profile := rfl

end Itasca
