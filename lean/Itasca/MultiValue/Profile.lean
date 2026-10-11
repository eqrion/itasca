import Itasca.Generated.Funs

open Aeneas Aeneas.Std

namespace Itasca

/-- Explicit Wasm 1.0 selection is definitionally the established validator,
    so its existing soundness, totality and completeness contracts transfer. -/
theorem validate_module_with_profile.wasm1_eq (data : Slice U8) :
    validate_module_with_profile data .Wasm1 = module.validate_module data := rfl

end Itasca
