import Itasca.Profile.BinaryUnique

/-!
# Decoding uniqueness

A byte string encodes at most one raw module. Custom section placement and omitted empty sections
introduce no ambiguity. Neither typing nor implementation limits are premises, so a module that
`metadata.validate_module` accepts has exactly one decoding.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- A complete module has one decoding under the WebAssembly Core 2.0 grammar. -/
theorem Profile.module_unique {x y : ModuleBinary.Module}
    {bytes : List U8}
    (hx : ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding) x bytes)
    (hy : ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding) y bytes) : x = y :=
  ModuleBinary.ModuleEncodingWith.unique (Profile.code_prefix_unique) hx hy

end Itasca
