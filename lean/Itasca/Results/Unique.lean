import Itasca.Profile.BinaryUnique

/-!
# Decoding uniqueness

A byte string encodes at most one raw module. Custom section placement and omitted empty sections
introduce no ambiguity. Neither typing nor implementation limits are premises, so a module that
`metadata.validate_module` accepts has exactly one decoding.
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- A complete module has one decoding under either supported profile. -/
theorem Profile.module_unique {profile : ValidationProfile} {x y : ModuleBinary.Module}
    {bytes : List U8}
    (hx : ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding profile) x bytes profile)
    (hy : ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding profile) y bytes profile) : x = y :=
  ModuleBinary.ModuleEncodingWith.unique (Profile.code_prefix_unique profile) hx hy

/-- A byte string encodes at most one raw module under `ModuleEncoding` (Wasm 1.0). -/
theorem ModuleBinary.ModuleEncoding.unique {x y : ModuleBinary.Module} {bytes : List U8}
    (hx : ModuleBinary.ModuleEncoding x bytes) (hy : ModuleBinary.ModuleEncoding y bytes) : x = y :=
  ModuleBinary.ModuleEncodingWith.unique ModuleBinary.code_prefix_unique hx hy

end Itasca
