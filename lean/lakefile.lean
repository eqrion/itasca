import Lake
open Lake DSL

package itascaLean

require aeneas from "../vendor/aeneas-lean/backends/lean"

-- The equality helper is handwritten upstream. The specification below is
-- regenerated locally from the pinned SpecTec sources plus our source patches.
lean_lib SpecTecSupport where
  srcDir := "../vendor/spectec/spectec/src/test-lean-claude"
  globs := #[.one `ExtendedDeriveDecEq]

lean_lib SpecTecGenerated where
  srcDir := "SpecTec"
  globs := #[.one `«wasm2.0»]

@[default_target]
lean_lib Itasca
