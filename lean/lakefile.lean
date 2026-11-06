import Lake
open Lake DSL

package itascaLean

-- Keep this revision in sync with toolchain.mk.
require aeneas from git "https://github.com/AeneasVerif/aeneas.git" @
  "557eff83ecef5083b98a52a94ca7fae63d6c1dab" / "backends/lean"

-- The equality helper is handwritten upstream. The specification below is
-- regenerated locally from the pinned SpecTec sources plus our source patches.
lean_lib SpecTecSupport where
  srcDir := "../vendor/spectec/spectec/src/test-lean-claude"
  globs := #[.one `ExtendedDeriveDecEq]

lean_lib SpecTecGenerated where
  srcDir := "SpecTec"
  globs := #[.one `«wasm2.0»]

@[default_target]
lean_lib Itasca where
  globs := #[.andSubmodules `Itasca]

-- Compile every handwritten specification extension and supporting proof.
lean_lib SpecExt where
  globs := #[.submodules `SpecExt]
