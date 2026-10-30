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
  globs := #[.one `Wasm2Prefix, .one `«wasm2.0», .one `Wasm2Builtins]

@[default_target]
lean_lib Itasca

-- Handwritten specification extensions have an independent audit.
lean_lib SpecExt

-- This checker loads the current audit dynamically; compiling the graph walk
-- avoids interpreting it again on each optional `just dead` run.
lean_exe reachability where
  root := `scripts.reachability
