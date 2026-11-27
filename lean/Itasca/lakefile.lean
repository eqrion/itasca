import Lake

open Lake DSL System

package Itasca

require WebAssembly from "../WebAssembly"
require ItascaRust from "../ItascaRust"

@[default_target]
lean_lib Itasca where
  globs := #[.submodules `Itasca]

target audit pkg : FilePath := do
  -- Use Lake's module inventory so the audit follows each library's globs.
  let modules ← #[`Itasca, `ItascaRust, `WebAssembly].flatMapM fun name => do
    let some lib ← findLeanLib? name
      | error s!"Missing library {name} in the audit workspace"
    let modules ← (← lib.modules.fetch).await
    return modules ++ lib.rootModules.filter (fun root => !modules.any (·.name == root.name))
  let modules := modules.qsort fun a b => Lean.Name.lt a.name b.name
  let imports := String.join <| modules.toList.map (fun mod => s!"import {mod.name}\n")
  let artifacts := Job.mixArray (← modules.mapM fun mod => mod.leanArts.fetch)
  let checker ← inputTextFile (pkg.dir / "Audit.lean")
  let config ← inputTextFile pkg.configFile
  let report := pkg.buildDir / "audit.txt"
  let header ← Lean.parseImports' imports "audit"
  -- Resolve imports through Lake, including artifacts in its cache.
  let setup ← setupServerModule "audit" (pkg.buildDir / "Audit.lean") (some header)
  (artifacts.mix config).bindM (sync := true) fun _ =>
    (checker.zipWith Prod.mk setup).mapM fun (checkerPath, setup) => do
      addPureTrace imports "audit imports"
      buildFileUnlessUpToDate' (text := true) report do
        let source := imports ++ (← IO.FS.readFile checkerPath)
        let lean ← getLean
        let env ← getAugmentedEnv
        let result ← IO.FS.withTempFile fun handle path => do
          handle.putStr (Lean.toJson setup).compress
          handle.flush
          IO.Process.output
            {cmd := lean.toString, args := #["--stdin", "--setup", path.toString], env}
            (some source)
        if result.exitCode != 0 then
          error (result.stdout ++ result.stderr)
        createParentDirs report
        IO.FS.writeFile report result.stdout
      logInfo (← IO.FS.readFile report).trimAsciiEnd.toString
      return report
