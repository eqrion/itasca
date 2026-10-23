import Lean

/-!
# Axioms of the headline theorems

Run with `lake env lean --run scripts/trust.lean`. Imports each library's `Main` and prints the
axioms of every theorem declared in its `Results/` modules. Fails if one depends on anything
beyond `propext`, `Classical.choice` and `Quot.sound`. The library audits check every other
declaration.
-/

open Lean

def libraries : Array Name := #[`Itasca, `Exec]

def allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules (libraries.map fun lib => { module := lib ++ `Main }) {}
    (loadExts := false)
  let modules := env.header.moduleNames
  let mut failed := false
  for lib in libraries do
    let mut names : Array Name := #[]
    for (n, c) in env.constants.map₁.toList do
      if let some idx := env.getModuleIdxFor? n then
        if (lib ++ `Results).isPrefixOf modules[idx.toNat]! && c matches .thmInfo _ &&
            !n.isInternalDetail then
          names := names.push n
    IO.println s!"{lib} headline theorems:"
    for n in names.qsort (·.toString < ·.toString) do
      let (axioms, _) ← (collectAxioms n : CoreM _).toIO
        { fileName := "trust", fileMap := default } { env }
      IO.println s!"  {n}: {axioms}"
      failed := failed || axioms.any (!allowed.contains ·)
  return if failed then 1 else 0
