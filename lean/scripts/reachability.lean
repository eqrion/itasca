import Lean

/-!
# Reachability from the headline theorems

Run with `lake env lean --run scripts/reachability.lean [--check] [OUT]`. Imports the
`Itasca` and `Exec` audits and walks the constants used by every declaration of the
root modules of both libraries; the execution proofs keep validator facts alive.
Reports the source declarations of each library that no root reaches, grouped by module.
`OUT` receives the full report and standard output a summary. With `--check`, the run
fails if a module outside `allowlist` has no reachable declaration. Generated and
audit modules are not reported.
-/

open Lean

def libraries : Array Name := #[`Itasca, `Exec]

/-- The reachability roots besides `Examples/`. -/
def roots : Array Name := #[
  `Itasca.Module.Validation, `Itasca.Module.Completeness,
  `Itasca.Stream.DriverSound, `Itasca.Stream.DriverTotal, `Itasca.Stream.DriverComplete,
  `Itasca.Stream.BatchTotal, `Itasca.Stream.BatchComplete,
  `Exec.Theorems.Compilation, `Exec.Theorems.CompilationComplete,
  `Exec.Theorems.Invocation.PublicExecutableWorldInvocation,
  `Exec.Theorems.Invocation.PublicExecutableWorldResources,
  `Exec.Theorems.Invocation.PublicExecutableWorldDivergence,
  `Exec.Theorems.Invocation.PublicWorldChosenMatches,
  `Exec.Theorems.Progress.ExecutableWorldFinite,
  `Exec.Theorems.Instantiation.InstantiateExecutableWorldSource,
  `Exec.Theorems.Instantiation.InstantiateExecutableWorldRecordingResources,
  `Exec.Theorems.Host.Open.Completeness.ChosenSourceCompleteness,
  `Exec.Theorems.Host.Open.Completeness.ReturningRecovery,
  `Exec.Theorems.Host.Open.Native.NativeChosenSourceInvocation]

/-- Modules kept without a reachable declaration, each with its reason. -/
def allowlist : Array Name := #[]

def isRoot (mod : Name) : Bool :=
  roots.contains mod || libraries.any fun lib => (lib ++ `Examples).isPrefixOf mod

def libraryOf (mod : Name) : Option Name :=
  libraries.find? fun lib =>
    lib.isPrefixOf mod && !(lib ++ `Generated).isPrefixOf mod && mod != lib ++ `Audit

/-- Declarations a user writes, as opposed to compiler-generated companions. -/
def isSource (env : Environment) (n : Name) (c : ConstantInfo) : Bool :=
  !n.isInternalDetail && !c.isCtor && !(c matches .recInfo _ | .quotInfo _) &&
  !isAuxRecursor env n && !isNoConfusion env n && !(env.isProjectionFn n) &&
  !Meta.isMatcherCore env n &&
  match n with
  | .str _ s => !((s.startsWith "eq_" && (s.drop 3).all Char.isDigit) ||
      s ∈ ["eq_def", "eq_unfold", "injEq", "inj", "sizeOf_spec", "induct",
        "induct_unfolding", "mutual_induct", "fun_cases"])
  | _ => true

def kind : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .inductInfo _ => "inductive"
  | .opaqueInfo _ => "opaque"
  | _ => "def"

def main (args : List String) : IO UInt32 := do
  let check := args.contains "--check"
  let out? := (args.filter (· != "--check")).head?
  initSearchPath (← findSysroot)
  let env ← importModules (libraries.map fun lib => { module := lib ++ `Audit }) {}
    (loadExts := false)
  let modules := env.header.moduleNames
  let modOf (n : Name) : Option Name := (env.getModuleIdxFor? n).map (modules[·.toNat]!)
  for r in roots ++ allowlist do
    unless modules.contains r do
      IO.eprintln s!"missing root or allowlisted module {r}"; return 2
  let mut stack : Array Name := #[]
  for (n, _) in env.constants.map₁.toList do
    if let some m := modOf n then
      if isRoot m then stack := stack.push n
  let mut seen : NameHashSet := {}
  while h : stack.size > 0 do
    let n := stack.back
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some c := env.find? n | continue
    for u in c.getUsedConstantsAsSet do
      unless seen.contains u do stack := stack.push u
    if let .inductInfo i := c then
      for ctor in i.ctors do stack := stack.push ctor
  let mut unused : Std.HashMap Name (Array (String × Name)) := {}
  let mut total : Std.HashMap Name Nat := {}
  for (n, c) in env.constants.map₁.toList do
    let some m := modOf n | continue
    unless (libraryOf m).isSome && !isRoot m && isSource env n c do continue
    total := total.insert m (total.getD m 0 + 1)
    unless seen.contains n do
      unused := unused.insert m ((unused.getD m #[]).push (kind c, n))
  let sorted := unused.toArray.qsort (fun a b => a.1.toString < b.1.toString)
  let isDead (m : Name) (ds : Array (String × Name)) := ds.size == total.getD m 0
  let mut out := ""
  for (m, ds) in sorted do
    out := out ++ s!"{m}{if isDead m ds then " (unused)" else ""}\n"
    for (k, n) in ds.qsort (fun a b => a.2.toString < b.2.toString) do
      out := out ++ s!"  {k} {n}\n"
  if let some (path : String) := out? then IO.FS.writeFile path out
  let mut failed := false
  for lib in libraries do
    let mine := sorted.filter fun (m, _) => lib.isPrefixOf m
    let decls := mine.foldl (· + ·.2.size) 0
    let theorems := mine.foldl (fun k (_, ds) => k + (ds.filter (·.1 == "theorem")).size) 0
    let dead := mine.filter fun (m, ds) => isDead m ds && !allowlist.contains m
    IO.println s!"{lib}: {decls} unused declarations ({theorems} theorems) in {mine.size} modules; {dead.size} modules unused"
    for (m, _) in dead do
      IO.println s!"unused module {m}"
    failed := failed || (check && !dead.isEmpty)
  return if failed then 1 else 0
