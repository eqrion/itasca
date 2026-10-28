import Lean

/-!
# Reachability from the headline theorems

Run with `lake env lean --run scripts/reachability.lean [--check] [--cone NAMES]... [OUT]`. Imports the
`Itasca` audit and walks the constants used by every declaration of the root modules; the runtime
proofs keep validator facts alive. Reports the source declarations that no root reaches, grouped
by module.
`OUT` receives the full report, with source lines, and standard output a summary. With `--check`, the run
fails if a module outside `allowlist` has no reachable declaration. Generated and
audit modules are not reported.

Each `--cone NAMES` (comma-separated root declarations) also reports the exclusive cone of that
group: the source declarations reachable from the group but from no other root, with their line
count and the modules they make up entirely.
-/

open Lean

def libraries : Array Name := #[`Itasca]

/-- The reachability roots besides `Examples/`. -/
def roots : Array Name := #[
  `Itasca.Main, `Itasca.Results.Validate, `Itasca.Results.Stream, `Itasca.Results.Batch,
  `Itasca.Results.Trace, `Itasca.Results.Unique,
  `Itasca.Results.Compile, `Itasca.Results.Instantiate, `Itasca.Results.Invoke]

/-- Modules kept without a reachable declaration, each with its reason. -/
def allowlist : Array Name := #[
  -- Specification sanity checks, built by `make checkpoint` and `spec-check`.
  `Itasca.Spec.Checks,
  -- Characterize the generated judgments changed by the SpecTec host-typing and
  -- export-membership patches; cited by the patch descriptions in `README.md`.
  `Itasca.Runtime.Spec.Typing.HostTyping, `Itasca.Runtime.Spec.ModuleMembership]

def isRoot (mod : Name) : Bool :=
  roots.contains mod || libraries.any fun lib => (lib ++ `Examples).isPrefixOf mod

def libraryOf (mod : Name) : Option Name :=
  libraries.find? fun lib =>
    lib.isPrefixOf mod && !(lib ++ `Generated).isPrefixOf mod && mod != lib ++ `Audit

/-- Syntax, macros, simprocs and other metaprograms run during elaboration, so proof terms
never mention them. Their modules count as used. -/
def isMeta (c : ConstantInfo) : Bool :=
  match c.type.getForallBody.getAppFn.constName? with
  | some head => (`Lean).isPrefixOf head
  | none => false

/-- Declarations a user writes, as opposed to compiler-generated companions. -/
def isSource (env : Environment) (n : Name) (c : ConstantInfo) : Bool :=
  let range? := declRangeExt.find? env n
  range?.isSome &&
  -- Attributes and `where` clauses add declarations inside their owner's range.
  !(match range?, declRangeExt.find? env n.getPrefix with
    | some r, some p => env.getModuleIdxFor? n == env.getModuleIdxFor? n.getPrefix &&
        p.range.pos.line ≤ r.range.pos.line && r.range.endPos.line ≤ p.range.endPos.line
    | _, _ => false) &&
  let n := (privateToUserName? n).getD n
  !n.isInternalDetail && !c.isCtor && !(c matches .recInfo _ | .quotInfo _) &&
  !isAuxRecursor env n && !isNoConfusion env n && !(env.isProjectionFn n) &&
  !Meta.isMatcherCore env n &&
  !n.components.any (fun | .str _ s => s.startsWith "match_" || s == "splitter" | _ => false) &&
  match n with
  | .str _ s => !((s.startsWith "eq_" && (s.drop 3).all Char.isDigit) ||
      s ∈ ["eq_def", "eq_unfold", "mvcgen_spec", "injEq", "inj", "sizeOf_spec", "induct",
        "induct_unfolding", "mutual_induct", "fun_cases"])
  | _ => true

def kind : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .inductInfo _ => "inductive"
  | .opaqueInfo _ => "opaque"
  | _ => "def"

/-- Every constant reachable from `start`, constructors of reached inductives included. -/
def reach (env : Environment) (start : Array Name) : NameHashSet := Id.run do
  let mut stack := start
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
  return seen

def parseArgs : List String → Bool × Array (Array Name) × Option String
  | [] => (false, #[], none)
  | "--check" :: rest => let (_, cones, out) := parseArgs rest; (true, cones, out)
  | "--cone" :: names :: rest =>
    let (check, cones, out) := parseArgs rest
    (check, #[(names.splitOn ",").toArray.map String.toName] ++ cones, out)
  | path :: rest => let (check, cones, _) := parseArgs rest; (check, cones, some path)

def main (args : List String) : IO UInt32 := do
  let (check, cones, out?) := parseArgs args
  initSearchPath (← findSysroot)
  let env ← importModules (libraries.map fun lib => { module := lib ++ `Audit }) {}
    (loadExts := false)
  let modules := env.header.moduleNames
  let modOf (n : Name) : Option Name := (env.getModuleIdxFor? n).map (modules[·.toNat]!)
  for r in roots ++ allowlist do
    unless modules.contains r do
      IO.eprintln s!"missing root or allowlisted module {r}"; return 2
  let mut rootDecls : Array Name := #[]
  for (n, _) in env.constants.map₁.toList do
    if let some m := modOf n then
      if isRoot m then rootDecls := rootDecls.push n
  let seen := reach env rootDecls
  let mut unused : Std.HashMap Name (Array (String × Name)) := {}
  let mut total : Std.HashMap Name Nat := {}
  for (n, c) in env.constants.map₁.toList do
    let some m := modOf n | continue
    unless (libraryOf m).isSome && !isRoot m && isSource env n c do continue
    total := total.insert m (total.getD m 0 + 1)
    unless seen.contains n || isMeta c do
      unused := unused.insert m ((unused.getD m #[]).push (kind c, n))
  let sorted := unused.toArray.qsort (fun a b => a.1.toString < b.1.toString)
  let isDead (m : Name) (ds : Array (String × Name)) := ds.size == total.getD m 0
  let mut out := ""
  for (m, ds) in sorted do
    out := out ++ s!"{m}{if isDead m ds then " (unused)" else ""}\n"
    for (k, n) in ds.qsort (fun a b => a.2.toString < b.2.toString) do
      let lines := (declRangeExt.find? env n).elim "" fun r =>
        s!" {r.range.pos.line}-{r.range.endPos.line}"
      out := out ++ s!"  {k} {n}{lines}\n"
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
  for group in cones do
    if let some n := group.find? (!env.contains ·) then
      IO.eprintln s!"unknown cone root {n}"; return 2
    let others := reach env (rootDecls.filter (!group.contains ·))
    let mut decls := 0
    let mut theorems := 0
    let mut lines := 0
    let mut perModule : Std.HashMap Name Nat := {}
    for n in (reach env group).toArray do
      if others.contains n then continue
      let some c := env.find? n | continue
      let some m := modOf n | continue
      unless (libraryOf m).isSome && !isRoot m && isSource env n c do continue
      decls := decls + 1
      if c matches .thmInfo _ then theorems := theorems + 1
      if let some r := declRangeExt.find? env n then
        lines := lines + r.range.endPos.line + 1 - r.range.pos.line
      perModule := perModule.insert m (perModule.getD m 0 + 1)
    let whole := perModule.toArray.filter fun (m, k) => k == total.getD m 0
    IO.println s!"cone {", ".intercalate (group.toList.map toString)}: {decls} declarations ({theorems} theorems, {lines} lines) in {perModule.size} modules, {whole.size} modules entirely"
  return if failed then 1 else 0
