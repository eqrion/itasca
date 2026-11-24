import Itasca.Main

/-!
Trust audit for the headline theorems. After `just prove`, run from the repository root:

    just audit --check --no-build

The driver imports every handwritten Itasca and SpecExt module, including unused
implementation modules and examples, before evaluating these checks. Use the driver
for whole-project coverage and explicit artifact checking or refresh.

The output has two parts.

1. Axioms. One line per headline theorem. Any axiom other than `propext`, `Classical.choice` and
   `Quot.sound` makes this file fail with an error. So does any declaration in `Itasca` or
   `SpecExt` that uses `sorry` or one of the three unproved theorems of the generated specification.
2. Statement cone. Every declaration a reader must understand to know what the headline theorems
   say: the constants in each theorem's type, followed through the bodies of definitions and the
   constructors of inductive types, but never through proofs. A change in this list is a change in
   what the project claims, so review the diff of `metrics/audit.txt` in every change.

This file is not part of the `Itasca` library and is never imported.
-/

open Lean

/-- Reviewed exact public root registry; discovery below rejects drift. -/
def headline : List Name := (include_str "public-results.txt").splitOn "\n"
  |>.filter (fun s => !s.isEmpty) |>.map (fun s => s.toName)

def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => `_local

/-- Direct dependencies for the global forbidden-reference scan include opaque
proof bodies. ConstantInfo.value? hides theorem and opaque values by default. -/
def dependenciesIncludingProofs (info : ConstantInfo) : Array Name :=
  info.type.getUsedConstants ++
    ((info.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]

/- Regression: a proof-only dependency must be visible for theorem and opaque
payloads as well as ordinary definitions. These are data fixtures, never added
to the environment as declarations. -/
#guard (dependenciesIncludingProofs (.thmInfo {
  toConstantVal := { «name» := `audit_probe, levelParams := [], type := mkConst ``True }
  value := mkConst ``True.intro })).contains ``True.intro
#guard (dependenciesIncludingProofs (.opaqueInfo {
  toConstantVal := { «name» := `audit_probe, levelParams := [], type := mkConst ``True }
  value := mkConst ``True.intro, isUnsafe := false })).contains ``True.intro
#guard (dependenciesIncludingProofs (.defnInfo {
  toConstantVal := { «name» := `audit_probe, levelParams := [], type := mkConst ``True }
  value := mkConst ``True.intro, hints := .opaque, safety := .safe })).contains ``True.intro
#guard (dependenciesIncludingProofs (.thmInfo {
  toConstantVal := { «name» := `audit_probe, levelParams := [], type := mkConst ``True }
  value := mkConst ``True.intro })).contains ``True

/-- Modules whose definitions are expanded. Library definitions are trusted as given. -/
def projectModule (m : Name) : Bool :=
  let r := m.getRoot
  r == `Itasca || r == `SpecExt || r == `«wasm2.0» || r == `ExtendedDeriveDecEq

partial def cone (env : Environment) (stack : List Name) (seen : NameSet) : NameSet :=
  match stack with
  | [] => seen
  | n :: rest =>
    if seen.contains n then cone env rest seen else
    let seen := seen.insert n
    if !projectModule (moduleOf env n) then cone env rest seen else
    match env.find? n with
    | none => cone env rest seen
    | some info =>
      let deps := info.type.getUsedConstants ++ (match info with
        | .defnInfo d => d.value.getUsedConstants
        | .opaqueInfo d => d.value.getUsedConstants
        | .inductInfo d => d.ctors.toArray
        | _ => #[])
      cone env (deps.toList ++ rest) seen

def category (m : Name) : String :=
  match m.components.map toString with
  | "Itasca" :: "Generated" :: _ => "extracted"
  | "Itasca" :: _ => "handwritten"
  | "SpecExt" :: _ => "handwritten"
  | _ => "spectec"


/-- Keep the human audit's original inclusive source-line convention. -/
def declarationLineCount (r : DeclarationRange) : Nat :=
  r.endPos.line - r.pos.line + 1

/- Regression: a single-line declaration must never be reported as zero lines. -/
#guard declarationLineCount default == 1

/-- Stable expression encoding. Binder labels and metadata are display-only; binder kinds,
universe names, constants, literals and every expression node are retained. -/
partial def exprJson : Expr → Json
  | .bvar i => toJson ("bvar", i)
  | .fvar i => toJson ("fvar", i.name.toString)
  | .mvar i => toJson ("mvar", i.name.toString)
  | .sort l => toJson ("sort", reprStr l)
  | .const n ls => toJson ("const", n.toString, ls.map reprStr)
  | .app f a => toJson ("app", exprJson f, exprJson a)
  | .lam _ t b k => toJson ("lam", reprStr k, exprJson t, exprJson b)
  | .forallE _ t b k => toJson ("forall", reprStr k, exprJson t, exprJson b)
  | .letE _ t v b nd => toJson ("let", nd, exprJson t, exprJson v, exprJson b)
  | .lit l => toJson ("lit", reprStr l)
  | .mdata _ e => exprJson e
  | .proj n i e => toJson ("proj", n.toString, i, exprJson e)

def infoKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def directDependencies (info : ConstantInfo) : Array Name :=
  info.type.getUsedConstants ++ (match info with
    | .defnInfo d => d.value.getUsedConstants
    | .opaqueInfo d => d.value.getUsedConstants
    | .inductInfo d => d.ctors.toArray
    | _ => #[])

/-- JSONL export is separated from the human report by ITASCA_AUDIT_JSON.
The export contains external leaves as well as every semantic cone declaration. -/
def exportManifest (env : Environment) (all : NameSet) (path : String) (includeRoots : Bool := true) (slim : Bool := false) : CoreM Unit := do
  if !slim then
    let mut sourceRanges : Array Json := #[]
    for (n, info) in env.constants.map₁.toList do
      let m := moduleOf env n
      if m.getRoot != `Itasca || category m != "handwritten" then continue
      if let some r ← findDeclarationRanges? n then
        sourceRanges := sourceRanges.push <| Json.mkObj [
          ("name", toJson n.toString), ("module", toJson m.toString),
          ("kind", toJson (infoKind info)),
          ("range", Json.mkObj [
            ("start", toJson (r.range.pos.line, r.range.pos.column + 1)),
            ("end", toJson (r.range.endPos.line, r.range.endPos.column + 1))])]
    IO.FS.writeFile (path ++ ".ranges.json") ((toJson sourceRanges).compress ++ "\n")
  let mut selected := all.toList ++ if includeRoots then headline else []
  if slim then
    -- Use the actual environment Name, preserving numeric/private components.
    for (n, _) in env.constants.map₁.toList do
      if (moduleOf env n).toString.startsWith "Itasca.Results.Definitions." then
        selected := n :: selected
  let names := selected.mergeSort (fun a b => a.toString ≤ b.toString)
  let mut records : Array Json := #[]
  let mut missing : Array String := #[]
  let mut seen : NameSet := {}
  for n in names do
    if seen.contains n then continue
    seen := seen.insert n
    let some info := env.find? n |
      missing := missing.push n.toString
      continue
    let m := moduleOf env n
    let range ← findDeclarationRanges? n
    let rangeJson := match range with
      | none => Json.null
      | some r => Json.mkObj [
          ("start", toJson (r.range.pos.line, r.range.pos.column + 1)),
          ("end", toJson (r.range.endPos.line, r.range.endPos.column + 1)),
          ("selection", toJson (r.selectionRange.pos.line, r.selectionRange.pos.column + 1))]
    let parent := match info with
      | .ctorInfo c => some c.induct
      | .recInfo c => c.all.head?
      | _ => none
    let foundation := if !projectModule m then "external"
      else if m.getRoot == `SpecExt then "specext"
      else category m
    let mut fields : List (String × Json) := [
      ("name", toJson n.toString), ("name_identity", toJson (reprStr n)),
      ("module", toJson m.toString),
      ("reading", toJson (all.contains n || headline.contains n)),
      ("kind", toJson (infoKind info)), ("range", rangeJson),
      ("parent", toJson (parent.map toString)), ("category", toJson foundation),
      ("root", toJson (headline.contains n)),
      ("dependencies", toJson ((directDependencies info).toList.map toString)),
      ("levels", toJson (info.levelParams.map toString)),
      ("reducibility", match info with
        | .defnInfo d => toJson (match d.hints with | .opaque => "opaque" | .abbrev => "abbrev" | .regular h => "regular:" ++ toString h)
        | _ => Json.null)]
    if !slim then
      fields := fields ++ [
        ("type", exprJson info.type),
        ("value", match info with
          | .defnInfo d => exprJson d.value
          | .opaqueInfo d => exprJson d.value
          | _ => Json.null)]
    else
      if info matches .thmInfo _ then
        if (all.contains n || headline.contains n) && m.getRoot == `Itasca && category m == "handwritten" then
          let statement ← withOptions (fun ppOptions => ppOptions.set `pp.maxSteps (1000000 : Nat)) <|
            (Meta.ppExpr info.type).run'
          fields := fields ++ [("statement", toJson statement.pretty)]
      if m.toString.startsWith "Itasca.Results.Definitions." then
        let proofDeps := match info with
          | .thmInfo d => d.value.getUsedConstants.toList.map toString
          | _ => []
        fields := fields ++ [("proof_dependencies", toJson proofDeps)]
    records := records.push <| Json.mkObj fields
  IO.FS.writeFile path ((Json.mkObj [("schema", toJson (1 : Nat)), ("missing", toJson missing),
    ("roots", toJson ((if includeRoots then headline else []).map toString)), ("declarations", toJson records)]).compress ++ "\n")


def publicDeclarations (candidates : Array (Name × Name × DeclarationRanges)) : List Name := candidates.toList.filterMap fun (n, m, ranges) =>
    -- A generated theorem sharing a parent's source block is not another export.
    if candidates.any (fun (parent, pm, pr) => pm == m && parent != n &&
        pr.range == ranges.range && parent.isPrefixOf n) then none else some n

/- Regression: a new explicit result must be discovered, while a generated theorem
sharing its parent range is not an additional public root. -/
#guard publicDeclarations #[
  (`Itasca.newResult, `Itasca.Results.Test, default),
  (`Itasca.newResult.match_1, `Itasca.Results.Test, default)] == [`Itasca.newResult]

/-- Definition helpers share Results ownership but are not exported theorem roots. -/
def publicResultModule (module : Name) : Bool :=
  module.toString.startsWith "Itasca.Results." &&
    module != `Itasca.Results.Definitions &&
    !module.toString.startsWith "Itasca.Results.Definitions."

#guard publicResultModule `Itasca.Results.Validate
#guard !publicResultModule `Itasca.Results.Definitions
#guard !publicResultModule `Itasca.Results.Definitions.Validation
#guard !publicResultModule `Itasca.Runtime.Validation

def audit : CoreM Unit := do
  let env ← getEnv
  let mut candidates : Array (Name × Name × DeclarationRanges) := #[]
  for (n, info) in env.constants.map₁.toList do
    let m := moduleOf env n
    unless publicResultModule m do continue
    unless info matches .thmInfo _ do continue
    if n.isInternalDetail then continue
    if let some ranges ← findDeclarationRanges? n then
      candidates := candidates.push (n, m, ranges)
  let discovered := publicDeclarations candidates
  let missing := discovered.filter (!headline.contains ·)
  let stale := headline.filter (!discovered.contains ·)
  unless missing.isEmpty && stale.isEmpty do
    throwError "public root registry mismatch; unregistered: {missing}; no longer exported: {stale}"
  IO.println "# Axioms"
  let mut failed := false
  for theoremName in headline do
    unless env.contains theoremName do
      throwError "headline theorem {theoremName} does not exist; update scripts/Audit.lean"
    let axioms := (← collectAxioms theoremName).toList
    let extra := axioms.filter (!allowedAxioms.contains ·)
    IO.println s!"{theoremName}: {if extra.isEmpty then "standard axioms only" else toString extra}"
    if !extra.isEmpty then failed := true
  if failed then throwError "a headline theorem depends on a non-standard axiom"
  -- No handwritten declaration may use `sorryAx` or the unproved theorems of the generated
  -- specification, whether or not a headline theorem depends on it.
  let unproved : List Name := [``sorryAx, `Step_is_wf, `Step_read_is_wf, `Step_pure_is_wf]
  let mut offenders : Array Name := #[]
  for (declName, info) in env.constants.map₁.toList do
    let root := (moduleOf env declName).getRoot
    unless root == `Itasca || root == `SpecExt do continue
    let used := dependenciesIncludingProofs info
    if used.any (unproved.contains ·) then offenders := offenders.push declName
  unless offenders.isEmpty do
    throwError "declarations using sorry or an unproved specification theorem: {offenders}"
  IO.println "no handwritten declaration uses sorry or an unproved specification theorem"
  let roots := headline.foldl (fun acc r => match env.find? r with
    | some info => acc ++ info.type.getUsedConstants.toList
    | none => acc) []
  let all := cone env roots {}
  if (← IO.getEnv "ITASCA_AUDIT_REQUIRE_INTERFACE") == some "1" then
    let mut escaped : Array Name := #[]
    for n in all.toList do
      let m := moduleOf env n
      if m.getRoot != `Itasca || category m != "handwritten" then continue
      if m.toString.startsWith "Itasca.Results.Definitions." then continue
      match env.find? n with
      | some (.thmInfo _) =>
        unless publicResultModule m do
          escaped := escaped.push n
      | some (.axiomInfo _) => pure ()
      | some _ => escaped := escaped.push n
      | none => throwError "missing reading-cone declaration {n}"
    unless escaped.isEmpty do
      throwError "reading vocabulary misplaced: semantic declarations require Results.Definitions; theorem statements require public definition or theorem modules: {escaped}"
  if let some path ← IO.getEnv "ITASCA_AUDIT_JSON" then
    exportManifest env all path
  if let some path ← IO.getEnv "ITASCA_AUDIT_SLIM_JSON" then
    exportManifest env all path (slim := true)
  -- One row per source declaration. Auxiliary declarations share their parent's range.
  let mut rows : Array (String × Name × Nat × Name × Nat) := #[]
  let mut seen : Std.HashSet (Name × Nat) := {}
  for n in all.toList do
    if n.isInternalDetail then continue
    let m := moduleOf env n
    unless projectModule m do continue
    if let some r ← findDeclarationRanges? n then
      let key := (m, r.range.pos.line)
      unless seen.contains key do
        seen := seen.insert key
        rows := rows.push (category m, m, r.range.pos.line, n, declarationLineCount r.range)
  let sorted := rows.qsort fun a b =>
    a.1 < b.1 || (a.1 == b.1 && (a.2.1.toString < b.2.1.toString ||
      (a.2.1 == b.2.1 && a.2.2.1 < b.2.2.1)))
  IO.println "\n# Statement cone totals (declarations, lines)"
  for kind in ["handwritten", "spectec", "extracted"] do
    let chosen := sorted.filter (·.1 == kind)
    IO.println s!"{kind}: {chosen.size} declarations, {chosen.foldl (fun acc r => acc + r.2.2.2.2) 0} lines"
  IO.println "\n# Handwritten statement cone (module, declaration, lines)"
  for (kind, m, _, n, len) in sorted do
    if kind == "handwritten" then IO.println s!"{m}\t{n}\t{len}"

#eval audit
