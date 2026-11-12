import Itasca.Main

/-!
Trust audit for the headline theorems. Run from `lean/` after `lake build Itasca`:

    lake env lean scripts/Audit.lean > metrics/audit.txt

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

def headline : List Name := [
  `Itasca.metadata.validate_module.profile_spec,
  `Itasca.metadata.validate_module.profile_total,
  `Itasca.metadata.validate_module.profile_sound,
  `Itasca.metadata.validate_module.profile_complete,
  `Itasca.metadata.validate_module.profile_complete_with_metadata,
  `Itasca.stream.validate_streaming.profile_sound,
  `Itasca.stream.validate_streaming.profile_total,
  `Itasca.stream.validate_streaming.profile_complete,
  `Itasca.Runtime.runtime.compiler.compile_with.profile_sound,
  `Itasca.Runtime.runtime.compiler.compile_with.profile_spec,
  `Itasca.Runtime.runtime.compiler.compile_with.profile_complete,
  `Itasca.Runtime.runtime.compiler.compile_default_with.profile_spec,
  `Itasca.Runtime.runtime.store.instantiate.Store.instantiate_with.spec,
  `Itasca.Runtime.runtime.interp.invoke_with.behaves,
  `Itasca.Runtime.runtime.interp.invoke_with.terminates,
  `Itasca.Runtime.runtime.interp.invoke_with.no_spurious_errors]

def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => `_local

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

def audit : CoreM Unit := do
  let env ← getEnv
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
    let used := info.type.getUsedConstants ++ (info.value?.map (·.getUsedConstants)).getD #[]
    if used.any (unproved.contains ·) then offenders := offenders.push declName
  unless offenders.isEmpty do
    throwError "declarations using sorry or an unproved specification theorem: {offenders}"
  IO.println "no handwritten declaration uses sorry or an unproved specification theorem"
  let roots := headline.foldl (fun acc r => match env.find? r with
    | some info => acc ++ info.type.getUsedConstants.toList
    | none => acc) []
  let all := cone env roots {}
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
        rows := rows.push (category m, m, r.range.pos.line, n, r.range.endPos.line - r.range.pos.line + 1)
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
