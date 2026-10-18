import Exec.Code.Local.Control.Table.StructuredCodeWithTablesPoint
import Exec.Code.Local.Control.Common.StructuredLabels
namespace Exec.Code
open Aeneas.Std

theorem StructuredCodeWithTables.Targets.cons {emission types functions returns locals code jumpTables label labels next after}
    (outer : StructuredCodeWithTables.Targets emission types functions returns locals code jumpTables labels)
    (target : label.branchLive = true → StructuredCodeWithTables emission types functions returns locals code jumpTables labels (label.front ++ label.branchTypes)
      (label.cont ++ label.after) label.target.val next after)
    (aligned : label.branchLive = true → ExitAligned labels next)
    (root : label.branchLive = true → RootAligned code returns labels next after) :
    StructuredCodeWithTables.Targets emission types functions returns locals code jumpTables (label :: labels) := by
  intro depth found lookup live
  cases depth with
  | zero =>
    have same : found = label := by simpa using lookup.symm
    subst found
    exact ⟨next, after, by simpa using target live, by simpa using aligned live, by simpa using root live⟩
  | succ depth =>
    simpa using outer depth found (by simpa using lookup) live

theorem StructuredCodeWithTables.Normals.cons {emission types functions returns locals code jumpTables label labels next after}
    (outer : StructuredCodeWithTables.Normals emission types functions returns locals code jumpTables labels)
    (target : label.normalLive = true → StructuredCodeWithTables emission types functions returns locals code jumpTables labels (label.front ++ label.resultTypes)
      label.after label.normalExit next after)
    (aligned : label.normalLive = true → ExitAligned labels next)
    (root : label.normalLive = true → RootAligned code returns labels next after) :
    StructuredCodeWithTables.Normals emission types functions returns locals code jumpTables (label :: labels) := by
  intro depth found lookup live
  cases depth with
  | zero =>
    have same : found = label := by simpa using lookup.symm
    subst found
    exact ⟨next, after, by simpa using target live, by simpa using aligned live, by simpa using root live⟩
  | succ depth => simpa using outer depth found (by simpa using lookup) live

theorem StructuredCodeWithTables.Point.block_body {emission types functions returns locals code jumpTables labels front params results
    after body pc normalExit branchExit next final normalLive branchLive}
    (bodyCode : StructuredCodeWithTables emission types functions returns locals code jumpTables
      (⟨front, results, results, branchExit, normalExit, [], after, normalLive, branchLive⟩ :: labels)
      (front ++ params) body pc normalExit (front ++ results))
    (rest : normalLive = true → StructuredCodeWithTables emission types functions returns locals code jumpTables labels (front ++ results) after normalExit next final)
    (targetRest : branchLive = true → StructuredCodeWithTables emission types functions returns locals code jumpTables labels (front ++ results) after
      branchExit.val next final)
    (outer : StructuredCodeWithTables.Targets emission types functions returns locals code jumpTables labels)
    (normal : StructuredCodeWithTables.Normals emission types functions returns locals code jumpTables labels)
    (restAligned : ExitAligned labels next)
    (root : RootAligned code returns labels next final) :
    StructuredCodeWithTables.Point emission types functions returns locals code jumpTables
      (⟨front, results, results, branchExit, normalExit, [], after, normalLive, branchLive⟩ :: labels)
      (front ++ params) body pc normalExit (front ++ results) :=
  ⟨bodyCode, outer.cons (by simpa using targetRest) (fun _ => restAligned) (fun _ => root),
    normal.cons (by simpa using rest) (fun _ => restAligned) (fun _ => root), ExitAligned.cons _ _, RootAligned.cons _ _ _ _ _ _⟩

theorem StructuredCodeWithTables.Point.loop_body {emission types functions returns locals code jumpTables labels front params results
    after body bt entry exit next final normalLive}
    (signature : BlockSignature types bt params results)
    (head : code[entry.val]? = some .LoopHead)
    (bodyCode : StructuredCodeWithTables emission types functions returns locals code jumpTables
      (⟨front, params, results, entry, exit, [.LOOP bt body], after, normalLive, true⟩ :: labels)
      (front ++ params) body (entry.val + 1) exit (front ++ results))
    (rest : normalLive = true → StructuredCodeWithTables emission types functions returns locals code jumpTables labels (front ++ results) after exit next final)
    (bounds : entry.val ≤ next ∧ next ≤ code.length)
    (outer : StructuredCodeWithTables.Targets emission types functions returns locals code jumpTables labels)
    (normal : StructuredCodeWithTables.Normals emission types functions returns locals code jumpTables labels)
    (aligned : ExitAligned labels next)
    (root : RootAligned code returns labels next final) :
    StructuredCodeWithTables.Point emission types functions returns locals code jumpTables
      (⟨front, params, results, entry, exit, [.LOOP bt body], after, normalLive, true⟩ :: labels)
      (front ++ params) body (entry.val + 1) exit (front ++ results) := by
  exact ⟨bodyCode, outer.cons (fun _ => StructuredCodeWithTables.loop signature head bodyCode rest bounds) (fun _ => aligned) (fun _ => root),
    normal.cons rest (fun _ => aligned) (fun _ => root), ExitAligned.cons _ _, RootAligned.cons _ _ _ _ _ _⟩

/-- The target certificate is obtained from retained label evidence, while
inner labels are discarded exactly as the source branch discards them. -/
theorem StructuredCodeWithTables.Point.branch_target {emission types functions returns locals code jumpTables labels stack source pc next after
    depth label}
    (point : StructuredCodeWithTables.Point emission types functions returns locals code jumpTables labels stack source pc next after)
    (lookup : labels[depth]? = some label) (live : label.branchLive = true) :
    ∃ targetNext targetAfter, StructuredCodeWithTables.Point emission types functions returns locals code jumpTables
      (labels.drop (depth + 1)) (label.front ++ label.branchTypes)
      (label.cont ++ label.after) label.target.val targetNext targetAfter := by
  obtain ⟨targetNext, targetAfter, continuation, aligned, root⟩ := point.targets depth label lookup live
  exact ⟨targetNext, targetAfter, continuation, point.targets.drop (depth + 1),
    point.normal.drop (depth + 1), aligned, root⟩

/-- A selected then arm retains a skip only if normal fallthrough is live. -/
theorem StructuredCodeWithTables.if_then {emission types functions returns locals code jumpTables labels front params results
    after yes bt pc yesExit exit next final yesNormal yesBranch} {noEntry : U32}
    (signature : BlockSignature types bt params results)
    (yesCode : StructuredCodeWithTables emission types functions returns locals code jumpTables
      (⟨front, results, results, exit, yesExit, [], after, yesNormal, yesBranch⟩ :: labels)
      (front ++ params) yes pc yesExit (front ++ results))
    (skip : IfSkip code yesExit noEntry exit yesNormal)
    (order : noEntry.val ≤ exit.val)
    (rest : yesNormal = true ∨ yesBranch = true →
      StructuredCodeWithTables emission types functions returns locals code jumpTables labels (front ++ results) after exit.val next final)
    (bounds : pc ≤ next ∧ next ≤ code.length) :
    StructuredCodeWithTables emission types functions returns locals code jumpTables labels (front ++ params)
      (.BLOCK bt yes :: after) pc next final := by
  apply StructuredCodeWithTables.block signature yesCode ?_ (fun live => rest (Or.inr live)) bounds
  intro live
  cases skip with
  | direct normal otherwise => simpa only [normal] using rest (Or.inl live)
  | emitted fragment =>
    have skipLive : Segment code yesExit [.Jump exit] noEntry.val := by simpa only [live, ite_true] using fragment
    have forward : yesExit < exit.val := by
      obtain ⟨_, _, _, _, h⟩ := skipLive
      simp only [List.length_singleton] at h
      omega
    have fetched := skipLive.fetch (index := 0) (by rfl)
    simp only [Nat.add_zero] at fetched
    exact StructuredCodeWithTables.skip forward fetched (rest (Or.inl live))

/-- The ordinary block has coincident fallthrough and branch exits. -/
theorem StructuredCodeWithTables.ordinary_block {emission types functions returns locals code jumpTables labels front params results
    after body bt pc exit next final normalLive branchLive}
    (signature : BlockSignature types bt params results)
    (bodyCode : StructuredCodeWithTables emission types functions returns locals code jumpTables
      (⟨front, results, results, exit, exit.val, [], after, normalLive, branchLive⟩ :: labels)
      (front ++ params) body pc exit.val (front ++ results))
    (rest : normalLive = true ∨ branchLive = true →
      StructuredCodeWithTables emission types functions returns locals code jumpTables labels (front ++ results) after exit.val next final)
    (bounds : pc ≤ next ∧ next ≤ code.length) :
    StructuredCodeWithTables emission types functions returns locals code jumpTables labels (front ++ params) (.BLOCK bt body :: after) pc next final :=
  StructuredCodeWithTables.block signature bodyCode (fun live => rest (Or.inl live)) (fun live => rest (Or.inr live)) bounds


theorem StructuredCodeWithTables.Point.map_emission {first second types functions returns locals code jumpTables labels stack source pc next final}
    (point : StructuredCodeWithTables.Point first types functions returns locals code jumpTables labels stack source pc next final)
    (map : ∀ before instruction emitted after, first before instruction emitted after → second before instruction emitted after) :
    StructuredCodeWithTables.Point second types functions returns locals code jumpTables labels stack source pc next final := by
  refine ⟨point.current.map_emission map, ?_, ?_, point.exit, point.root⟩
  · intro depth label lookup live
    obtain ⟨next, after, relation, aligned, root⟩ := point.targets depth label lookup live
    exact ⟨next, after, relation.map_emission map, aligned, root⟩
  · intro depth label lookup live
    obtain ⟨next, after, relation, aligned, root⟩ := point.normal depth label lookup live
    exact ⟨next, after, relation.map_emission map, aligned, root⟩

theorem StructuredCodeWithTables.Point.of_legacy {types functions returns locals code jumpTables labels stack source pc next final}
    (point : StructuredPoint types functions returns locals code labels stack source pc next final) :
    StructuredCodeWithTables.Point (LinearEmission locals) types functions returns locals code jumpTables labels stack source pc next final := by
  refine ⟨StructuredCodeWithTables.of_legacy point.current, ?_, ?_, point.exit, point.root⟩
  · intro depth label lookup live
    obtain ⟨next, after, relation, aligned, root⟩ := point.targets depth label lookup live
    exact ⟨next, after, StructuredCodeWithTables.of_legacy relation, aligned, root⟩
  · intro depth label lookup live
    obtain ⟨next, after, relation, aligned, root⟩ := point.normal depth label lookup live
    exact ⟨next, after, StructuredCodeWithTables.of_legacy relation, aligned, root⟩
end Exec.Code
