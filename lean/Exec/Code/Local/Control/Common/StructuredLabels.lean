import Exec.Code.Local.Control.Common.StructuredComposition
namespace Exec.Code
open Aeneas.Std

theorem LabelContinuations.cons {types functions returns locals code label labels next after}
    (outer : LabelContinuations types functions returns locals code labels)
    (target : label.branchLive = true → CodeRel types functions returns locals code labels (label.front ++ label.branchTypes)
      (label.cont ++ label.after) label.target.val next after)
    (aligned : label.branchLive = true → ExitAligned labels next)
    (root : label.branchLive = true → RootAligned code returns labels next after) :
    LabelContinuations types functions returns locals code (label :: labels) := by
  intro depth found lookup live
  cases depth with
  | zero =>
    have same : found = label := by simpa using lookup.symm
    subst found
    exact ⟨next, after, by simpa using target live, by simpa using aligned live, by simpa using root live⟩
  | succ depth =>
    simpa using outer depth found (by simpa using lookup) live

theorem NormalContinuations.cons {types functions returns locals code label labels next after}
    (outer : NormalContinuations types functions returns locals code labels)
    (target : label.normalLive = true → CodeRel types functions returns locals code labels (label.front ++ label.resultTypes)
      label.after label.normalExit next after)
    (aligned : label.normalLive = true → ExitAligned labels next)
    (root : label.normalLive = true → RootAligned code returns labels next after) :
    NormalContinuations types functions returns locals code (label :: labels) := by
  intro depth found lookup live
  cases depth with
  | zero =>
    have same : found = label := by simpa using lookup.symm
    subst found
    exact ⟨next, after, by simpa using target live, by simpa using aligned live, by simpa using root live⟩
  | succ depth => simpa using outer depth found (by simpa using lookup) live

theorem ExitAligned.cons (label : LabelTarget) (labels : List LabelTarget) :
    ExitAligned (label :: labels) label.normalExit := by
  intro found lookup
  have same : found = label := by simpa using lookup.symm
  subst found
  rfl

theorem StructuredPoint.block_body {types functions returns locals code labels front params results
    after body pc normalExit branchExit next final normalLive branchLive}
    (bodyCode : CodeRel types functions returns locals code
      (⟨front, results, results, branchExit, normalExit, [], after, normalLive, branchLive⟩ :: labels)
      (front ++ params) body pc normalExit (front ++ results))
    (rest : normalLive = true → CodeRel types functions returns locals code labels (front ++ results) after normalExit next final)
    (targetRest : branchLive = true → CodeRel types functions returns locals code labels (front ++ results) after
      branchExit.val next final)
    (outer : LabelContinuations types functions returns locals code labels)
    (normal : NormalContinuations types functions returns locals code labels)
    (restAligned : ExitAligned labels next)
    (root : RootAligned code returns labels next final) :
    StructuredPoint types functions returns locals code
      (⟨front, results, results, branchExit, normalExit, [], after, normalLive, branchLive⟩ :: labels)
      (front ++ params) body pc normalExit (front ++ results) :=
  ⟨bodyCode, outer.cons (by simpa using targetRest) (fun _ => restAligned) (fun _ => root),
    normal.cons (by simpa using rest) (fun _ => restAligned) (fun _ => root), ExitAligned.cons _ _, RootAligned.cons _ _ _ _ _ _⟩

theorem StructuredPoint.loop_body {types functions returns locals code labels front params results
    after body bt entry exit next final normalLive}
    (signature : BlockSignature types bt params results)
    (head : code[entry.val]? = some .LoopHead)
    (bodyCode : CodeRel types functions returns locals code
      (⟨front, params, results, entry, exit, [.LOOP bt body], after, normalLive, true⟩ :: labels)
      (front ++ params) body (entry.val + 1) exit (front ++ results))
    (rest : normalLive = true → CodeRel types functions returns locals code labels (front ++ results) after exit next final)
    (bounds : entry.val ≤ next ∧ next ≤ code.length)
    (outer : LabelContinuations types functions returns locals code labels)
    (normal : NormalContinuations types functions returns locals code labels)
    (aligned : ExitAligned labels next)
    (root : RootAligned code returns labels next final) :
    StructuredPoint types functions returns locals code
      (⟨front, params, results, entry, exit, [.LOOP bt body], after, normalLive, true⟩ :: labels)
      (front ++ params) body (entry.val + 1) exit (front ++ results) := by
  exact ⟨bodyCode, outer.cons (fun _ => CodeRel.loop signature head bodyCode rest bounds) (fun _ => aligned) (fun _ => root),
    normal.cons rest (fun _ => aligned) (fun _ => root), ExitAligned.cons _ _, RootAligned.cons _ _ _ _ _ _⟩

/-- The target certificate is obtained from retained label evidence, while
inner labels are discarded exactly as the source branch discards them. -/
theorem StructuredPoint.branch_target {types functions returns locals code labels stack source pc next after
    depth label}
    (point : StructuredPoint types functions returns locals code labels stack source pc next after)
    (lookup : labels[depth]? = some label) (live : label.branchLive = true) :
    ∃ targetNext targetAfter, StructuredPoint types functions returns locals code
      (labels.drop (depth + 1)) (label.front ++ label.branchTypes)
      (label.cont ++ label.after) label.target.val targetNext targetAfter := by
  obtain ⟨targetNext, targetAfter, continuation, aligned, root⟩ := point.targets depth label lookup live
  exact ⟨targetNext, targetAfter, continuation, point.targets.drop (depth + 1),
    point.normal.drop (depth + 1), aligned, root⟩

/-- A selected then arm retains a skip only if normal fallthrough is live. -/
theorem CodeRel.if_then {types functions returns locals code labels front params results
    after yes bt pc yesExit exit next final yesNormal yesBranch} {noEntry : U32}
    (signature : BlockSignature types bt params results)
    (yesCode : CodeRel types functions returns locals code
      (⟨front, results, results, exit, yesExit, [], after, yesNormal, yesBranch⟩ :: labels)
      (front ++ params) yes pc yesExit (front ++ results))
    (skip : IfSkip code yesExit noEntry exit yesNormal)
    (order : noEntry.val ≤ exit.val)
    (rest : yesNormal = true ∨ yesBranch = true →
      CodeRel types functions returns locals code labels (front ++ results) after exit.val next final)
    (bounds : pc ≤ next ∧ next ≤ code.length) :
    CodeRel types functions returns locals code labels (front ++ params)
      (.BLOCK bt yes :: after) pc next final := by
  apply CodeRel.block signature yesCode ?_ (fun live => rest (Or.inr live)) bounds
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
    exact CodeRel.skip forward fetched (rest (Or.inl live))

/-- The ordinary block has coincident fallthrough and branch exits. -/
theorem CodeRel.ordinary_block {types functions returns locals code labels front params results
    after body bt pc exit next final normalLive branchLive}
    (signature : BlockSignature types bt params results)
    (bodyCode : CodeRel types functions returns locals code
      (⟨front, results, results, exit, exit.val, [], after, normalLive, branchLive⟩ :: labels)
      (front ++ params) body pc exit.val (front ++ results))
    (rest : normalLive = true ∨ branchLive = true →
      CodeRel types functions returns locals code labels (front ++ results) after exit.val next final)
    (bounds : pc ≤ next ∧ next ≤ code.length) :
    CodeRel types functions returns locals code labels (front ++ params) (.BLOCK bt body :: after) pc next final :=
  CodeRel.block signature bodyCode (fun live => rest (Or.inl live)) (fun live => rest (Or.inr live)) bounds

end Exec.Code
