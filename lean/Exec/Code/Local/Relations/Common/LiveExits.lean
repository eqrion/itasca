import Exec.Code.Local.Control.Common.StructuredLabels
namespace Exec.Code
open Aeneas.Std

/-- An empty reachable source continuation cannot inhabit a dead normal exit,
even if forward bytecode skips precede its final source position. -/
theorem CodeRel.empty_live {types functions returns locals code labels stack pc next final}
    (relation : CodeRel types functions returns locals code labels stack [] pc next final) :
    NormalLive labels := by
  generalize sourceEq : ([] : List instr) = source at relation
  induction relation with
  | nil labels stack pc bound live => exact live
  | skip forward fetched rest ih => exact ih sourceEq
  | linear => simp at sourceEq
  | block => simp at sourceEq
  | loop => simp at sourceEq
  | ifElse => simp at sourceEq
  | branch => simp at sourceEq
  | branchIf => simp at sourceEq
  | call => simp at sourceEq
  | unreachable => simp at sourceEq
  | return_ => simp at sourceEq

/-- A terminal block body need not compile an unreachable source suffix. -/
theorem CodeRel.dead_block {types functions returns locals code labels front params results
    after body bt pc normalExit branchExit next final}
    (signature : BlockSignature types bt params results)
    (bodyCode : CodeRel types functions returns locals code
      (⟨front, results, results, branchExit, normalExit, [], after, false, false⟩ :: labels)
      (front ++ params) body pc normalExit (front ++ results))
    (bounds : pc ≤ next ∧ next ≤ code.length) :
    CodeRel types functions returns locals code labels (front ++ params)
      (.BLOCK bt body :: after) pc next final :=
  .block signature bodyCode (by intro h; cases h) (by intro h; cases h) bounds

/-- A loop with no live fallthrough retains its back edge without requiring
bytecode for an unreachable suffix. -/
theorem CodeRel.dead_loop {types functions returns locals code labels front params results
    after body bt entry exit next final}
    (signature : BlockSignature types bt params results)
    (head : code[entry.val]? = some .LoopHead)
    (bodyCode : CodeRel types functions returns locals code
      (⟨front, params, results, entry, exit, [.LOOP bt body], after, false, true⟩ :: labels)
      (front ++ params) body (entry.val + 1) exit (front ++ results))
    (bounds : entry.val ≤ next ∧ next ≤ code.length) :
    CodeRel types functions returns locals code labels (front ++ params)
      (.LOOP bt body :: after) entry.val next final :=
  .loop signature head bodyCode (by intro h; cases h) bounds
end Exec.Code
