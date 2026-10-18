import Exec.Code.Local.Relations.Common.StatefulEmission
namespace Exec.Code
open Aeneas.Std

/-- Appending metadata preserves every existing pair-table lookup. -/
theorem StatefulPair.append {pairs op a b entry} (extra : List (U32 × U32))
    (pair : StatefulPair pairs op a b entry) : StatefulPair (pairs ++ extra) op a b entry := by
  cases op <;> simp only [StatefulPair] at pair ⊢ <;> try trivial
  all_goals
    have bound := (List.getElem?_eq_some_iff.mp pair).1
    simpa only [List.getElem?_append, if_pos bound] using pair

theorem StatefulEmission.map_pairs {beforePairs afterPairs C before instruction emitted after}
    (preserve : ∀ (index : Nat) (pair : U32 × U32), beforePairs[index]? = some pair → afterPairs[index]? = some pair)
    (head : StatefulEmission beforePairs C before instruction emitted after) :
    StatefulEmission afterPairs C before instruction emitted after := by
  cases head with
  | instruction stack input output op signature first second a b entry firstSlot secondSlot arguments pair =>
    refine .instruction stack input output op signature first second a b entry firstSlot secondSlot arguments ?_
    cases op <;> simp only [StatefulPair] at pair ⊢ <;> try trivial
    all_goals exact preserve _ _ pair

theorem CumulativeCodeRel.map_pairs {beforePairs afterPairs C returns code labels stack source pc next final}
    (preserve : ∀ (index : Nat) (pair : U32 × U32), beforePairs[index]? = some pair → afterPairs[index]? = some pair)
    (relation : CumulativeCodeRel beforePairs C returns code labels stack source pc next final) :
    CumulativeCodeRel afterPairs C returns code labels stack source pc next final := by
  apply relation.map_emission
  intro before instruction emitted after head
  cases head with
  | left h => exact .left h
  | right h => exact .right (h.map_pairs preserve)
  | indirect h => exact .indirect (h.map_pairs preserve)

end Exec.Code
