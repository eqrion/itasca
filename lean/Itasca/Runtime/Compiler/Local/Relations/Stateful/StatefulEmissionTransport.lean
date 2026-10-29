import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulEmission

/-!
Transport of stateful emission across compiler index-pair tables.

Main declarations: `StatefulEmission.map_pairs`. A direct consumer is `Compiler.Body.Control.Control.CumulativePointControl`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas.Std

theorem StatefulEmission.map_pairs {beforePairs afterPairs C before instruction emitted after}
    (preserve : ∀ (index : Nat) (pair : U32 × U32), beforePairs[index]? = some pair → afterPairs[index]? = some pair)
    (head : StatefulEmission beforePairs C before instruction emitted after) :
    StatefulEmission afterPairs C before instruction emitted after := by
  cases head with
  | instruction stack input output op signature first second a b entry firstSlot secondSlot arguments pair =>
    refine .instruction stack input output op signature first second a b entry firstSlot secondSlot arguments ?_
    cases op <;> simp only [StatefulPair] at pair ⊢ <;> try trivial
    all_goals exact preserve _ _ pair

end Itasca.Runtime.Compiler
