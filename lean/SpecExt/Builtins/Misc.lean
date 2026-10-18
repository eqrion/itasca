import Wasm2Prefix

/-!
The generated inverse-concat signature omits chunk sizes. The pinned SpecTec
interpreter (`spectec/src/backend-interpreter/numerics.ml`, `inv_concat_helper`)
uses consecutive pairs. This is an auxiliary implementation convention, not a
left inverse for arbitrary lists of lists. The generated specification currently
has no call sites. Odd-length inputs, rejected by the reference helper, are
here totalized with a final singleton; no specification rule relies on that case.
-/

def inv_concat_ (X : Type) : List X → List (List X)
  | [] => []
  | [a] => [[a]]
  | a :: b :: rest => [a, b] :: inv_concat_ X rest

namespace SpecExt.Builtins

/-- Pair chunking preserves the original sequence when flattened. -/
theorem flatten_inv_concat (X : Type) :
    (xs : List X) → (inv_concat_ X xs).flatten = xs
  | [] => rfl
  | [_] => rfl
  | a :: b :: rest => by
      simp [inv_concat_, flatten_inv_concat X rest]

end SpecExt.Builtins
