import «wasm2.0»

namespace SpecExt.Builtins

/-- Pair chunking preserves the original sequence when flattened. -/
theorem flatten_inv_concat (X : Type) :
    (xs : List X) → (inv_concat_ X xs).flatten = xs
  | [] => rfl
  | [_] => rfl
  | a :: b :: rest => by
      simp [inv_concat_, flatten_inv_concat X rest]

end SpecExt.Builtins
