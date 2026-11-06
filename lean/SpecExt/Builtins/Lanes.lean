import «wasm2.0»

namespace SpecExt.Builtins

theorem unpackLanes_length (ty : lanetype) (count bits : Nat) :
    (unpackLanes ty count bits).length = count := by
  induction count generalizing bits with
  | zero => rfl
  | succ count ih => simp only [unpackLanes, List.length_cons, ih]

end SpecExt.Builtins
