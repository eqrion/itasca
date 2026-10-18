import SpecExt.Builtins.LaneLaws
namespace SpecExt.Builtins

theorem unpackLanes_eq_replicate (ty : lanetype) (count bits value : Nat)
    (lanes : ∀ j, j < count → bits / 2^(lsize ty*j) % 2^lsize ty = value) :
    unpackLanes ty count bits = List.replicate count (laneOfBits ty value) := by
  apply List.ext_getElem?
  intro j
  rw [unpackLanes_getElem?]
  by_cases valid : j < count
  · simp [valid, lanes j valid]
  · simp [valid]

theorem pack_replicate_of_lanes (ty : lanetype) (count bits value : Nat)
    (lanes : ∀ j, j < count → bits / 2^(lsize ty*j) % 2^lsize ty = value) :
    packLanes ty (List.replicate count (laneOfBits ty value)) = bits % 2^(lsize ty*count) := by
  rw [←unpackLanes_eq_replicate ty count bits value lanes, pack_unpackLanes]

end SpecExt.Builtins
