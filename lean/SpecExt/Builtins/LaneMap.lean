import SpecExt.Builtins.LaneLaws
namespace SpecExt.Builtins

theorem unpackLanes_eq_map (ty : lanetype) (count bits : Nat) (values : Nat → Nat)
    (lanes : ∀ j, j < count → bits/2^(lsize ty*j)%2^lsize ty = values j) :
    unpackLanes ty count bits = (List.range count).map (fun j => laneOfBits ty (values j)) := by
  apply List.ext_getElem?
  intro j
  rw [unpackLanes_getElem?]
  by_cases valid : j < count
  · simp [List.getElem?_map,List.getElem?_range,valid,lanes j valid]
  · simp [List.getElem?_map,List.getElem?_range,valid]

theorem pack_map_of_lanes (ty : lanetype) (count bits : Nat) (values : Nat → Nat)
    (lanes : ∀ j, j < count → bits/2^(lsize ty*j)%2^lsize ty = values j) :
    packLanes ty ((List.range count).map (fun j => laneOfBits ty (values j))) = bits%2^(lsize ty*count) := by
  rw [←unpackLanes_eq_map ty count bits values lanes,pack_unpackLanes]

end SpecExt.Builtins
