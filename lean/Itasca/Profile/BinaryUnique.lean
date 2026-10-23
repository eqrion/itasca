import Itasca.Profile.CodeEntry
import Itasca.Binary.Wasm2.EncodingUnique
import Itasca.Binary.ModuleUniquePrimitives
import Itasca.Binary.ModuleUnique

/-!
# Profile binary uniqueness

Lifts the uniqueness of the binary grammars to both profiles: `BodyBytes.unique` for body bytes
and `code_prefix_unique` for code entries. `Itasca/Results/Unique` gives the complete-module
result.
-/

open Aeneas Aeneas.Std

namespace Itasca.Profile

open ModuleBinary

/-- The profile's body bytes determine one instruction tree, independently of typing and
implementation bounds. -/
theorem BodyBytes.unique (profile : ValidationProfile) : Unique (BodyBytes profile) := by
  cases profile with
  | Wasm1 => exact ModuleBinary.BodyEncoding.unique
  | Wasm2 =>
    rintro xs ys bytes ⟨xt, hx, hxs⟩ ⟨yt, hy, hys⟩
    obtain rfl := Wasm2.tokens_unique hx hy
    exact hxs.unique hys

/-- Code entries, with their size prefix and local declarations, are prefix-unique under either
profile. -/
theorem code_prefix_unique (profile : ValidationProfile) : PrefixUnique (CodeEncoding profile) := by
  intro x y a b rest tail hx hy he
  obtain ⟨xn, xl, xb, hn, hl, hb, rfl⟩ := hx
  obtain ⟨yn, yl, yb, hn', hl', hb', rfl⟩ := hy
  obtain ⟨hlen, rfl, hcontent⟩ := leb_prefix_unique hn hn'
    (by simpa [List.append_assoc] using he)
  obtain ⟨hpayload, rfl⟩ := split_of_length
    (by simpa [List.append_assoc] using hcontent : (xl ++ xb) ++ rest = (yl ++ yb) ++ tail)
    (by simpa using hlen)
  obtain ⟨hlv, rfl, rfl⟩ := local_prefix_unique.vec hl hl' hpayload
  have hbv := BodyBytes.unique profile hb hb'
  have hv : x = y := by cases x; cases y; simp_all
  exact ⟨hv, rfl, rfl⟩

end Itasca.Profile
