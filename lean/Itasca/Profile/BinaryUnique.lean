import Itasca.Profile.CodeEntry
import Itasca.MultiValue.BinaryUnique
import Itasca.Binary.ModuleBinaryUniquePrimitives
import Itasca.Binary.ModuleBinaryUnique

open Aeneas Aeneas.Std

namespace Itasca.Profile

open ModuleBinary

/-- The selected profile's raw body bytes determine one structured tree,
independently of typing and implementation bounds. -/
theorem BodyBytes.unique (profile : ValidationProfile) : Unique (BodyBytes profile) := by
  cases profile with
  | Wasm1 => exact ModuleBinary.BodyEncoding.unique
  | Wasm2 =>
    rintro xs ys bytes ⟨xt, hx, hxs⟩ ⟨yt, hy, hys⟩
    obtain rfl := MultiValue.tokens_unique hx hy
    exact hxs.unique hys

/-- Entry sizes and local declarations retain uniqueness for both grammars. -/
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

/-- A complete module has one decoding under either supported profile. -/
theorem module_unique {profile x y bytes}
    (hx : ModuleBinary.ModuleEncodingWith (CodeEncoding profile) x bytes profile)
    (hy : ModuleBinary.ModuleEncodingWith (CodeEncoding profile) y bytes profile) : x = y :=
  ModuleBinary.ModuleEncodingWith.unique (code_prefix_unique profile) hx hy

end Itasca.Profile
