import WebAssembly.Binary.InstructionUnique
import WebAssembly.Binary.SyntaxUnique

namespace WebAssembly.Binary

/-- The body bytes determine one instruction tree, independently of typing and
implementation bounds. -/
theorem BodyBytes.unique : EncodingUnique BodyBytes := by
  rintro xs ys bytes ⟨xt, hx, hxs⟩ ⟨yt, hy, hys⟩
  obtain rfl := tokens_unique hx hy
  exact BodyTokens.unique hxs hys

/-- Code entries, with their size prefix and local declarations, are prefix-unique under Wasm 2.0. -/
theorem CodeEncoding.prefix_unique : PrefixUnique CodeEncoding := by
  intro x y a b rest tail hx hy he
  obtain ⟨xn, xl, xb, hn, hl, hb, rfl⟩ := hx
  obtain ⟨yn, yl, yb, hn', hl', hb', rfl⟩ := hy
  obtain ⟨hlen, rfl, hcontent⟩ := IndexEncoding.prefix_unique hn hn'
    (by simpa [List.append_assoc] using he)
  obtain ⟨hpayload, rfl⟩ := split_of_length
    (by simpa [List.append_assoc] using hcontent : (xl ++ xb) ++ rest = (yl ++ yb) ++ tail)
    (by simpa using hlen)
  obtain ⟨hlv, rfl, rfl⟩ := LocalEncoding.prefix_unique.vec hl hl' hpayload
  have hbv := BodyBytes.unique hb hb'
  have hv : x = y := by cases x; cases y; simp_all
  exact ⟨hv, rfl, rfl⟩

/-- Exact bytes determine the WebAssembly raw module, including its grouped locals. -/
theorem ModuleEncoding.unique {x y : Module} {bs : List UInt8}
    (hx : ModuleEncoding x bs) (hy : ModuleEncoding y bs) : x = y :=
  ModuleEncodingWith.unique CodeEncoding.prefix_unique hx hy

end WebAssembly.Binary
