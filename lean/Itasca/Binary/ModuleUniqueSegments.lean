import Itasca.Binary.ModuleUniquePrimitives

/-!
# Prefix uniqueness of segments

Proves `PrefixUnique` for the Wasm 2.0 element and data segment encodings by splitting off the
flag and treating each flag's payload grammar separately. `elementFor_prefix_unique` and
`dataFor_prefix_unique` cover both profiles.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleBinary

/-- The grammar of an element segment payload after its flag. -/
private inductive ElementPayload : Nat → Element → List U8 → Prop where
  | activeIndices {offset initializers encodedOffset entries} :
      ConstEncoding offset encodedOffset → VecEncoding IndexEncoding initializers entries →
      ElementPayload 0 ⟨.FuncRef, .Active 0#u32 offset, initializers.map wasm_types.ConstExpr.RefFunc⟩
        (encodedOffset ++ entries)
  | passiveIndices {initializers entries} : VecEncoding IndexEncoding initializers entries →
      ElementPayload 1 ⟨.FuncRef, .Passive, initializers.map wasm_types.ConstExpr.RefFunc⟩ (0#u8 :: entries)
  | explicitIndices {tableIndex offset initializers table encodedOffset entries} :
      IndexEncoding tableIndex table → ConstEncoding offset encodedOffset →
      VecEncoding IndexEncoding initializers entries →
      ElementPayload 2 ⟨.FuncRef, .Active tableIndex offset, initializers.map wasm_types.ConstExpr.RefFunc⟩
        (table ++ encodedOffset ++ (0#u8 :: entries))
  | declarativeIndices {initializers entries} : VecEncoding IndexEncoding initializers entries →
      ElementPayload 3 ⟨.FuncRef, .Declarative, initializers.map wasm_types.ConstExpr.RefFunc⟩ (0#u8 :: entries)
  | activeExpressions {offset initializers encodedOffset entries} :
      ConstEncoding offset encodedOffset → VecEncoding ConstEncoding initializers entries →
      ElementPayload 4 ⟨.FuncRef, .Active 0#u32 offset, initializers⟩ (encodedOffset ++ entries)
  | passiveExpressions {elem initializers entries} : VecEncoding ConstEncoding initializers entries →
      ElementPayload 5 ⟨elem, .Passive, initializers⟩ (elemByte elem :: entries)
  | explicitExpressions {elem tableIndex offset initializers table encodedOffset entries} :
      IndexEncoding tableIndex table → ConstEncoding offset encodedOffset →
      VecEncoding ConstEncoding initializers entries →
      ElementPayload 6 ⟨elem, .Active tableIndex offset, initializers⟩
        (table ++ encodedOffset ++ (elemByte elem :: entries))
  | declarativeExpressions {elem initializers entries} : VecEncoding ConstEncoding initializers entries →
      ElementPayload 7 ⟨elem, .Declarative, initializers⟩ (elemByte elem :: entries)

private theorem element_parts {entry bytes} (h : Wasm2ElementEncoding entry bytes) :
    ∃ flag flags payload, IndexEncoding flag flags ∧ ElementPayload flag.val entry payload ∧
      bytes = flags ++ payload := by
  cases h with
  | activeIndices hf ho hi => exact ⟨0#u32, _, _, hf, .activeIndices ho hi, by simp [List.append_assoc]⟩
  | passiveIndices hf hi => exact ⟨1#u32, _, _, hf, .passiveIndices hi, by simp [List.append_assoc]⟩
  | explicitIndices hf ht ho hi => exact ⟨2#u32, _, _, hf, .explicitIndices ht ho hi, by simp [List.append_assoc]⟩
  | declarativeIndices hf hi => exact ⟨3#u32, _, _, hf, .declarativeIndices hi, by simp [List.append_assoc]⟩
  | activeExpressions hf ho hi => exact ⟨4#u32, _, _, hf, .activeExpressions ho hi, by simp [List.append_assoc]⟩
  | passiveExpressions hf hi => exact ⟨5#u32, _, _, hf, .passiveExpressions hi, by simp [List.append_assoc]⟩
  | explicitExpressions hf ht ho hi => exact ⟨6#u32, _, _, hf, .explicitExpressions ht ho hi, by simp [List.append_assoc]⟩
  | declarativeExpressions hf hi => exact ⟨7#u32, _, _, hf, .declarativeExpressions hi, by simp [List.append_assoc]⟩

private theorem elementPayload_prefix_unique (flag : Nat) : PrefixUnique (ElementPayload flag) := by
  intro x y a b rest tail hx hy he
  cases hx <;> cases hy
  case activeIndices.activeIndices offset initializers encodedOffset entries ho hi offset' initializers' encodedOffset' entries' ho' hi' =>
    obtain ⟨rfl, rfl, hs⟩ := const_prefix_unique ho ho' (by simpa [List.append_assoc] using he)
    obtain ⟨rfl, rfl, rfl⟩ := index_prefix_unique.vec hi hi' hs
    exact ⟨rfl, rfl, rfl⟩
  case passiveIndices.passiveIndices initializers entries hi initializers' entries' hi' =>
    obtain ⟨rfl, rfl, rfl⟩ := index_prefix_unique.vec hi hi' (List.cons.inj he).2
    exact ⟨rfl, rfl, rfl⟩
  case explicitIndices.explicitIndices table offset initializers tb ob ib ht ho hi table' offset' initializers' tb' ob' ib' ht' ho' hi' =>
    obtain ⟨rfl, rfl, hs⟩ := index_prefix_unique ht ht' (by simpa [List.append_assoc] using he)
    obtain ⟨rfl, rfl, hs'⟩ := const_prefix_unique ho ho' (by simpa [List.append_assoc] using hs)
    obtain ⟨rfl, rfl, rfl⟩ := index_prefix_unique.vec hi hi' (List.cons.inj hs').2
    exact ⟨rfl, rfl, rfl⟩
  case declarativeIndices.declarativeIndices initializers entries hi initializers' entries' hi' =>
    obtain ⟨rfl, rfl, rfl⟩ := index_prefix_unique.vec hi hi' (List.cons.inj he).2
    exact ⟨rfl, rfl, rfl⟩
  case activeExpressions.activeExpressions offset initializers encodedOffset entries ho hi offset' initializers' encodedOffset' entries' ho' hi' =>
    obtain ⟨rfl, rfl, hs⟩ := const_prefix_unique ho ho' (by simpa [List.append_assoc] using he)
    obtain ⟨rfl, rfl, rfl⟩ := const_prefix_unique.vec hi hi' hs
    exact ⟨rfl, rfl, rfl⟩
  case passiveExpressions.passiveExpressions elem initializers entries hi elem' initializers' entries' hi' =>
    obtain ⟨ht, hs⟩ := List.cons.inj he
    obtain rfl := elemByte_injective ht
    obtain ⟨rfl, rfl, rfl⟩ := const_prefix_unique.vec hi hi' hs
    exact ⟨rfl, rfl, rfl⟩
  case explicitExpressions.explicitExpressions elem table offset initializers tb ob ib ht ho hi elem' table' offset' initializers' tb' ob' ib' ht' ho' hi' =>
    obtain ⟨rfl, rfl, hs⟩ := index_prefix_unique ht ht' (by simpa [List.append_assoc] using he)
    obtain ⟨rfl, rfl, hs'⟩ := const_prefix_unique ho ho' (by simpa [List.append_assoc] using hs)
    obtain ⟨hty, hs''⟩ := List.cons.inj hs'
    obtain rfl := elemByte_injective hty
    obtain ⟨rfl, rfl, rfl⟩ := const_prefix_unique.vec hi hi' hs''
    exact ⟨rfl, rfl, rfl⟩
  case declarativeExpressions.declarativeExpressions elem initializers entries hi elem' initializers' entries' hi' =>
    obtain ⟨ht, hs⟩ := List.cons.inj he
    obtain rfl := elemByte_injective ht
    obtain ⟨rfl, rfl, rfl⟩ := const_prefix_unique.vec hi hi' hs
    exact ⟨rfl, rfl, rfl⟩

/-- Wasm 2.0 element segment encodings are prefix-unique. -/
theorem wasm2Element_prefix_unique : PrefixUnique Wasm2ElementEncoding := by
  intro x y a b rest tail hx hy he
  obtain ⟨xf, xb, xp, hxf, hxp, rfl⟩ := element_parts hx
  obtain ⟨yf, yb, yp, hyf, hyp, rfl⟩ := element_parts hy
  obtain ⟨rfl, rfl, hs⟩ := index_prefix_unique hxf hyf (by simpa [List.append_assoc] using he)
  obtain ⟨rfl, rfl, rfl⟩ := elementPayload_prefix_unique _ hxp hyp hs
  exact ⟨rfl, rfl, rfl⟩

/-- The grammar of a data segment payload after its flag. -/
private inductive DataPayload : Nat → Data → List U8 → Prop where
  | implicit {offset init encodedOffset entries} :
      ConstEncoding offset encodedOffset → ByteVecEncoding init entries →
      DataPayload 0 ⟨.Active 0#u32 offset, init⟩ (encodedOffset ++ entries)
  | passive {init entries} : ByteVecEncoding init entries →
      DataPayload 1 ⟨.Passive, init⟩ entries
  | explicit {index offset init indexBytes encodedOffset entries} :
      IndexEncoding index indexBytes → ConstEncoding offset encodedOffset → ByteVecEncoding init entries →
      DataPayload 2 ⟨.Active index offset, init⟩ (indexBytes ++ encodedOffset ++ entries)

private theorem data_parts {entry bytes} (h : Wasm2DataEncoding entry bytes) :
    ∃ flag flags payload, IndexEncoding flag flags ∧ DataPayload flag.val entry payload ∧
      bytes = flags ++ payload := by
  cases h with
  | active hi ho hb =>
    cases hi with
    | implicit hf => exact ⟨0#u32, _, _, hf, .implicit ho hb, by simp [List.append_assoc]⟩
    | explicit hf hi => exact ⟨2#u32, _, _, hf, .explicit hi ho hb, by simp [List.append_assoc]⟩
  | passive hf hb => exact ⟨1#u32, _, _, hf, .passive hb, rfl⟩

private theorem dataPayload_prefix_unique (flag : Nat) : PrefixUnique (DataPayload flag) := by
  intro x y a b rest tail hx hy he
  cases hx <;> cases hy
  case implicit.implicit offset init encodedOffset entries ho hi offset' init' encodedOffset' entries' ho' hi' =>
    obtain ⟨rfl, rfl, hs⟩ := const_prefix_unique ho ho' (by simpa [List.append_assoc] using he)
    obtain ⟨rfl, rfl, rfl⟩ := byte_prefix_unique.vec hi hi' hs
    exact ⟨rfl, rfl, rfl⟩
  case passive.passive init hi init' hi' =>
    obtain ⟨rfl, rfl, rfl⟩ := byte_prefix_unique.vec hi hi' he
    exact ⟨rfl, rfl, rfl⟩
  case explicit.explicit index offset init indexBytes encodedOffset entries ht ho hi index' offset' init' indexBytes' encodedOffset' entries' ht' ho' hi' =>
    obtain ⟨rfl, rfl, hs⟩ := index_prefix_unique ht ht' (by simpa [List.append_assoc] using he)
    obtain ⟨rfl, rfl, hs'⟩ := const_prefix_unique ho ho' (by simpa [List.append_assoc] using hs)
    obtain ⟨rfl, rfl, rfl⟩ := byte_prefix_unique.vec hi hi' hs'
    exact ⟨rfl, rfl, rfl⟩

/-- Wasm 2.0 data segment encodings are prefix-unique. -/
theorem wasm2Data_prefix_unique : PrefixUnique Wasm2DataEncoding := by
  intro x y a b rest tail hx hy he
  obtain ⟨xf, xb, xp, hxf, hxp, rfl⟩ := data_parts hx
  obtain ⟨yf, yb, yp, hyf, hyp, rfl⟩ := data_parts hy
  obtain ⟨rfl, rfl, hs⟩ := index_prefix_unique hxf hyf (by simpa [List.append_assoc] using he)
  obtain ⟨rfl, rfl, rfl⟩ := dataPayload_prefix_unique _ hxp hyp hs
  exact ⟨rfl, rfl, rfl⟩

/-- Element segment encodings of either profile are prefix-unique. -/
theorem elementFor_prefix_unique (profile : ValidationProfile) : PrefixUnique (ElementEncodingFor profile) := by
  cases profile with
  | Wasm1 => exact element_prefix_unique
  | Wasm2 => exact wasm2Element_prefix_unique

/-- Data segment encodings of either profile are prefix-unique. -/
theorem dataFor_prefix_unique (profile : ValidationProfile) : PrefixUnique (DataEncodingFor profile) := by
  cases profile with
  | Wasm1 => exact data_prefix_unique
  | Wasm2 => exact wasm2Data_prefix_unique

end Itasca.ModuleBinary
