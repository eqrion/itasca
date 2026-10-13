import Itasca.Module.Env.Slots

/-!
# Ordered section chain

`Chain` restates the independent prefix grammar as the ten ordered optional declaration slots
followed by trailing custom sections, indexed by how many slots have been passed.
`PrefixEncoding.chain` converts a `PrefixEncoding` into a `Chain` for the parser's run order.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleEnv

open ModuleBinary

/-- The ten ordered optional declaration slots, followed by all custom bytes consumed before the
first code or data section. -/
inductive Chain (raw : ModuleBinary.Module) :
    Nat → List U8 → (profile : optParam ValidationProfile .Wasm1) → Prop where
  | done {profile bytes} : CustomsEncoding bytes → Chain raw 10 bytes profile
  | step {profile} {n : Nat} {id : U8} {first rest : List U8} :
      n < 10 → (sectionRank id).val = n + 1 → SlotEncoding raw id first profile → Chain raw (n + 1) rest profile →
      Chain raw n (first ++ rest) profile

/-- A padded section encoding is a slot encoding when the absent value is an empty slot and
every present payload is a valid payload for that section. -/
theorem padded_slot {profile} {α : Type} {R : α → List U8 → Prop} {raw : ModuleBinary.Module}
    {id : U8} {value absent : α} {bytes : List U8}
    (h : PaddedEncoding id R absent value bytes)
    (hzero : value = absent → Empty raw (sectionRank id).val)
    (hpayload : ∀ bs, R value bs → Payload raw (sectionRank id).val () bs profile) : SlotEncoding raw id bytes profile := by
  obtain ⟨customs, body, hc, hs, rfl⟩ := h
  refine ⟨customs, body, hc, ?_, rfl⟩
  cases hs with
  | absent => exact .inl ⟨hzero rfl, rfl⟩
  | present hsection =>
    obtain ⟨size, payload, hsize, hp, rfl⟩ := hsection
    exact .inr ⟨size, payload, hsize, hpayload payload hp, rfl⟩

/-- A `PrefixEncoding` after the module header is a `Chain` starting at slot `0`, keeping all
custom-section bytes and all empty slots. -/
theorem PrefixEncoding.chain {profile} {decls : Declarations} {bytes : List U8}
    (h : PrefixEncoding decls bytes profile) (codes : List ModuleBinary.Code) (datas : List ModuleBinary.Data) :
    ∃ suffix, Chain (decls.module codes datas) 0 suffix profile ∧ bytes = magicVersion ++ suffix := by
  obtain ⟨types, imports, functions, tables, memories, globals, exports, start, elements, dataCount,
    customs, ht, hi, hf, hta, hm, hg, he, hs, hel, hdc, hc, rfl, hallowed⟩ := h
  have ht' := padded_slot (profile := profile) (raw := decls.module codes datas) ht (fun h => h) (fun _ h => h)
  have hi' := padded_slot (profile := profile) (raw := decls.module codes datas) hi (fun h => h) (fun _ h => h)
  have hf' := padded_slot (profile := profile) (raw := decls.module codes datas) hf (fun h => h) (fun _ h => h)
  have hta' := padded_slot (profile := profile) (raw := decls.module codes datas) hta (fun h => h) (fun _ h => h)
  have hm' := padded_slot (profile := profile) (raw := decls.module codes datas) hm (fun h => h) (fun _ h => h)
  have hg' := padded_slot (profile := profile) (raw := decls.module codes datas) hg (fun h => h) (fun _ h => h)
  have he' := padded_slot (profile := profile) (raw := decls.module codes datas) he (fun h => h) (fun _ h => h)
  have hs' := padded_slot (profile := profile) (raw := decls.module codes datas) hs (fun h => h) (fun _ h => h)
  have hel' := padded_slot (profile := profile) (raw := decls.module codes datas) hel (fun h => h) (fun _ h => h)
  have hdc' : SlotEncoding (decls.module codes datas) 12#u8 dataCount profile := by
    cases profile with
    | Wasm1 =>
      obtain ⟨hvalue, rfl⟩ := hdc
      exact ⟨[], [], .nil, .inl ⟨hvalue, rfl⟩, rfl⟩
    | Wasm2 =>
      exact padded_slot hdc (fun h => h) (fun _ h => ⟨rfl, h⟩)
  refine ⟨types ++ imports ++ functions ++ tables ++ memories ++ globals ++ exports ++ start ++ elements ++ dataCount ++ customs,
    ?_, by simp [List.append_assoc]⟩
  simpa only [List.append_assoc] using
    (Chain.step (n := 0) (id := 1#u8) (by decide) rfl ht'
    (Chain.step (n := 1) (id := 2#u8) (by decide) rfl hi'
    (Chain.step (n := 2) (id := 3#u8) (by decide) rfl hf'
    (Chain.step (n := 3) (id := 4#u8) (by decide) rfl hta'
    (Chain.step (n := 4) (id := 5#u8) (by decide) rfl hm'
    (Chain.step (n := 5) (id := 6#u8) (by decide) rfl hg'
    (Chain.step (n := 6) (id := 7#u8) (by decide) rfl he'
    (Chain.step (n := 7) (id := 8#u8) (by decide) rfl hs'
    (Chain.step (n := 8) (id := 9#u8) (by decide) rfl hel'
    (Chain.step (n := 9) (id := 12#u8) (by decide) rfl hdc' (.done hc)))))))))))

end Itasca.ModuleEnv
