import WebAssembly.Binary.Module

namespace WebAssembly.Binary

theorem Utf8CharWith.map {byte : β → Nat} (f : α → β) {bs}
    (h : Utf8CharWith (byte ∘ f) bs) : Utf8CharWith byte (bs.map f) := by
  cases h with
  | one a h => exact .one (f a) h
  | two a b h₁ h₂ h₃ h₄ => exact .two (f a) (f b) h₁ h₂ h₃ h₄
  | three a b c h₁ h₂ h₃ => exact .three (f a) (f b) (f c) h₁ h₂ h₃
  | four a b c d h₁ h₂ h₃ h₄ h₅ => exact .four (f a) (f b) (f c) (f d) h₁ h₂ h₃ h₄ h₅

theorem Utf8With.map {byte : β → Nat} (f : α → β) {bs}
    (h : Utf8With (byte ∘ f) bs) : Utf8With byte (bs.map f) := by
  induction h with
  | nil => exact .nil
  | cons hc _ ih => simpa only [List.map_append] using Utf8With.cons (hc.map f) ih

theorem Rep.map {R : α → List β → Prop} {S : γ → List δ → Prop} (f : α → γ) (g : β → δ)
    (step : ∀ {x bs}, R x bs → S (f x) (bs.map g)) {xs bs} (h : Rep R xs bs) :
    Rep S (xs.map f) (bs.map g) := by
  induction h with
  | nil => exact .nil
  | cons hx _ ih => simpa only [List.map_cons, List.map_append] using Rep.cons (step hx) ih

theorem VecEncodingWith.map {R : α → List β → Prop} {S : γ → List δ → Prop}
    {C : List β → Nat → Prop} {D : List δ → Nat → Prop} (f : α → γ) (g : β → δ)
    (count : ∀ {bs n}, C bs n → D (bs.map g) n)
    (step : ∀ {x bs}, R x bs → S (f x) (bs.map g)) {xs bs} (h : VecEncodingWith C R xs bs) :
    VecEncodingWith D S (xs.map f) (bs.map g) := by
  obtain ⟨cs, es, hc, he, rfl⟩ := h
  exact ⟨_, _, by simpa only [List.length_map] using count hc, he.map f g @step, List.map_append⟩

theorem NameEncodingWith.map {C : List α → Nat → Prop} {D : List β → Nat → Prop}
    {byte : β → Nat} (g : α → β) (count : ∀ {bs n}, C bs n → D (bs.map g) n)
    {nm bs} (h : NameEncodingWith (byte ∘ g) C nm bs) :
    NameEncodingWith byte D (nm.map g) (bs.map g) :=
  ⟨VecEncodingWith.map g g @count (fun eq => congrArg (List.map g) eq) h.1, h.2.map g⟩

theorem Rep.unmapValues {R : α → List β → Prop} {S : γ → List δ → Prop}
    (f : α → γ) (g : δ → β)
    (step : ∀ {x bs}, S (f x) bs → R x (bs.map g))
    {xs bs} (h : Rep S (xs.map f) bs) : Rep R xs (bs.map g) := by
  induction xs generalizing bs with
  | nil => cases h; exact .nil
  | cons x xs ih =>
    cases h with
    | cons hx hs => simpa only [List.map_append] using Rep.cons (step hx) (ih hs)

theorem VecEncodingWith.unmapValues {R : α → List β → Prop} {S : γ → List δ → Prop}
    {C : List β → Nat → Prop} {D : List δ → Nat → Prop} (f : α → γ) (g : δ → β)
    (count : ∀ {bs n}, D bs n → C (bs.map g) n)
    (step : ∀ {x bs}, S (f x) bs → R x (bs.map g))
    {xs bs} (h : VecEncodingWith D S (xs.map f) bs) : VecEncodingWith C R xs (bs.map g) := by
  obtain ⟨cs, es, hc, he, rfl⟩ := h
  exact ⟨_, _, by simpa only [List.length_map] using count hc, he.unmapValues f g @step, List.map_append⟩

end WebAssembly.Binary
