namespace WebAssembly.Binary.Leb128

/-- The byte projection lets decoder proofs use the same grammar on their byte representation. -/
def payloadWith (byte : α → Nat) : List α → Nat
  | [] => 0
  | b :: bs => byte b % 128 + 128 * payloadWith byte bs

def UnsignedForm (byte : α → Nat) (payload : List α → Nat) (bytes : List α) (value : Nat) : Prop :=
  ∃ before last, bytes = before ++ [last] ∧ before.length ≤ 4 ∧
    (∀ b ∈ before, 128 ≤ byte b) ∧ byte last < 128 ∧
    (before.length = 4 → byte last < 16) ∧ value = payload bytes

abbrev UnsignedWith (byte : α → Nat) := UnsignedForm byte (payloadWith byte)

def signedFinal (acc mult : Int) (last : Nat) : Int :=
  acc + (last : Int) * mult - if 64 ≤ last then 128 * mult else 0

def SignedForm (byte : α → Nat) (payload : List α → Nat) (terminal : Int → Int → α → Int)
    (maxPrefix : Nat) (lower upper : Int)
    (bytes : List α) (value : Int) : Prop :=
  ∃ before last, bytes = before ++ [last] ∧ before.length ≤ maxPrefix ∧
    (∀ b ∈ before, 128 ≤ byte b) ∧ byte last < 128 ∧
    value = terminal (payload before) (128 ^ before.length) last ∧
    lower ≤ value ∧ value ≤ upper

abbrev SignedWith (byte : α → Nat) :=
  SignedForm byte (payloadWith byte) (fun acc mult b => signedFinal acc mult (byte b))

abbrev U32Encoding := UnsignedWith UInt8.toNat
abbrev S32Encoding := SignedWith UInt8.toNat 4 (-2147483648) 2147483647
abbrev S33Encoding := SignedWith UInt8.toNat 4 (-4294967296) 4294967295
abbrev S64Encoding := SignedWith UInt8.toNat 9 (-9223372036854775808) 9223372036854775807

private theorem payload_map (f : α → β) (byte : β → Nat) (xs : List α) :
    payloadWith byte (xs.map f) = payloadWith (byte ∘ f) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [payloadWith, ih]

private theorem map_eq_snoc {xs : List α} {before : List β} {last : β} {f : α → β}
    (h : xs.map f = before ++ [last]) :
    ∃ ys y, xs = ys ++ [y] ∧ ys.map f = before ∧ f y = last := by
  obtain ⟨ys, zs, rfl, rfl, hz⟩ := List.map_eq_append_iff.mp h
  obtain ⟨y, rfl, rfl⟩ := List.map_eq_singleton_iff.mp hz
  exact ⟨_, _, rfl, rfl, rfl⟩

theorem unsigned_map (f : α → β) (byte : β → Nat) (xs : List α) (value : Nat) :
    UnsignedWith byte (xs.map f) value ↔ UnsignedWith (byte ∘ f) xs value := by
  constructor
  · rintro ⟨bs, b, h, rest⟩
    obtain ⟨ys, y, rfl, rfl, rfl⟩ := map_eq_snoc h
    exact ⟨ys, y, rfl, by simpa [-List.map_append, payload_map] using rest⟩
  · rintro ⟨ys, y, rfl, rest⟩
    exact ⟨ys.map f, f y, by simp, by simpa [-List.map_append, payload_map] using rest⟩

theorem signed_map (f : α → β) (byte : β → Nat) (n : Nat) (lo hi : Int)
    (xs : List α) (value : Int) :
    SignedWith byte n lo hi (xs.map f) value ↔ SignedWith (byte ∘ f) n lo hi xs value := by
  constructor
  · rintro ⟨bs, b, h, rest⟩
    obtain ⟨ys, y, rfl, rfl, rfl⟩ := map_eq_snoc h
    exact ⟨ys, y, rfl, by simpa [-List.map_append, payload_map] using rest⟩
  · rintro ⟨ys, y, rfl, rest⟩
    exact ⟨ys.map f, f y, by simp, by simpa [-List.map_append, payload_map] using rest⟩

end WebAssembly.Binary.Leb128
