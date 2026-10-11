import Itasca.Binary.ModuleBinaryUniquePrimitives
import Itasca.Binary.WasmBinaryPrefix

open Aeneas Aeneas.Std

namespace Itasca.ModuleBinary

theorem code_prefix_unique : PrefixUnique CodeEncoding := by
  intro x y a b rest tail hx hy he
  obtain ⟨xn, xl, xb, hn, hl, hb, rfl⟩ := hx
  obtain ⟨yn, yl, yb, hn', hl', hb', rfl⟩ := hy
  obtain ⟨hlen, rfl, hcontent⟩ := leb_prefix_unique hn hn'
    (by simpa [List.append_assoc] using he)
  obtain ⟨hpayload, rfl⟩ := split_of_length
    (by simpa [List.append_assoc] using hcontent : (xl ++ xb) ++ rest = (yl ++ yb) ++ tail)
    (by simpa using hlen)
  obtain ⟨hlv, rfl, rfl⟩ := local_prefix_unique.vec hl hl' hpayload
  have hbv := BodyEncoding.unique hb hb'
  have hv : x = y := by cases x; cases y; simp_all
  exact ⟨hv, rfl, rfl⟩

namespace SectionDecode

/-- Exact raw section framing, without interpreting its payload. -/
def Encoding (frame : U8 × List U8) (bytes : List U8) : Prop :=
  ∃ size, Leb128.Encoding size frame.2.length ∧ bytes = frame.1 :: (size ++ frame.2)

theorem prefix_unique : PrefixUnique Encoding := by
  rintro ⟨xt, xp⟩ ⟨yt, yp⟩ a b rest tail ⟨xn, hx, rfl⟩ ⟨yn, hy, rfl⟩ he
  obtain ⟨rfl, hbody⟩ := List.cons.inj he
  obtain ⟨hlen, rfl, hpayload⟩ := leb_prefix_unique hx hy
    (by simpa [List.append_assoc] using hbody)
  obtain ⟨rfl, rfl⟩ := split_of_length hpayload hlen
  exact ⟨rfl, rfl, rfl⟩

theorem unique : Unique (Rep Encoding) :=
  prefix_unique.rep_unique (by rintro _ _ ⟨n, hn, rfl⟩; simp)

def payloads (id : U8) : List (U8 × List U8) → List (List U8)
  | [] => []
  | (tag, bytes) :: sections =>
      if id = tag then bytes :: payloads id sections else payloads id sections

theorem payloads_append (id : U8) (xs ys : List (U8 × List U8)) :
    payloads id (xs ++ ys) = payloads id xs ++ payloads id ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x; simp only [List.cons_append, payloads]; split <;> simp_all

/-- Each standard field is either omitted or represented by exactly one payload. -/
inductive Field {α : Type} (R : α → List U8 → Prop) (absent : α) : α → List (List U8) → Prop where
  | absent : Field R absent absent []
  | present {value bytes} : R value bytes → Field R absent value [bytes]

theorem Field.unique {α : Type} {R : α → List U8 → Prop} {absent x y payloads}
    (hu : Unique R) (hx : Field R absent x payloads) (hy : Field R absent y payloads) : x = y := by
  cases hx <;> cases hy
  · rfl
  · apply hu <;> assumption

end SectionDecode

theorem SectionEncoding.frame {α : Type} {R : α → List U8 → Prop} {id value bytes}
    (h : SectionEncoding id R value bytes) :
    ∃ payload, R value payload ∧ SectionDecode.Encoding (id, payload) bytes := by
  obtain ⟨size, payload, hn, hp, rfl⟩ := h
  exact ⟨payload, hp, size, hn, rfl⟩

theorem CustomsEncoding.frames {bytes} (h : CustomsEncoding bytes) :
    ∃ sections, Rep SectionDecode.Encoding sections bytes ∧
      ∀ id, id ≠ 0#u8 → SectionDecode.payloads id sections = [] := by
  induction h with
  | nil => exact ⟨[], .nil, by intros; rfl⟩
  | cons hc _ ih =>
    obtain ⟨nm, content, nameBytes, hn, hs⟩ := hc
    obtain ⟨payload, _, hf⟩ := hs.frame
    obtain ⟨sections, hp, hids⟩ := ih
    refine ⟨(0#u8, payload) :: sections, .cons hf hp, ?_⟩
    intro id hid
    simp [SectionDecode.payloads, hid, hids id hid]

theorem PaddedEncoding.frames {α : Type} {R : α → List U8 → Prop} {id absent value bytes}
    (h : PaddedEncoding id R absent value bytes) :
    ∃ sections payloads, Rep SectionDecode.Encoding sections bytes ∧
      SectionDecode.Field R absent value payloads ∧
      ∀ wanted, wanted ≠ 0#u8 → SectionDecode.payloads wanted sections =
        if wanted = id then payloads else [] := by
  obtain ⟨customs, sec, hc, hs, rfl⟩ := h
  obtain ⟨before, hp, hids⟩ := hc.frames
  cases hs with
  | absent => exact ⟨before, [], by simpa using hp, .absent, by intros; simp [*]⟩
  | present hs =>
    obtain ⟨payload, hv, hf⟩ := hs.frame
    refine ⟨before ++ [(id, payload)], [payload], hp.snoc hf, .present hv, ?_⟩
    intro wanted hw
    simp [SectionDecode.payloads_append, hids wanted hw, SectionDecode.payloads]

end Itasca.ModuleBinary
