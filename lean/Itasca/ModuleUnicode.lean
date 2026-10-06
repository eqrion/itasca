import Itasca.ModuleNames

open Aeneas Aeneas.Std

namespace Itasca.ModuleBinary

def specByte (b : U8) : byte := .mk_byte b.val

theorem specByte_wf (b : U8) : wf_byte (specByte b) := by
  apply wf_byte.byte_case_0
  scalar_tac

/-- Deterministic Unicode decoding; malformed branches are irrelevant to the
proved interface, which starts from the independent strict UTF-8 grammar. -/
def decodeChars : List U8 → List char
  | [] => []
  | a :: rest =>
      if a.val < 128 then .mk_char a.val :: decodeChars rest
      else match rest with
        | [] => []
        | b :: rest =>
            if a.val < 224 then .mk_char (64 * (a.val - 192) + (b.val - 128)) :: decodeChars rest
            else match rest with
              | [] => []
              | c :: rest =>
                  if a.val < 240 then
                    .mk_char (4096 * (a.val - 224) + 64 * (b.val - 128) + (c.val - 128)) :: decodeChars rest
                  else match rest with
                    | [] => []
                    | d :: rest =>
                        .mk_char (262144 * (a.val - 240) + 4096 * (b.val - 128) +
                          64 * (c.val - 128) + (d.val - 128)) :: decodeChars rest

def nameOfBytes (bytes : List U8) : «name» := .mk_name (decodeChars bytes)

/-- Each canonical byte sequence has its actual scalar value in the generated
UTF-8 relation. This constructs Unicode scalars, rather than treating bytes as characters. -/
theorem Utf8Char.semantic {bytes : List U8} (h : Utf8Char bytes) (rest : List U8) :
    ∃ ch, decodeChars (bytes ++ rest) = ch :: decodeChars rest ∧
      fun_utf8 [ch] (bytes.map specByte) ∧ wf_char ch := by
  cases h with
  | one a ha =>
      refine ⟨.mk_char a.val, ?_, ?_, ?_⟩
      · rcases rest with _ | ⟨x, (_ | ⟨y, (_ | ⟨z, tail⟩)⟩)⟩ <;>
          simp [decodeChars, show a.val < 128 by omega]
      · exact .fun_utf8_case_0 _ _ ⟨ha.trans_lt (by decide), rfl⟩ (specByte_wf a) (specByte_wf a)
      · apply wf_char.char_case_0; omega
  | two a b ha ha' hb hb' =>
      refine ⟨.mk_char (64 * (a.val - 192) + (b.val - 128)), ?_, ?_, ?_⟩
      · rcases rest with _ | ⟨x, (_ | ⟨y, tail⟩)⟩ <;>
          simp [decodeChars, show ¬a.val < 128 by omega, show a.val < 224 by omega]
      · apply fun_utf8.fun_utf8_case_1 _ _ _ ?_ (specByte_wf a) (specByte_wf b)
        simp only [proj_char_0, specByte, proj_byte_0]
        omega
      · apply wf_char.char_case_0; omega
  | three a b c ha hc hc' =>
      refine ⟨.mk_char (4096 * (a.val - 224) + 64 * (b.val - 128) + (c.val - 128)), ?_, ?_, ?_⟩
      · rcases rest with _ | ⟨x, tail⟩ <;>
          simp [decodeChars, show ¬a.val < 128 by omega, show ¬a.val < 224 by omega,
            show a.val < 240 by omega]
      · apply fun_utf8.fun_utf8_case_2 _ _ _ _ ?_ (specByte_wf a) (specByte_wf b) (specByte_wf c)
        simp only [proj_char_0, specByte, proj_byte_0]
        omega
      · apply wf_char.char_case_0; omega
  | four a b c d ha hc hc' hd hd' =>
      refine ⟨.mk_char (262144 * (a.val - 240) + 4096 * (b.val - 128) +
        64 * (c.val - 128) + (d.val - 128)), ?_, ?_, ?_⟩
      · simp [decodeChars, show ¬a.val < 128 by omega, show ¬a.val < 224 by omega,
          show ¬a.val < 240 by omega]
      · apply fun_utf8.fun_utf8_case_3 _ _ _ _ _ ?_ (specByte_wf a) (specByte_wf b)
          (specByte_wf c) (specByte_wf d)
        simp only [proj_char_0, specByte, proj_byte_0]
        omega
      · apply wf_char.char_case_0; omega

private theorem Utf8.chunks {bytes : List U8} (h : Utf8 bytes) :
    ∃ chunks, chunks.length = (decodeChars bytes).length ∧
      Forall₂ (fun bs ch => fun_utf8 [ch] bs) chunks (decodeChars bytes) ∧
      concat_ byte chunks = bytes.map specByte ∧ Forall wf_char (decodeChars bytes) := by
  induction h with
  | nil => exact ⟨[], rfl, by simp [Forall₂, decodeChars], rfl, by simp [Forall, decodeChars]⟩
  | @cons first rest hc hr ih =>
      obtain ⟨ch, hd, he, hw⟩ := hc.semantic rest
      obtain ⟨chunks, hl, hh, hb, hw'⟩ := ih
      refine ⟨first.map specByte :: chunks, ?_, ?_, ?_, ?_⟩
      · simp [hd, hl]
      · simp only [hd, Forall₂, List.zip_cons_cons, List.mem_cons]
        intro pair hm
        rcases hm with rfl | hm
        · exact he
        · exact hh pair hm
      · simp [concat_, hb, List.map_append]
      · simp only [hd, Forall, List.mem_cons]
        intro c hm
        rcases hm with rfl | hm
        · exact hw
        · exact hw' c hm

private theorem concat_flatten (chunks : List (List byte)) : concat_ byte chunks = chunks.flatten := by
  induction chunks with
  | nil => rfl
  | cons head tail ih => simp [concat_, ih]

/-- Accepted UTF-8 bytes denote exactly the deterministically decoded Unicode
string in the generated relation, and each resulting scalar is well formed. -/
theorem Utf8.semantic {bytes : List U8} (h : Utf8 bytes) :
    fun_utf8 (decodeChars bytes) (bytes.map specByte) ∧ Forall wf_char (decodeChars bytes) := by
  obtain ⟨chunks, hl, hh, hb, hw⟩ := h.chunks
  have hbytes : Forall wf_byte (concat_ byte chunks) := by
    rw [hb]
    intro b hm
    obtain ⟨source, _, rfl⟩ := List.mem_map.mp hm
    exact specByte_wf source
  have hnested : Forall (fun bs => Forall wf_byte bs) chunks := by
    intro bs hbs b hmem
    apply hbytes b
    rw [concat_flatten]
    exact List.mem_flatten.mpr ⟨bs, hbs, hmem⟩
  refine ⟨?_, hw⟩
  rw [← hb]
  exact fun_utf8.fun_utf8_case_4 _ chunks chunks chunks hl hh hl hh hl hh hbytes hnested

/-- A binary name has the actual Unicode name required by generated module
syntax, including its UTF-8 byte-size bound. -/
theorem NameEncoding.wellFormed {nm bytes} (h : NameEncoding nm bytes) :
    wf_name (nameOfBytes nm) := by
  obtain ⟨count, hcount, _⟩ := ByteVecEncoding.iff.mp h.1
  obtain ⟨hutf, hw⟩ := h.2.semantic
  apply wf_name.name_case_0 _ (nm.map specByte) hutf hw
  simpa using Leb128.Encoding.value_lt hcount

end Itasca.ModuleBinary
