import Itasca.Binary.Definitions
import Itasca.Results.Definitions.Binary
import Itasca.Binary.Scalar.Encoding

/-!
Proofs for Binary.

This module collects ModuleGrammar, ModuleUnique.
Each section documents its contracts and consumers.
-/

/-! ## ModuleGrammar -/

section

/-! ## Module -/

section

/-!
# Module binary grammar

Proves properties of the independent raw-module format in
`Results/Definitions/Binary/ModuleGrammar`: vectors, names, types, initializers,
imports/exports, segments, entries and sections. `ModuleEncodingWith` assembles a
module using its chosen code-entry encoding. The grammar states syntax only;
typing and implementation limits remain separate premises.
-/

open Aeneas Aeneas.Std

namespace Itasca.Binary

/-- An element type as its type byte. -/
def ElemTypeEncoding (ty : wasm_types.ElemType) (bytes : List U8) : Prop := bytes = [elemByte ty]

/-- The optional explicit table or memory index of an active segment, as selected by the flag. -/
def SegmentIndexEncoding (flags index : U32)
    (explicit : Bool) (bytes : List U8) : Prop :=
  (flags = 0#u32 ∧ index = 0#u32 ∧ explicit = false ∧ bytes = []) ∨
  (flags = 2#u32 ∧ explicit = true ∧ IndexEncoding index bytes)

/-- A Wasm 2.0 segment index with its flag is an `ActiveIndexEncoding`. -/
theorem SegmentIndexEncoding.active {flags index explicit bytes headBytes}
    (h : SegmentIndexEncoding flags index explicit bytes)
    (hf : IndexEncoding flags headBytes) : ActiveIndexEncoding index explicit (headBytes ++ bytes) := by
  rcases h with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, hi⟩
  · simpa using ActiveIndexEncoding.implicit hf
  · exact .explicit hf hi

/-- An `ActiveIndexEncoding` splits into a flag and a Wasm 2.0 `SegmentIndexEncoding`. -/
theorem ActiveIndexEncoding.parts {index explicit bytes}
    (h : ActiveIndexEncoding index explicit bytes) :
    ∃ flags headBytes suffix, IndexEncoding flags headBytes ∧
      SegmentIndexEncoding flags index explicit suffix ∧ bytes = headBytes ++ suffix := by
  cases h with
  | implicit hf => exact ⟨0#u32, _, [], hf, Or.inl ⟨rfl, rfl, rfl, rfl⟩, by simp⟩
  | explicit hf hi => exact ⟨2#u32, _, _, hf, Or.inr ⟨rfl, rfl, hi⟩, rfl⟩

/-- Assembles an active data segment from its flag, memory index, offset and
bytes. -/
theorem DataEncoding.of_parts {flags memoryIndex explicit offset init fb mb ob ib}
    (hf : IndexEncoding flags fb)
    (hm : SegmentIndexEncoding flags memoryIndex explicit mb)
    (ho : ConstEncoding offset ob) (hi : ByteVecEncoding init ib) :
    DataEncoding ⟨.Active memoryIndex offset, init⟩ (fb ++ mb ++ ob ++ ib) := by
  exact .active (hm.active hf) ho hi

/-- An `At` interval lies within the buffer. -/
theorem At.span {α : Type} {R : α → List U8 → Prop} {data start value next}
    (h : At R data start value next) : start.val ≤ next.val ∧ next.val ≤ data.length := by
  obtain ⟨bytes, _, hs⟩ := h
  exact ⟨by have := hs.length; omega, hs.bound⟩

/-- `Rep` is closed under concatenation. -/
theorem Rep.append {α : Type} {R : α → List U8 → Prop} {xs ys bs cs}
    (h : Rep R xs bs) (h' : Rep R ys cs) : Rep R (xs ++ ys) (bs ++ cs) := by
  induction h with
  | nil => simpa using h'
  | cons hx _ ih => simpa [List.append_assoc] using Rep.cons hx ih

/-- `Rep` is closed under appending one entry. -/
theorem Rep.snoc {α : Type} {R : α → List U8 → Prop} {xs x bs last}
    (h : Rep R xs bs) (h' : R x last) : Rep R (xs ++ [x]) (bs ++ last) := by
  simpa using h.append (.cons h' .nil)

/-- A `Rep` of raw bytes encodes to the bytes themselves. -/
theorem Rep.bytes {bytes encoded} (h : Rep ByteEncoding bytes encoded) : encoded = bytes := by
  induction h with
  | nil => rfl
  | cons hb _ ih => simp_all [ByteEncoding]

/-- A byte vector is a LEB128 length followed by the bytes. -/
theorem ByteVecEncoding.iff {bytes encoded} : ByteVecEncoding bytes encoded ↔
    ∃ count, Binary.Leb128.Encoding count bytes.length ∧ encoded = count ++ bytes := by
  constructor
  · rintro ⟨count, entries, hc, hr, rfl⟩
    exact ⟨count, hc, by rw [hr.bytes]⟩
  · rintro ⟨count, hc, rfl⟩
    refine ⟨count, bytes, hc, ?_, rfl⟩
    clear hc
    induction bytes with
    | nil => exact .nil
    | cons b bs ih => exact .cons (show ByteEncoding b [b] from rfl) ih

end Itasca.Binary

end

/-! ## PrefixUnique -/

section

/-!
# Prefix uniqueness of the binary grammar

Defines `PrefixUnique` and `Unique` for byte-level relations and shows that they are preserved by
sequences (`PrefixUnique.rep`, `PrefixUnique.rep_unique`) and vectors (`PrefixUnique.vec`). Proves
`PrefixUnique` for the primitive encodings: LEB128 integers, indices, bytes, names and float bits.
Prefix uniqueness is what makes concatenated encodings decode in only one way.
-/

open Aeneas Aeneas.Std

namespace Itasca.Binary

/-- An encoding relation determines both the value and the consumed prefix of any byte string that
starts with an encoding. Suffixes are arbitrary lists, with no implementation bound. -/
def PrefixUnique {α : Type} (R : α → List U8 → Prop) : Prop :=
  ∀ ⦃x y first second rest tail⦄, R x first → R y second →
    first ++ rest = second ++ tail → x = y ∧ first = second ∧ rest = tail

/-- An encoding relation determines its value from the complete byte string. -/
def Unique {α : Type} (R : α → List U8 → Prop) : Prop :=
  ∀ ⦃x y bytes⦄, R x bytes → R y bytes → x = y

/-- Prefix uniqueness implies uniqueness. -/
theorem PrefixUnique.unique {α : Type} {R : α → List U8 → Prop}
    (h : PrefixUnique R) : Unique R := by
  intro x y bytes hx hy
  exact (h hx hy (rest := []) (tail := []) rfl).1

/-- Equal-length prefixes of equal lists are equal, and so are the remainders. -/
theorem split_of_length {α : Type} {xs ys rest tail : List α}
    (he : xs ++ rest = ys ++ tail) (hl : xs.length = ys.length) :
    xs = ys ∧ rest = tail := by
  have h := congrArg (List.take xs.length) he
  have hx : xs = ys := by simpa [List.take_append, hl] using h
  subst ys
  exact ⟨rfl, List.append_cancel_left he⟩

/-- Prefix uniqueness extends to sequences of the same length. -/
theorem PrefixUnique.rep {α : Type} {R : α → List U8 → Prop} (h : PrefixUnique R)
    {xs ys first second rest tail} (hx : Rep R xs first) (hy : Rep R ys second)
    (hl : xs.length = ys.length) (he : first ++ rest = second ++ tail) :
    xs = ys ∧ first = second ∧ rest = tail := by
  induction hx generalizing ys second with
  | nil =>
    cases hy with
    | nil => exact ⟨rfl, rfl, he⟩
    | cons => simp at hl
  | @cons x xs a b ha hb ih =>
    cases hy with
    | nil => simp at hl
    | @cons y ys c d hc hd =>
      obtain ⟨rfl, rfl, ht⟩ := h ha hc (by simpa [List.append_assoc] using he)
      obtain ⟨rfl, rfl, rfl⟩ := ih hd (by simpa using hl) ht
      exact ⟨rfl, rfl, rfl⟩

/-- A prefix-unique relation with nonempty encodings gives unique sequence encodings. -/
theorem PrefixUnique.rep_unique {α : Type} {R : α → List U8 → Prop}
    (h : PrefixUnique R) (hn : ∀ x bs, R x bs → bs ≠ []) : Unique (Rep R) := by
  intro xs ys bytes hx hy
  generalize he : bytes = other at hy
  induction hx generalizing ys other with
  | nil =>
    cases hy with
    | nil => rfl
    | @cons y ys a b ha hb =>
      exact False.elim (hn y a ha (List.append_eq_nil_iff.mp he.symm).1)
  | @cons x xs a b ha hb ih =>
    cases hy with
    | nil =>
      exact False.elim (hn x a ha (List.append_eq_nil_iff.mp he).1)
    | @cons y ys c d hc hd =>
      obtain ⟨rfl, rfl, rfl⟩ := h ha hc he
      exact congrArg (List.cons x) (ih b rfl hd)

/-- Unsigned LEB128 encodings are prefix-unique. -/
theorem leb_prefix_unique : PrefixUnique (fun n bs => Binary.Leb128.Encoding bs n) := by
  intro x y a b rest tail hx hy he
  obtain ⟨rfl, rfl⟩ := Binary.Leb128.Encoding.prefix_unique hx hy he
  exact ⟨rfl, rfl, List.append_cancel_left he⟩

/-- Index encodings are prefix-unique. -/
theorem index_prefix_unique : PrefixUnique IndexEncoding := by
  intro x y a b rest tail hx hy he
  obtain ⟨hv, rfl, ht⟩ := leb_prefix_unique hx hy he
  exact ⟨UScalar.eq_of_val_eq hv, rfl, ht⟩

/-- Vector encodings of a prefix-unique relation are prefix-unique. -/
theorem PrefixUnique.vec {α : Type} {R : α → List U8 → Prop}
    (h : PrefixUnique R) : PrefixUnique (VecEncoding R) := by
  intro xs ys a b rest tail hx hy he
  obtain ⟨n, entries, hn, hx, rfl⟩ := hx
  obtain ⟨m, entries', hm, hy, rfl⟩ := hy
  obtain ⟨hl, rfl, ht⟩ := leb_prefix_unique hn hm (by simpa [List.append_assoc] using he)
  obtain ⟨rfl, rfl, rfl⟩ := h.rep hx hy hl ht
  exact ⟨rfl, rfl, rfl⟩

/-- Raw byte encodings are prefix-unique. -/
theorem byte_prefix_unique : PrefixUnique ByteEncoding := by
  rintro x y a b rest tail rfl rfl he
  obtain ⟨rfl, rfl⟩ := List.cons.inj he
  exact ⟨rfl, rfl, rfl⟩

/-- Name encodings are prefix-unique. -/
theorem name_prefix_unique : PrefixUnique NameEncoding := by
  intro x y a b rest tail hx hy he
  exact byte_prefix_unique.vec hx.1 hy.1 he

/-- Fixed-width float bit pattern encodings are prefix-unique. -/
theorem float_prefix_unique (n : Nat) :
    PrefixUnique (fun bits bs => Binary.FloatBits.Encoding n bs bits) := by
  intro x y a b rest tail hx hy he
  obtain ⟨rfl, rfl⟩ := split_of_length he (hx.1.trans hy.1.symm)
  exact ⟨hx.2.trans hy.2.symm, rfl, rfl⟩

/-- Signed 32-bit LEB128 encodings are prefix-unique. -/
theorem signed32_prefix_unique : PrefixUnique (fun n bs => Binary.SignedLeb32.Encoding bs n) := by
  intro x y a b rest tail hx hy he
  obtain ⟨rfl, rfl⟩ := Binary.SignedLeb32.Encoding.prefix_unique hx hy he
  exact ⟨rfl, rfl, List.append_cancel_left he⟩

/-- Signed 64-bit LEB128 encodings are prefix-unique. -/
theorem signed64_prefix_unique : PrefixUnique (fun n bs => Binary.SignedLeb64.Encoding bs n) := by
  intro x y a b rest tail hx hy he
  obtain ⟨rfl, rfl⟩ := Binary.SignedLeb64.Encoding.prefix_unique hx hy he
  exact ⟨rfl, rfl, List.append_cancel_left he⟩

end Itasca.Binary

end

/-! ## Unicode -/

section

/-!
# Unicode semantics of names

Connects the byte-level `Utf8` grammar to the generated specification's `fun_utf8` relation.
`decodeChars` decodes strict UTF-8, `Utf8.semantic` shows that accepted bytes denote the decoded
string and `NameEncoding.well_formed` shows that a binary name satisfies `wf_name`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Binary

/-- A byte as a generated-specification `byte`. -/
def specByte (b : U8) : byte := .mk_byte b.val

/-- Every byte is well formed. -/
theorem spec_byte_wf (b : U8) : wf_byte (specByte b) := by
  apply wf_byte.byte_case_0
  scalar_tac

/-- Each `Utf8Char` sequence decodes to one well-formed Unicode scalar related to its bytes by
`fun_utf8`. -/
theorem Utf8Char.semantic {bytes : List U8} (h : Utf8Char bytes) (rest : List U8) :
    ∃ ch, decodeChars (bytes ++ rest) = ch :: decodeChars rest ∧
      fun_utf8 [ch] (bytes.map specByte) ∧ wf_char ch := by
  cases h with
  | one a ha =>
      refine ⟨.mk_char a.val, ?_, ?_, ?_⟩
      · rcases rest with _ | ⟨x, (_ | ⟨y, (_ | ⟨z, tail⟩)⟩)⟩ <;>
          simp [decodeChars, show a.val < 128 by omega]
      · exact .fun_utf8_case_0 _ _ ⟨ha.trans_lt (by decide), rfl⟩ (spec_byte_wf a) (spec_byte_wf a)
      · apply wf_char.char_case_0; omega
  | two a b ha ha' hb hb' =>
      refine ⟨.mk_char (64 * (a.val - 192) + (b.val - 128)), ?_, ?_, ?_⟩
      · rcases rest with _ | ⟨x, (_ | ⟨y, tail⟩)⟩ <;>
          simp [decodeChars, show ¬a.val < 128 by omega, show a.val < 224 by omega]
      · apply fun_utf8.fun_utf8_case_1 _ _ _ ?_ (spec_byte_wf a) (spec_byte_wf b)
        simp only [proj_char_0, specByte, proj_byte_0]
        omega
      · apply wf_char.char_case_0; omega
  | three a b c ha hc hc' =>
      refine ⟨.mk_char (4096 * (a.val - 224) + 64 * (b.val - 128) + (c.val - 128)), ?_, ?_, ?_⟩
      · rcases rest with _ | ⟨x, tail⟩ <;>
          simp [decodeChars, show ¬a.val < 128 by omega, show ¬a.val < 224 by omega,
            show a.val < 240 by omega]
      · apply fun_utf8.fun_utf8_case_2 _ _ _ _ ?_ (spec_byte_wf a) (spec_byte_wf b) (spec_byte_wf c)
        simp only [proj_char_0, specByte, proj_byte_0]
        omega
      · apply wf_char.char_case_0; omega
  | four a b c d ha hc hc' hd hd' =>
      refine ⟨.mk_char (262144 * (a.val - 240) + 4096 * (b.val - 128) +
        64 * (c.val - 128) + (d.val - 128)), ?_, ?_, ?_⟩
      · simp [decodeChars, show ¬a.val < 128 by omega, show ¬a.val < 224 by omega,
          show ¬a.val < 240 by omega]
      · apply fun_utf8.fun_utf8_case_3 _ _ _ _ _ ?_ (spec_byte_wf a) (spec_byte_wf b)
          (spec_byte_wf c) (spec_byte_wf d)
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

/-- Accepted UTF-8 bytes are related by `fun_utf8` to the string `decodeChars` computes, and each
scalar is well formed. -/
theorem Utf8.semantic {bytes : List U8} (h : Utf8 bytes) :
    fun_utf8 (decodeChars bytes) (bytes.map specByte) ∧ Forall wf_char (decodeChars bytes) := by
  obtain ⟨chunks, hl, hh, hb, hw⟩ := h.chunks
  have hbytes : Forall wf_byte (concat_ byte chunks) := by
    rw [hb]
    intro b hm
    obtain ⟨source, _, rfl⟩ := List.mem_map.mp hm
    exact spec_byte_wf source
  have hnested : Forall (fun bs => Forall wf_byte bs) chunks := by
    intro bs hbs b hmem
    apply hbytes b
    rw [concat_flatten]
    exact List.mem_flatten.mpr ⟨bs, hbs, hmem⟩
  refine ⟨?_, hw⟩
  rw [← hb]
  exact fun_utf8.fun_utf8_case_4 _ chunks chunks chunks hl hh hl hh hl hh hbytes hnested

/-- A binary name denotes a well-formed generated-specification name, including its UTF-8 byte
size bound. -/
theorem NameEncoding.well_formed {nm bytes} (h : NameEncoding nm bytes) :
    wf_name (nameOfBytes nm) := by
  obtain ⟨count, hcount, _⟩ := ByteVecEncoding.iff.mp h.1
  obtain ⟨hutf, hw⟩ := h.2.semantic
  apply wf_name.name_case_0 _ (nm.map specByte) hutf hw
  simpa using Binary.Leb128.Encoding.value_lt hcount

end Itasca.Binary

end

/-! ## UnicodeUnique -/

section

/-!
# Uniqueness of decoded names

Shows that `decodeChars` is injective on bytes accepted by `Utf8`, by re-encoding scalars
canonically (`Utf8.roundtrip`). `Utf8.name_of_bytes_injective` transports the validator's
duplicate-name check on raw bytes to equality of Unicode names.
-/

open Aeneas Aeneas.Std

namespace Itasca.Binary

/-- The shortest UTF-8 encoding of a scalar, as natural numbers. -/
def encodeChar : char → List Nat
  | .mk_char n =>
      if n < 128 then [n]
      else if n < 2048 then [192 + n / 64, 128 + n % 64]
      else if n < 65536 then [224 + n / 4096, 128 + n / 64 % 64, 128 + n % 64]
      else [240 + n / 262144, 128 + n / 4096 % 64, 128 + n / 64 % 64, 128 + n % 64]

private theorem encode_two (a b : Nat) (ha : 194 ≤ a) (ha' : a ≤ 223)
    (hb : 128 ≤ b) (hb' : b ≤ 191) :
    encodeChar (.mk_char (64 * (a - 192) + (b - 128))) = [a, b] := by
  have hlo : ¬64 * (a - 192) + (b - 128) < 128 := by omega
  have hhi : 64 * (a - 192) + (b - 128) < 2048 := by omega
  simp [encodeChar, hlo, hhi]
  omega

private theorem encode_three (a b c : Nat)
    (ha : (a = 224 ∧ 160 ≤ b ∧ b ≤ 191) ∨
      (225 ≤ a ∧ a ≤ 236 ∧ 128 ≤ b ∧ b ≤ 191) ∨
      (a = 237 ∧ 128 ≤ b ∧ b ≤ 159) ∨
      (238 ≤ a ∧ a ≤ 239 ∧ 128 ≤ b ∧ b ≤ 191))
    (hc : 128 ≤ c) (hc' : c ≤ 191) :
    encodeChar (.mk_char (4096 * (a - 224) + 64 * (b - 128) + (c - 128))) = [a, b, c] := by
  have hlo : ¬4096 * (a - 224) + 64 * (b - 128) + (c - 128) < 128 := by omega
  have hlo' : ¬4096 * (a - 224) + 64 * (b - 128) + (c - 128) < 2048 := by omega
  have hhi : 4096 * (a - 224) + 64 * (b - 128) + (c - 128) < 65536 := by omega
  simp [encodeChar, hlo, hlo', hhi]
  omega

private theorem encode_four (a b c d : Nat)
    (ha : (a = 240 ∧ 144 ≤ b ∧ b ≤ 191) ∨
      (241 ≤ a ∧ a ≤ 243 ∧ 128 ≤ b ∧ b ≤ 191) ∨
      (a = 244 ∧ 128 ≤ b ∧ b ≤ 143))
    (hc : 128 ≤ c) (hc' : c ≤ 191) (hd : 128 ≤ d) (hd' : d ≤ 191) :
    encodeChar (.mk_char (262144 * (a - 240) + 4096 * (b - 128) +
      64 * (c - 128) + (d - 128))) = [a, b, c, d] := by
  have hlo : ¬262144 * (a - 240) + 4096 * (b - 128) + 64 * (c - 128) + (d - 128) < 128 := by omega
  have hlo' : ¬262144 * (a - 240) + 4096 * (b - 128) + 64 * (c - 128) + (d - 128) < 2048 := by omega
  have hlo'' : ¬262144 * (a - 240) + 4096 * (b - 128) + 64 * (c - 128) + (d - 128) < 65536 := by omega
  simp [encodeChar, hlo, hlo', hlo'']
  omega

/-- Decoding a `Utf8Char` sequence and re-encoding the scalar recovers its bytes. -/
theorem Utf8Char.roundtrip {bytes} (h : Utf8Char bytes) (rest : List U8) :
    (decodeChars (bytes ++ rest)).flatMap encodeChar =
      bytes.map UScalar.val ++ (decodeChars rest).flatMap encodeChar := by
  cases h with
  | one a ha =>
      rcases rest with _ | ⟨x, (_ | ⟨y, (_ | ⟨z, tail⟩)⟩)⟩ <;>
        simp [decodeChars, show a.val < 128 by omega, encodeChar]
  | two a b ha ha' hb hb' =>
      have he := encode_two a.val b.val ha ha' hb hb'
      rcases rest with _ | ⟨x, (_ | ⟨y, tail⟩)⟩ <;>
        simp [decodeChars, show ¬a.val < 128 by omega, show a.val < 224 by omega, he]
  | three a b c ha hc hc' =>
      have he := encode_three a.val b.val c.val ha hc hc'
      rcases rest with _ | ⟨x, tail⟩ <;>
        simp [decodeChars, show ¬a.val < 128 by omega, show ¬a.val < 224 by omega,
          show a.val < 240 by omega, he]
  | four a b c d ha hc hc' hd hd' =>
      have he := encode_four a.val b.val c.val d.val ha hc hc' hd hd'
      simp [decodeChars, show ¬a.val < 128 by omega, show ¬a.val < 224 by omega,
        show ¬a.val < 240 by omega, he]

/-- Decoding accepted UTF-8 and re-encoding each scalar recovers the original bytes. -/
theorem Utf8.roundtrip {bytes} (h : Utf8 bytes) :
    (decodeChars bytes).flatMap encodeChar = bytes.map UScalar.val := by
  induction h with
  | nil => rfl
  | cons hc _ ih => rw [hc.roundtrip, ih, List.map_append]

/-- `decodeChars` is injective on accepted UTF-8. -/
theorem Utf8.decode_chars_injective {first rest} (h : Utf8 first) (h' : Utf8 rest)
    (heq : decodeChars first = decodeChars rest) : first = rest := by
  have hbytes : first.map UScalar.val = rest.map UScalar.val := by
    rw [← h.roundtrip, heq, h'.roundtrip]
  clear h h' heq
  induction first generalizing rest with
  | nil => cases rest <;> simp_all
  | cons a first ih =>
      cases rest with
      | nil => simp at hbytes
      | cons b rest =>
          obtain ⟨ha, ht⟩ := List.cons.inj hbytes
          rw [UScalar.eq_of_val_eq ha, ih ht]

/-- For names the binary grammar accepts, equal Unicode names have equal bytes. -/
theorem Utf8.name_of_bytes_injective {first rest} (h : Utf8 first) (h' : Utf8 rest)
    (heq : nameOfBytes first = nameOfBytes rest) : first = rest := by
  exact h.decode_chars_injective h' («name».mk_name.inj heq)

end Itasca.Binary

end

end

/-! ## ModuleUnique -/

section

/-!
# Module Unique

Primitive and section-level prefix uniqueness determine one raw module from exact bytes. Element and data payload grammars feed the final module uniqueness argument.
-/

/-! ## ModuleUniquePrimitives -/

section

/-!
# Prefix uniqueness of module components

Proves `PrefixUnique` for the encodings of value, element, function, table, memory and global
types, constant expressions, imports, exports, globals, locals, and the start section.
-/

open Aeneas Aeneas.Std

namespace Itasca.Binary

theorem value_byte_injective : Function.Injective Itasca.Binary.valueByte := by
  intro a b h
  cases a <;> cases b <;> simp_all [Itasca.Binary.valueByte]

theorem elem_byte_injective : Function.Injective elemByte := by
  intro a b h
  cases a <;> cases b <;> simp_all [elemByte]

theorem mut_byte_injective : Function.Injective mutByte := by
  intro a b h
  cases a <;> cases b <;> simp_all [mutByte]

/-- Value type encodings are prefix-unique. -/
theorem value_type_prefix_unique : PrefixUnique ValueTypeEncoding := by
  rintro x y a b rest tail rfl rfl he
  obtain ⟨hv, rfl⟩ := List.cons.inj he
  obtain rfl := value_byte_injective hv
  exact ⟨rfl, rfl, rfl⟩

/-- Function type encodings are prefix-unique. -/
theorem func_type_prefix_unique : PrefixUnique FuncTypeEncoding := by
  intro x y a b rest tail hx hy he
  obtain ⟨xp, xr, hp, hr, rfl⟩ := hx
  obtain ⟨yp, yr, hp', hr', rfl⟩ := hy
  have hseq1 := (List.cons.inj he).2
  obtain ⟨hpv, rfl, hseq2⟩ := value_type_prefix_unique.vec hp hp' (by simpa [List.append_assoc] using hseq1)
  obtain ⟨hrv, rfl, rfl⟩ := value_type_prefix_unique.vec hr hr' hseq2
  have hp := alloc.vec.Vec.ext _ _ hpv
  have hr := alloc.vec.Vec.ext _ _ hrv
  have hxy : x = y := by cases x; cases y; simp_all
  exact ⟨hxy, rfl, rfl⟩

/-- Limits encodings are prefix-unique. -/
theorem limits_prefix_unique : PrefixUnique LimitsEncoding := by
  intro x y a b rest tail hx hy he
  cases hx <;> cases hy
  all_goals simp only [List.cons_append, List.cons.injEq] at he
  all_goals try { have : (0#u8) = 1#u8 := he.1; contradiction }
  all_goals try { have : (1#u8) = 0#u8 := he.1; contradiction }
  case noMax.noMax x a hx y b hy =>
    obtain ⟨rfl, rfl, rfl⟩ := index_prefix_unique hx hy he.2
    exact ⟨rfl, rfl, rfl⟩
  case max.max x xmax a b hx hm y ymax c d hy hn =>
    obtain ⟨rfl, rfl, ht⟩ := index_prefix_unique hx hy (by simpa [List.append_assoc] using he.2)
    obtain ⟨rfl, rfl, rfl⟩ := index_prefix_unique hm hn ht
    exact ⟨rfl, rfl, rfl⟩

/-- Table type encodings are prefix-unique. -/
theorem table_type_prefix_unique : PrefixUnique TableTypeEncoding := by
  intro x y a b rest tail hx hy he
  obtain ⟨a, hx, rfl⟩ := hx
  obtain ⟨b, hy, rfl⟩ := hy
  obtain ⟨helem, hrest⟩ := List.cons.inj he
  have helem := elem_byte_injective helem
  obtain ⟨hv, rfl, rfl⟩ := limits_prefix_unique hx hy hrest
  have hxy : x = y := by cases x; cases y; simp_all
  exact ⟨hxy, by simp [helem], rfl⟩

/-- Memory type encodings are prefix-unique. -/
theorem mem_type_prefix_unique : PrefixUnique MemTypeEncoding := by
  intro x y a b rest tail hx hy he
  obtain ⟨hv, rfl, rfl⟩ := limits_prefix_unique hx hy he
  have hxy : x = y := by cases x; cases y; cases hv; rfl
  exact ⟨hxy, rfl, rfl⟩

/-- Global type encodings are prefix-unique. -/
theorem global_type_prefix_unique : PrefixUnique GlobalTypeEncoding := by
  rintro x y a b rest tail rfl rfl he
  obtain ⟨hv, hseq1⟩ := List.cons.inj he
  obtain ⟨hm, rfl⟩ := List.cons.inj hseq1
  have hv := value_byte_injective hv
  have hm := mut_byte_injective hm
  have hxy : x = y := by cases x; cases y; simp_all
  exact ⟨hxy, by simp [hv, hm], rfl⟩

/-- Constant expression encodings are prefix-unique. -/
theorem const_prefix_unique : PrefixUnique ConstEncoding := by
  intro x y a b rest tail hx hy he
  cases hx <;> cases hy
  all_goals simp only [List.cons_append, List.cons.injEq] at he
  all_goals try { have := he.1; contradiction }
  case i32.i32 x a hx y b hy =>
    obtain ⟨hv, rfl, hseq1⟩ := signed32_prefix_unique hx hy (by simpa [List.append_assoc] using he.2)
    obtain rfl := IScalar.eq_of_val_eq hv
    obtain rfl := (List.cons.inj hseq1).2
    exact ⟨rfl, rfl, rfl⟩
  case i64.i64 x a hx y b hy =>
    obtain ⟨hv, rfl, hseq1⟩ := signed64_prefix_unique hx hy (by simpa [List.append_assoc] using he.2)
    obtain rfl := IScalar.eq_of_val_eq hv
    obtain rfl := (List.cons.inj hseq1).2
    exact ⟨rfl, rfl, rfl⟩
  case f32.f32 x a hx y b hy =>
    obtain ⟨hv, rfl, hseq1⟩ := float_prefix_unique 4 hx hy (by simpa [List.append_assoc] using he.2)
    obtain rfl := UScalar.eq_of_val_eq hv
    obtain rfl := (List.cons.inj hseq1).2
    exact ⟨rfl, rfl, rfl⟩
  case f64.f64 x a hx y b hy =>
    obtain ⟨hv, rfl, hseq1⟩ := float_prefix_unique 8 hx hy (by simpa [List.append_assoc] using he.2)
    obtain rfl := UScalar.eq_of_val_eq hv
    obtain rfl := (List.cons.inj hseq1).2
    exact ⟨rfl, rfl, rfl⟩
  case globalGet.globalGet x a hx y b hy =>
    obtain ⟨rfl, rfl, hseq1⟩ := index_prefix_unique hx hy (by simpa [List.append_assoc] using he.2)
    obtain rfl := (List.cons.inj hseq1).2
    exact ⟨rfl, rfl, rfl⟩
  case refFunc.refFunc x a hx y b hy =>
    obtain ⟨rfl, rfl, hseq1⟩ := index_prefix_unique hx hy (by simpa [List.append_assoc] using he.2)
    obtain rfl := (List.cons.inj hseq1).2
    exact ⟨rfl, rfl, rfl⟩
  case refNull.refNull x y =>
    obtain rfl := elem_byte_injective he.2.1
    exact ⟨rfl, rfl, he.2.2.2⟩
  case v128.v128 low high sub first second hs hl hh low' high' sub' first' second' hs' hl' hh' =>
    obtain ⟨_, rfl, hseq1⟩ := index_prefix_unique hs hs' (by simpa [List.append_assoc] using he.2)
    obtain ⟨hlo, rfl, hseq2⟩ := float_prefix_unique 8 hl hl' (by simpa [List.append_assoc] using hseq1)
    obtain ⟨hhi, rfl, hseq3⟩ := float_prefix_unique 8 hh hh' (by simpa [List.append_assoc] using hseq2)
    obtain rfl := UScalar.eq_of_val_eq hlo
    obtain rfl := UScalar.eq_of_val_eq hhi
    obtain rfl := (List.cons.inj hseq3).2
    exact ⟨rfl, rfl, rfl⟩

/-- Import descriptor encodings are prefix-unique. -/
theorem import_desc_prefix_unique : PrefixUnique ImportDescEncoding := by
  intro x y a b rest tail hx hy he
  cases hx <;> cases hy
  all_goals simp only [List.cons_append, List.cons.injEq] at he
  all_goals try { have := he.1; contradiction }
  case func.func x a hx y b hy =>
    obtain ⟨rfl, rfl, rfl⟩ := index_prefix_unique hx hy he.2
    exact ⟨rfl, rfl, rfl⟩
  case table.table x a hx y b hy =>
    obtain ⟨rfl, rfl, rfl⟩ := table_type_prefix_unique hx hy he.2
    exact ⟨rfl, rfl, rfl⟩
  case memory.memory x a hx y b hy =>
    obtain ⟨rfl, rfl, rfl⟩ := mem_type_prefix_unique hx hy he.2
    exact ⟨rfl, rfl, rfl⟩
  case global.global x a hx y b hy =>
    obtain ⟨rfl, rfl, rfl⟩ := global_type_prefix_unique hx hy he.2
    exact ⟨rfl, rfl, rfl⟩

/-- Export descriptor encodings are prefix-unique. -/
theorem export_desc_prefix_unique : PrefixUnique ExportDescEncoding := by
  intro x y a b rest tail hx hy he
  cases hx <;> cases hy
  all_goals simp only [List.cons_append, List.cons.injEq] at he
  all_goals try { have := he.1; contradiction }
  all_goals
    rename_i x a hx y b hy
    obtain ⟨rfl, rfl, rfl⟩ := index_prefix_unique hx hy he.2
    exact ⟨rfl, rfl, rfl⟩

/-- Import encodings are prefix-unique. -/
theorem import_prefix_unique : PrefixUnique ImportEncoding := by
  intro x y a b rest tail hx hy he
  obtain ⟨xm, xn, xd, hm, hn, hd, rfl⟩ := hx
  obtain ⟨ym, yn, yd, hm', hn', hd', rfl⟩ := hy
  obtain ⟨hmv, rfl, hseq1⟩ := name_prefix_unique hm hm' (by simpa [List.append_assoc] using he)
  obtain ⟨hnv, rfl, hseq2⟩ := name_prefix_unique hn hn' (by simpa [List.append_assoc] using hseq1)
  obtain ⟨hdv, rfl, rfl⟩ := import_desc_prefix_unique hd hd' hseq2
  have hv : x = y := by cases x; cases y; simp_all
  exact ⟨hv, rfl, rfl⟩

/-- Export encodings are prefix-unique. -/
theorem export_prefix_unique : PrefixUnique ExportEncoding := by
  intro x y a b rest tail hx hy he
  obtain ⟨xn, xd, hn, hd, rfl⟩ := hx
  obtain ⟨yn, yd, hn', hd', rfl⟩ := hy
  obtain ⟨hnv, rfl, hseq1⟩ := name_prefix_unique hn hn' (by simpa [List.append_assoc] using he)
  obtain ⟨hdv, rfl, rfl⟩ := export_desc_prefix_unique hd hd' hseq1
  have hv : x = y := by cases x; cases y; simp_all
  exact ⟨hv, rfl, rfl⟩

/-- Global encodings are prefix-unique. -/
theorem global_prefix_unique : PrefixUnique GlobalEncoding := by
  intro x y a b rest tail hx hy he
  obtain ⟨xt, xe, ht, he', rfl⟩ := hx
  obtain ⟨yt, ye, ht', he'', rfl⟩ := hy
  obtain ⟨htv, rfl, hseq1⟩ := global_type_prefix_unique ht ht' (by simpa [List.append_assoc] using he)
  obtain ⟨hev, rfl, rfl⟩ := const_prefix_unique he' he'' hseq1
  have hv : x = y := by cases x; cases y; simp_all
  exact ⟨hv, rfl, rfl⟩

/-- Local declaration encodings are prefix-unique. -/
theorem local_prefix_unique : PrefixUnique LocalEncoding := by
  intro x y a b rest tail hx hy he
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  obtain ⟨hn, rfl, hseq1⟩ := index_prefix_unique ha hb (by simpa [List.append_assoc] using he)
  obtain ⟨ht, rfl⟩ := List.cons.inj hseq1
  have ht := value_byte_injective ht
  have hv : x = y := Prod.ext hn ht
  exact ⟨hv, by simp [ht], rfl⟩

/-- Start section payload encodings are prefix-unique. -/
theorem start_prefix_unique : PrefixUnique StartEncoding := by
  rintro x y a b rest tail ⟨xi, rfl, hx⟩ ⟨yi, rfl, hy⟩ he
  obtain ⟨rfl, rfl, rfl⟩ := index_prefix_unique hx hy he
  exact ⟨rfl, rfl, rfl⟩

end Itasca.Binary

end

/-! ## ModuleUniqueSections -/

section

/-!
# Section framing

Defines the raw section framing
(`SectionDecode.Encoding`) that erases payload interpretation. `PaddedEncoding.frames` shows
that a field preceded by custom sections is a uniquely framed section list with at most one
payload for the field. `SectionDecode.Field.unique` lifts payload uniqueness to fields.
-/

open Aeneas Aeneas.Std

namespace Itasca.Binary

namespace SectionDecode

/-- A raw section: id byte, LEB128 size and payload bytes, with the payload uninterpreted. -/
def Encoding (frame : U8 × List U8) (bytes : List U8) : Prop :=
  ∃ size, Binary.Leb128.Encoding size frame.2.length ∧ bytes = frame.1 :: (size ++ frame.2)

/-- Raw section frames are prefix-unique. -/
theorem prefix_unique : PrefixUnique Encoding := by
  rintro ⟨xt, xp⟩ ⟨yt, yp⟩ a b rest tail ⟨xn, hx, rfl⟩ ⟨yn, hy, rfl⟩ he
  obtain ⟨rfl, hbody⟩ := List.cons.inj he
  obtain ⟨hlen, rfl, hpayload⟩ := leb_prefix_unique hx hy
    (by simpa [List.append_assoc] using hbody)
  obtain ⟨rfl, rfl⟩ := split_of_length hpayload hlen
  exact ⟨rfl, rfl, rfl⟩

/-- A sequence of raw section frames is determined by its bytes. -/
theorem unique : Unique (Rep Encoding) :=
  prefix_unique.rep_unique (by rintro _ _ ⟨n, hn, rfl⟩; simp)

/-- The payloads of the sections with the given id, in order. -/
def payloads (id : U8) : List (U8 × List U8) → List (List U8)
  | [] => []
  | (tag, bytes) :: sections =>
      if id = tag then bytes :: payloads id sections else payloads id sections

theorem payloads_append (id : U8) (xs ys : List (U8 × List U8)) :
    payloads id (xs ++ ys) = payloads id xs ++ payloads id ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x; simp only [List.cons_append, payloads]; split <;> simp_all

/-- A standard field is either omitted, giving `absent`, or encoded by exactly one payload. -/
inductive Field {α : Type} (R : α → List U8 → Prop) (absent : α) : α → List (List U8) → Prop where
  | absent : Field R absent absent []
  | present {value bytes} : R value bytes → Field R absent value [bytes]

/-- A field's value is determined by its payloads. -/
theorem Field.unique {α : Type} {R : α → List U8 → Prop} {absent x y payloads}
    (hu : Unique R) (hx : Field R absent x payloads) (hy : Field R absent y payloads) : x = y := by
  cases hx <;> cases hy
  · rfl
  · apply hu <;> assumption

end SectionDecode

/-- A section encoding gives a raw frame with the same payload. -/
theorem SectionEncoding.frame {α : Type} {R : α → List U8 → Prop} {id value bytes}
    (h : SectionEncoding id R value bytes) :
    ∃ payload, R value payload ∧ SectionDecode.Encoding (id, payload) bytes := by
  obtain ⟨size, payload, hn, hp, rfl⟩ := h
  exact ⟨payload, hp, size, hn, rfl⟩

/-- Custom sections frame into a section list with no payload for any other id. -/
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

/-- A field preceded by custom sections frames into a section list with the field's payload
under its own id and none under other ids. -/
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

end Itasca.Binary

end

/-! ## ModuleUniqueSegments -/

section

/-!
# Prefix uniqueness of segments

Proves `PrefixUnique` for the Wasm 2.0 element and data segment encodings by splitting off the
flag and treating each flag's payload grammar separately.
-/

open Aeneas Aeneas.Std

namespace Itasca.Binary

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

private theorem element_parts {entry bytes} (h : ElementEncoding entry bytes) :
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

private theorem element_payload_prefix_unique (flag : Nat) : PrefixUnique (ElementPayload flag) := by
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
    obtain rfl := elem_byte_injective ht
    obtain ⟨rfl, rfl, rfl⟩ := const_prefix_unique.vec hi hi' hs
    exact ⟨rfl, rfl, rfl⟩
  case explicitExpressions.explicitExpressions elem table offset initializers tb ob ib ht ho hi elem' table' offset' initializers' tb' ob' ib' ht' ho' hi' =>
    obtain ⟨rfl, rfl, hs⟩ := index_prefix_unique ht ht' (by simpa [List.append_assoc] using he)
    obtain ⟨rfl, rfl, hs'⟩ := const_prefix_unique ho ho' (by simpa [List.append_assoc] using hs)
    obtain ⟨hty, hs''⟩ := List.cons.inj hs'
    obtain rfl := elem_byte_injective hty
    obtain ⟨rfl, rfl, rfl⟩ := const_prefix_unique.vec hi hi' hs''
    exact ⟨rfl, rfl, rfl⟩
  case declarativeExpressions.declarativeExpressions elem initializers entries hi elem' initializers' entries' hi' =>
    obtain ⟨ht, hs⟩ := List.cons.inj he
    obtain rfl := elem_byte_injective ht
    obtain ⟨rfl, rfl, rfl⟩ := const_prefix_unique.vec hi hi' hs
    exact ⟨rfl, rfl, rfl⟩

/-- Wasm 2.0 element segment encodings are prefix-unique. -/
theorem element_encoding_prefix_unique : PrefixUnique ElementEncoding := by
  intro x y a b rest tail hx hy he
  obtain ⟨xf, xb, xp, hxf, hxp, rfl⟩ := element_parts hx
  obtain ⟨yf, yb, yp, hyf, hyp, rfl⟩ := element_parts hy
  obtain ⟨rfl, rfl, hs⟩ := index_prefix_unique hxf hyf (by simpa [List.append_assoc] using he)
  obtain ⟨rfl, rfl, rfl⟩ := element_payload_prefix_unique _ hxp hyp hs
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

private theorem data_parts {entry bytes} (h : DataEncoding entry bytes) :
    ∃ flag flags payload, IndexEncoding flag flags ∧ DataPayload flag.val entry payload ∧
      bytes = flags ++ payload := by
  cases h with
  | active hi ho hb =>
    cases hi with
    | implicit hf => exact ⟨0#u32, _, _, hf, .implicit ho hb, by simp [List.append_assoc]⟩
    | explicit hf hi => exact ⟨2#u32, _, _, hf, .explicit hi ho hb, by simp [List.append_assoc]⟩
  | passive hf hb => exact ⟨1#u32, _, _, hf, .passive hb, rfl⟩

private theorem data_payload_prefix_unique (flag : Nat) : PrefixUnique (DataPayload flag) := by
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
theorem data_encoding_prefix_unique : PrefixUnique DataEncoding := by
  intro x y a b rest tail hx hy he
  obtain ⟨xf, xb, xp, hxf, hxp, rfl⟩ := data_parts hx
  obtain ⟨yf, yb, yp, hyf, hyp, rfl⟩ := data_parts hy
  obtain ⟨rfl, rfl, hs⟩ := index_prefix_unique hxf hyf (by simpa [List.append_assoc] using he)
  obtain ⟨rfl, rfl, rfl⟩ := data_payload_prefix_unique _ hxp hyp hs
  exact ⟨rfl, rfl, rfl⟩

end Itasca.Binary

end

/-! ## ModuleUnique -/

section

/-!
# Uniqueness of module decoding

`ModuleEncodingWith.unique` shows that two raw modules with the same encoding are equal, for
Wasm 2.0 and any prefix-unique code entry grammar. Custom section placement and omitted
empty sections introduce no ambiguity. `Itasca/Results/Unique` specializes it to the validator’s code entry grammar.
-/

open Aeneas Aeneas.Std

namespace Itasca.Binary

/-- The data count section frames like other optional fields. -/
theorem DataCountSectionEncoding.frames {value bytes}
    (h : DataCountSectionEncoding value bytes) :
    ∃ sections payloads, Rep SectionDecode.Encoding sections bytes ∧
      SectionDecode.Field StartEncoding none value payloads ∧
      ∀ wanted, wanted ≠ 0#u8 → SectionDecode.payloads wanted sections =
        if wanted = 12#u8 then payloads else [] := by
  exact PaddedEncoding.frames h

namespace SectionDecode

/-- The standard fields of a raw module as payloads of a raw section list. -/
structure Fields (raw : Module) (sections : List (U8 × List U8))
    (codeRel : Code → List U8 → Prop) : Prop where
  types : Field (VecEncoding FuncTypeEncoding) [] raw.types (payloads 1#u8 sections)
  imports : Field (VecEncoding ImportEncoding) [] raw.imports (payloads 2#u8 sections)
  functions : Field (VecEncoding IndexEncoding) [] raw.functions (payloads 3#u8 sections)
  tables : Field (VecEncoding TableTypeEncoding) [] raw.tables (payloads 4#u8 sections)
  memories : Field (VecEncoding MemTypeEncoding) [] raw.memories (payloads 5#u8 sections)
  globals : Field (VecEncoding GlobalEncoding) [] raw.globals (payloads 6#u8 sections)
  exports : Field (VecEncoding ExportEncoding) [] raw.exports (payloads 7#u8 sections)
  start : Field StartEncoding none raw.start (payloads 8#u8 sections)
  elements : Field (VecEncoding ElementEncoding) [] raw.elements (payloads 9#u8 sections)
  dataCount : Field StartEncoding none raw.dataCount (payloads 12#u8 sections)
  codes : Field (VecEncoding codeRel) [] raw.codes (payloads 10#u8 sections)
  data : Field (VecEncoding DataEncoding) [] raw.data (payloads 11#u8 sections)

end SectionDecode

/-- A module encoding gives a raw section list that carries every standard field. -/
theorem ModuleEncodingWith.sections {codeRel raw bytes}
    (h : ModuleEncodingWith codeRel raw bytes) :
    ∃ sections, Rep SectionDecode.Encoding sections (bytes.drop magicVersion.length) ∧
      SectionDecode.Fields raw sections codeRel := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, bc, b10, b11, b12,
    h1, h2, h3, h4, h5, h6, h7, h8, h9, hc, h10, h11, h12, hb, _⟩ := h
  obtain ⟨s1, p1, hr1, hf1, hl1⟩ := h1.frames
  obtain ⟨s2, p2, hr2, hf2, hl2⟩ := h2.frames
  obtain ⟨s3, p3, hr3, hf3, hl3⟩ := h3.frames
  obtain ⟨s4, p4, hr4, hf4, hl4⟩ := h4.frames
  obtain ⟨s5, p5, hr5, hf5, hl5⟩ := h5.frames
  obtain ⟨s6, p6, hr6, hf6, hl6⟩ := h6.frames
  obtain ⟨s7, p7, hr7, hf7, hl7⟩ := h7.frames
  obtain ⟨s8, p8, hr8, hf8, hl8⟩ := h8.frames
  obtain ⟨s9, p9, hr9, hf9, hl9⟩ := h9.frames
  obtain ⟨sCount, pCount, hrCount, hfCount, hlCount⟩ := hc.frames
  obtain ⟨s10, p10, hr10, hf10, hl10⟩ := h10.frames
  obtain ⟨s11, p11, hr11, hf11, hl11⟩ := h11.frames
  obtain ⟨sc, hrc, hlc⟩ := h12.frames
  let sections := s1 ++ s2 ++ s3 ++ s4 ++ s5 ++ s6 ++ s7 ++ s8 ++ s9 ++ sCount ++ s10 ++ s11 ++ sc
  have hr : Rep SectionDecode.Encoding sections
      (b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7 ++ b8 ++ b9 ++ bc ++ b10 ++ b11 ++ b12) :=
    ((((((((((((hr1.append hr2).append hr3).append hr4).append hr5).append hr6).append hr7).append hr8).append hr9).append hrCount).append hr10).append hr11).append hrc)
  have lookup (id : U8) (hid : id ≠ 0#u8) :
      SectionDecode.payloads id sections =
        (if id = 1#u8 then p1 else []) ++
        (if id = 2#u8 then p2 else []) ++
        (if id = 3#u8 then p3 else []) ++
        (if id = 4#u8 then p4 else []) ++
        (if id = 5#u8 then p5 else []) ++
        (if id = 6#u8 then p6 else []) ++
        (if id = 7#u8 then p7 else []) ++
        (if id = 8#u8 then p8 else []) ++
        (if id = 9#u8 then p9 else []) ++
        (if id = 12#u8 then pCount else []) ++
        (if id = 10#u8 then p10 else []) ++
        (if id = 11#u8 then p11 else []) := by
    simp only [sections, SectionDecode.payloads_append, hl1 id hid, hl2 id hid, hl3 id hid,
      hl4 id hid, hl5 id hid, hl6 id hid, hl7 id hid, hl8 id hid, hl9 id hid, hlCount id hid, hl10 id hid,
      hl11 id hid, hlc id hid, List.append_nil]
  refine ⟨sections, ?_, ?_⟩
  · simpa only [hb, List.append_assoc, List.drop_left] using hr
  · constructor
    · simpa [lookup 1#u8 (by decide)] using hf1
    · simpa [lookup 2#u8 (by decide)] using hf2
    · simpa [lookup 3#u8 (by decide)] using hf3
    · simpa [lookup 4#u8 (by decide)] using hf4
    · simpa [lookup 5#u8 (by decide)] using hf5
    · simpa [lookup 6#u8 (by decide)] using hf6
    · simpa [lookup 7#u8 (by decide)] using hf7
    · simpa [lookup 8#u8 (by decide)] using hf8
    · simpa [lookup 9#u8 (by decide)] using hf9
    · simpa [lookup 12#u8 (by decide)] using hfCount
    · simpa [lookup 10#u8 (by decide)] using hf10
    · simpa [lookup 11#u8 (by decide)] using hf11

/-- A byte string encodes at most one raw module, with no typing or implementation limit premise. -/
theorem ModuleEncodingWith.unique {codeRel x y bytes}
    (hcode : PrefixUnique codeRel)
    (hx : ModuleEncodingWith codeRel x bytes)
    (hy : ModuleEncodingWith codeRel y bytes) : x = y := by
  obtain ⟨xs, hxs, hxf⟩ := hx.sections
  obtain ⟨ys, hys, hyf⟩ := hy.sections
  have he := SectionDecode.unique hxs hys
  subst ys
  have h_types := SectionDecode.Field.unique func_type_prefix_unique.vec.unique hxf.types hyf.types
  have h_imports := SectionDecode.Field.unique import_prefix_unique.vec.unique hxf.imports hyf.imports
  have h_functions := SectionDecode.Field.unique index_prefix_unique.vec.unique hxf.functions hyf.functions
  have h_tables := SectionDecode.Field.unique table_type_prefix_unique.vec.unique hxf.tables hyf.tables
  have h_memories := SectionDecode.Field.unique mem_type_prefix_unique.vec.unique hxf.memories hyf.memories
  have h_globals := SectionDecode.Field.unique global_prefix_unique.vec.unique hxf.globals hyf.globals
  have h_exports := SectionDecode.Field.unique export_prefix_unique.vec.unique hxf.exports hyf.exports
  have h_start := SectionDecode.Field.unique start_prefix_unique.unique hxf.start hyf.start
  have h_elements := SectionDecode.Field.unique element_encoding_prefix_unique.vec.unique hxf.elements hyf.elements
  have h_count := SectionDecode.Field.unique start_prefix_unique.unique hxf.dataCount hyf.dataCount
  have h_codes := SectionDecode.Field.unique hcode.vec.unique hxf.codes hyf.codes
  have h_data := SectionDecode.Field.unique data_encoding_prefix_unique.vec.unique hxf.data hyf.data
  cases x; cases y; simp_all

end Itasca.Binary

end

end
