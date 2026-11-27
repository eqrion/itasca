import Itasca.Binary.ReaderIndex
import WebAssembly.Binary.Map
import WebAssembly.Binary.ModuleUnique
import Itasca.Binary.SourceInjective
import Itasca.Binary.LebBytes
import Itasca.Binary.Definitions
import Itasca.Results.Definitions.Binary
import Itasca.Binary.Scalar.Encoding

open WebAssembly

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

theorem ByteVecEncoding.source_iff {xs bs} :
    ByteVecEncoding xs bs ↔ WebAssembly.Binary.ByteVecEncoding (Source.bytes xs) (Source.bytes bs) := by
  constructor
  · intro h
    exact WebAssembly.Binary.VecEncodingWith.map sourceByte sourceByte
      (fun e => (Leb128.encoding_iff _ _).mp e) (fun e => congrArg Source.bytes e) h
  · intro h
    have result : ByteVecEncoding (Source.readerBytes (Source.bytes xs))
        (Source.readerBytes (Source.bytes bs)) :=
      WebAssembly.Binary.VecEncodingWith.map Source.readerByte Source.readerByte
        (fun e => Source.readerLeb e) (fun e => congrArg Source.readerBytes e) h
    simpa only [Source.readerBytes_bytes] using result

theorem SegmentIndexEncoding.active {flags index explicit bytes headBytes}
    (h : SegmentIndexEncoding flags index explicit bytes)
    (hf : IndexEncoding flags headBytes) : ActiveIndexEncoding index explicit (headBytes ++ bytes) := by
  rcases h with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, hi⟩
  · rw [List.append_nil]
    exact .implicit ((Leb128.encoding_iff _ _).mp hf)
  · simp only [ActiveIndexEncoding, Source.bytes, List.map_append]
    exact .explicit ((Leb128.encoding_iff _ _).mp hf) ((Leb128.encoding_iff _ _).mp hi)

theorem ActiveIndexEncoding.parts {index explicit bs} (h : ActiveIndexEncoding index explicit bs) :
    ∃ flags headBytes suffix, IndexEncoding flags headBytes ∧
      SegmentIndexEncoding flags index explicit suffix ∧ bs = headBytes ++ suffix := by
  unfold ActiveIndexEncoding at h
  generalize hi : index.val = n at h
  generalize hb : Source.bytes bs = raw at h
  cases h with
  | implicit hf =>
    have eq : index = 0#u32 := UScalar.eq_of_val_eq hi
    subst index
    exact ⟨0#u32, bs, [], (Leb128.encoding_iff _ _).mpr (hb ▸ hf),
      Or.inl ⟨rfl, rfl, rfl, rfl⟩, (List.append_nil bs).symm⟩
  | explicit hf hx =>
    obtain ⟨fb, ib, rfl, rfl, rfl⟩ := List.map_eq_append_iff.mp hb
    exact ⟨2#u32, fb, ib, (Leb128.encoding_iff _ _).mpr hf,
      Or.inr ⟨rfl, rfl, (Leb128.encoding_iff _ _).mpr (hi.symm ▸ hx)⟩, rfl⟩

theorem DataEncoding.of_parts {flags memoryIndex explicit offset init fb mb ob ib}
    (hf : IndexEncoding flags fb)
    (hm : SegmentIndexEncoding flags memoryIndex explicit mb)
    (ho : ConstEncoding offset ob) (hi : ByteVecEncoding init ib) :
    DataEncoding ⟨.Active memoryIndex offset, init⟩ (fb ++ mb ++ ob ++ ib) := by
  change WebAssembly.Binary.DataEncoding _ (Source.bytes ((fb ++ mb ++ ob) ++ ib))
  rw [show Source.bytes (fb ++ mb ++ ob ++ ib) =
      Source.bytes (fb ++ mb) ++ Source.bytes ob ++ Source.bytes ib by simp [Source.bytes]]
  exact .active (hm.active hf) ho (ByteVecEncoding.source_iff.mp hi)

theorem DataEncoding.of_passive {init fb ib} (hf : IndexEncoding 1#u32 fb) (hi : ByteVecEncoding init ib) :
    DataEncoding ⟨.Passive, init⟩ (fb ++ ib) := by
  simp only [DataEncoding, Source.bytes, List.map_append]
  exact .passive ((Leb128.encoding_iff _ _).mp hf) (ByteVecEncoding.source_iff.mp hi)

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
  | cons hx _ ih => simpa [List.append_assoc] using WebAssembly.Binary.Rep.cons hx ih

/-- `Rep` is closed under appending one entry. -/
theorem Rep.snoc {α : Type} {R : α → List U8 → Prop} {xs x bs last}
    (h : Rep R xs bs) (h' : R x last) : Rep R (xs ++ [x]) (bs ++ last) := by
  simpa using h.append (.cons h' .nil)

/-- A `Rep` of raw bytes encodes to the bytes themselves. -/
theorem Rep.bytes {bytes encoded} (h : Rep ByteEncoding bytes encoded) : encoded = bytes := by
  induction h with
  | nil => rfl
  | cons hb _ ih => simp_all [WebAssembly.Binary.ByteEncoding]

/-- A byte vector is a LEB128 length followed by the bytes. -/
theorem ByteVecEncoding.iff {bytes encoded} : ByteVecEncoding bytes encoded ↔
    ∃ count, Binary.Leb128.Encoding count bytes.length ∧ encoded = count ++ bytes := by
  constructor
  · rintro ⟨count, entries, hc, hr, rfl⟩
    exact ⟨count, hc, by rw [Rep.bytes hr]⟩
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
      obtain ⟨ch, hd, he, hw⟩ := Utf8Char.semantic hc rest
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
  obtain ⟨hutf, hw⟩ := Utf8.semantic h.2
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
  | cons hc _ ih => rw [Utf8Char.roundtrip hc, ih, List.map_append]

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
  cases a <;> cases b <;> first | rfl | contradiction

theorem elem_byte_injective : Function.Injective elemByte := by
  intro a b h
  cases a <;> cases b <;> first | rfl | contradiction

/-- Value type encodings are prefix-unique. -/
theorem value_type_prefix_unique : PrefixUnique ValueTypeEncoding := by
  intro x y a b rest tail hx hy he
  obtain rfl := ValueTypeEncoding.reader_bytes.mp hx
  obtain rfl := ValueTypeEncoding.reader_bytes.mp hy
  obtain ⟨hv, rfl⟩ := List.cons.inj he
  obtain rfl := value_byte_injective hv
  exact ⟨rfl, rfl, rfl⟩

theorem VecEncoding.source_map {f : α → β} {R : β → List UInt8 → Prop} {xs bs}
    (h : VecEncoding (fun x raw => R (f x) (Source.bytes raw)) xs bs) :
    WebAssembly.Binary.VecEncoding R (xs.map f) (Source.bytes bs) :=
  WebAssembly.Binary.VecEncodingWith.map f sourceByte (fun h => (Leb128.encoding_iff _ _).mp h) (fun h => h) h

theorem VecEncoding.reader_map {f : α → β} {R : β → List UInt8 → Prop} {xs bs}
    (h : WebAssembly.Binary.VecEncoding R (xs.map f) bs) :
    VecEncoding (fun x raw => R (f x) (Source.bytes raw)) xs (Source.readerBytes bs) :=
  WebAssembly.Binary.VecEncodingWith.unmapValues f Source.readerByte (fun h => Source.readerLeb h)
    (fun h => by simpa only [Source.bytes_readerBytes] using h) h

theorem FuncTypeEncoding.reader_parts {ty bs} : FuncTypeEncoding ty bs ↔
    ∃ ps rs, VecEncoding ValueTypeEncoding ty.params.val ps ∧ VecEncoding ValueTypeEncoding ty.results.val rs ∧
      bs = 0x60#u8 :: (ps ++ rs) := by
  constructor
  · rintro ⟨ps, rs, hp, hr, eq⟩
    refine ⟨Source.readerBytes ps, Source.readerBytes rs, VecEncoding.reader_map hp, VecEncoding.reader_map hr, ?_⟩
    have he := congrArg Source.readerBytes eq
    rw [Source.readerBytes_bytes] at he
    exact he.trans (congrArg (_ :: ·) List.map_append)
  · rintro ⟨ps, rs, hp, hr, rfl⟩
    exact ⟨Source.bytes ps, Source.bytes rs, VecEncoding.source_map hp, VecEncoding.source_map hr,
      congrArg (_ :: ·) List.map_append⟩

/-- Function type encodings are prefix-unique. -/
theorem func_type_prefix_unique : PrefixUnique FuncTypeEncoding := by
  intro x y a b rest tail hx hy he
  obtain ⟨xp, xr, hp, hr, rfl⟩ := FuncTypeEncoding.reader_parts.mp hx
  obtain ⟨yp, yr, hp', hr', rfl⟩ := FuncTypeEncoding.reader_parts.mp hy
  have hseq1 := (List.cons.inj he).2
  obtain ⟨hpv, rfl, hseq2⟩ := value_type_prefix_unique.vec hp hp' (by simpa [List.append_assoc] using hseq1)
  obtain ⟨hrv, rfl, rfl⟩ := value_type_prefix_unique.vec hr hr' hseq2
  have hp := alloc.vec.Vec.ext _ _ hpv
  have hr := alloc.vec.Vec.ext _ _ hrv
  have hxy : x = y := by cases x; cases y; simp_all
  exact ⟨hxy, rfl, rfl⟩

theorem PrefixUnique.of_source {R : β → List UInt8 → Prop} {f : α → β}
    (h : WebAssembly.Binary.PrefixUnique R) (hf : Function.Injective f) :
    PrefixUnique (fun x bs => R (f x) (Source.bytes bs)) := by
  intro x y a b rest tail hx hy he
  have eq := congrArg Source.bytes he
  simp only [Source.bytes, List.map_append] at eq
  obtain ⟨hv, hab, hrt⟩ := h hx hy eq
  exact ⟨hf hv, by simpa only [Source.readerBytes_bytes] using congrArg Source.readerBytes hab,
    by simpa only [Source.readerBytes_bytes] using congrArg Source.readerBytes hrt⟩

/-- Limits encodings are prefix-unique. -/
theorem limits_prefix_unique : PrefixUnique LimitsEncoding :=
  PrefixUnique.of_source WebAssembly.Binary.LimitsEncoding.prefix_unique Source.limitsType

theorem tableType_reader_span {ty bs} (h : TableTypeEncoding ty bs) :
    ∃ ls, LimitsEncoding ty.limits ls ∧ bs = elemByte ty.elem :: ls := by
  obtain ⟨ls, hl, he⟩ := h
  refine ⟨Source.readerBytes ls, by simpa only [LimitsEncoding, Source.bytes_readerBytes] using hl, ?_⟩
  have eq := congrArg Source.readerBytes he
  rw [Source.readerBytes_bytes] at eq
  exact eq.trans (by cases ty.elem <;> rfl)

/-- Table type encodings are prefix-unique. -/
theorem table_type_prefix_unique : PrefixUnique TableTypeEncoding :=
  PrefixUnique.of_source WebAssembly.Binary.TableTypeEncoding.prefix_unique Source.tableType

/-- Memory type encodings are prefix-unique. -/
theorem mem_type_prefix_unique : PrefixUnique MemTypeEncoding :=
  PrefixUnique.of_source WebAssembly.Binary.MemTypeEncoding.prefix_unique Source.memType

theorem GlobalTypeEncoding.reader_bytes {ty bs} : GlobalTypeEncoding ty bs ↔
    bs = [Itasca.Binary.valueByte ty.valtype, mutByte ty.mutability] := by
  constructor
  · rintro ⟨vt, he, hb⟩
    have eq : Source.valueType ty.valtype = vt := by
      have inj : Function.Injective WebAssembly.Binary.ValueType.toSpec := by
        intro a b h
        cases a <;> cases b <;> first | rfl | contradiction
      exact inj ((Source.valueType_toSpec ty.valtype).trans he)
    subst vt
    have hb' := congrArg Source.readerBytes hb
    rw [Source.readerBytes_bytes] at hb'
    exact hb'.trans (by cases ty with | mk m t => cases m <;> cases t <;> rfl)
  · rintro rfl
    refine ⟨Source.valueType _, (Source.valueType_toSpec _).symm, ?_⟩
    cases ty with | mk m t => cases m <;> cases t <;> rfl

/-- Global type encodings are prefix-unique. -/
theorem global_type_prefix_unique : PrefixUnique GlobalTypeEncoding :=
  PrefixUnique.of_source WebAssembly.Binary.GlobalTypeEncoding.prefix_unique Source.globalType

/-- Constant expression encodings are prefix-unique. -/
theorem const_prefix_unique : PrefixUnique ConstEncoding :=
  PrefixUnique.of_source WebAssembly.Binary.ConstEncoding.prefix_unique Source.constantInjective

/-- Import descriptor encodings are prefix-unique. -/
theorem import_desc_prefix_unique : PrefixUnique ImportDescEncoding :=
  PrefixUnique.of_source WebAssembly.Binary.ImportDescEncoding.prefix_unique Source.importDescInjective

/-- Export descriptor encodings are prefix-unique. -/
theorem export_desc_prefix_unique : PrefixUnique ExportDescEncoding :=
  PrefixUnique.of_source WebAssembly.Binary.ExportDescEncoding.prefix_unique Source.exportDescInjective

theorem NameEncoding.source_iff {nm bs} :
    NameEncoding nm bs ↔ WebAssembly.Binary.NameEncoding (Source.bytes nm) (Source.bytes bs) := by
  constructor
  · intro h
    exact WebAssembly.Binary.NameEncodingWith.map sourceByte (fun h => (Leb128.encoding_iff _ _).mp h) h
  · intro h
    have hc {cs n} (e : WebAssembly.Binary.Leb128.U32Encoding cs n) :
        Leb128.Encoding (Source.readerBytes cs) n :=
      (Leb128.encoding_iff _ _).mpr (by simpa only [Source.bytes_readerBytes] using e)
    have result := WebAssembly.Binary.NameEncodingWith.map (byte := @UScalar.val .U8)
      Source.readerByte @hc h
    simpa only [Source.readerBytes_bytes] using result

theorem ImportEncoding.reader_parts {entry bs} : ImportEncoding entry bs ↔
    ∃ a b c, NameEncoding entry.moduleName a ∧ NameEncoding entry.name b ∧ ImportDescEncoding entry.desc c ∧ bs = a ++ b ++ c := by
  constructor
  · rintro ⟨a, b, c, ha, hb, hc, he⟩
    obtain ⟨left, right, rfl, hleft, hright⟩ := List.map_eq_append_iff.mp he
    obtain ⟨first, middle, rfl, hfirst, hmiddle⟩ := List.map_eq_append_iff.mp hleft
    subst a
    subst b
    subst c
    exact ⟨first, middle, right, NameEncoding.source_iff.mpr ha, NameEncoding.source_iff.mpr hb, hc, rfl⟩
  · rintro ⟨a, b, c, ha, hb, hc, rfl⟩
    exact ⟨Source.bytes a, Source.bytes b, Source.bytes c, NameEncoding.source_iff.mp ha, NameEncoding.source_iff.mp hb, hc, by simp [Source.bytes]⟩

theorem ExportEncoding.reader_parts {entry bs} : ExportEncoding entry bs ↔
    ∃ a b, NameEncoding entry.name a ∧ ExportDescEncoding entry.desc b ∧ bs = a ++ b := by
  constructor
  · rintro ⟨a, b, ha, hb, he⟩
    obtain ⟨left, right, rfl, hleft, hright⟩ := List.map_eq_append_iff.mp he
    subst a
    subst b
    exact ⟨left, right, NameEncoding.source_iff.mpr ha, hb, rfl⟩
  · rintro ⟨a, b, ha, hb, rfl⟩
    exact ⟨Source.bytes a, Source.bytes b, NameEncoding.source_iff.mp ha, hb, by simp [Source.bytes]⟩

theorem GlobalEncoding.reader_parts {entry bs} : GlobalEncoding entry bs ↔
    ∃ a b, GlobalTypeEncoding entry.gtype a ∧ ConstEncoding entry.init b ∧ bs = a ++ b := by
  constructor
  · rintro ⟨a, b, ha, hb, he⟩
    obtain ⟨left, right, rfl, hleft, hright⟩ := List.map_eq_append_iff.mp he
    subst a
    subst b
    exact ⟨left, right, ha, hb, rfl⟩
  · rintro ⟨a, b, ha, hb, rfl⟩
    exact ⟨Source.bytes a, Source.bytes b, ha, hb, by simp [Source.bytes]⟩

/-- Import encodings are prefix-unique. -/
theorem import_prefix_unique : PrefixUnique ImportEncoding :=
  PrefixUnique.of_source WebAssembly.Binary.ImportEncoding.prefix_unique Source.importEntryInjective

/-- Export encodings are prefix-unique. -/
theorem export_prefix_unique : PrefixUnique ExportEncoding :=
  PrefixUnique.of_source WebAssembly.Binary.ExportEncoding.prefix_unique Source.exportEntryInjective

/-- Global encodings are prefix-unique. -/
theorem global_prefix_unique : PrefixUnique GlobalEncoding :=
  PrefixUnique.of_source WebAssembly.Binary.GlobalEncoding.prefix_unique Source.globalEntryInjective

theorem LocalEncoding.reader_parts {entry bs} : LocalEncoding entry bs ↔
    ∃ count, IndexEncoding entry.1 count ∧ bs = count ++ [valueByte entry.2] := by
  constructor
  · rintro ⟨count, hc, eq⟩
    refine ⟨Source.readerBytes count, Source.readerLeb hc, ?_⟩
    have he := congrArg Source.readerBytes eq
    rw [Source.readerBytes_bytes] at he
    exact he.trans (List.map_append ..)
  · rintro ⟨count, hc, rfl⟩
    exact ⟨Source.bytes count, (Leb128.encoding_iff _ _).mp hc, List.map_append ..⟩

theorem local_prefix_unique : PrefixUnique LocalEncoding :=
  PrefixUnique.of_source WebAssembly.Binary.LocalEncoding.prefix_unique Source.localDeclInjective

/-- Start section payload encodings are prefix-unique. -/
theorem start_prefix_unique : PrefixUnique StartEncoding := by
  rintro x y a b rest tail ⟨xi, rfl, hx⟩ ⟨yi, rfl, hy⟩ he
  obtain ⟨rfl, rfl, rfl⟩ := index_prefix_unique hx hy he
  exact ⟨rfl, rfl, rfl⟩

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

abbrev ElementHeaderEncoding (mode elem ex) (bs : List U8) :=
  WebAssembly.Binary.ElementHeaderEncoding (Source.elementMode mode) (Translation.referenceType elem) ex (Source.bytes bs)

abbrev ElementInitializerEncoding (ex : Bool) (v : wasm_types.ConstExpr) (bs : List U8) :=
  WebAssembly.Binary.InitializerEncoding ex (Source.constant v) (Source.bytes bs)

theorem ElementInitializerEncoding.index_parts {v bs} : ElementInitializerEncoding false v bs ↔
    ∃ i, v = .RefFunc i ∧ IndexEncoding i bs := by
  constructor
  · rintro ⟨n, eq, hn⟩
    obtain ⟨i, rfl, _⟩ := Source.readerIndex hn
    exact ⟨i, Source.constantInjective eq, (Leb128.encoding_iff _ _).mpr hn⟩
  · rintro ⟨i, rfl, hi⟩
    exact ⟨i.val, rfl, (Leb128.encoding_iff _ _).mp hi⟩

theorem ElementEncoding.reader_parts {e bs} : ElementEncoding e bs ↔
    ∃ ex header init, ElementHeaderEncoding e.mode e.elem ex header ∧
      VecEncoding (ElementInitializerEncoding ex) e.init init ∧ bs = header ++ init := by
  constructor
  · rintro ⟨ex, header, init, hh, hi, eq⟩
    refine ⟨ex, Source.readerBytes header, Source.readerBytes init, ?_, VecEncoding.reader_map hi, ?_⟩
    · simpa only [ElementHeaderEncoding, Source.element, Source.bytes_readerBytes] using hh
    · have he := congrArg Source.readerBytes eq
      rw [Source.readerBytes_bytes] at he
      exact he.trans List.map_append
  · rintro ⟨ex, header, init, hh, hi, rfl⟩
    exact ⟨ex, Source.bytes header, Source.bytes init, hh, VecEncoding.source_map hi, List.map_append⟩

theorem ElementHeaderEncoding.nonempty {m t ex bs} (h : ElementHeaderEncoding m t ex bs) : 0 < bs.length := by
  simpa only [Source.bytes, List.length_map] using WebAssembly.Binary.ElementHeaderEncoding.nonempty h

theorem element_encoding_prefix_unique : PrefixUnique ElementEncoding :=
  PrefixUnique.of_source WebAssembly.Binary.ElementEncoding.prefix_unique Source.elementInjective

theorem DataEncoding.length_ge_two {e bs} (h : DataEncoding e bs) : 2 ≤ bs.length := by
  simpa only [Source.bytes, List.length_map] using WebAssembly.Binary.DataEncoding.length_ge_two h

theorem DataEncoding.init_length_lt {e bs} (h : DataEncoding e bs) : e.init.length < 2^32 := by
  obtain ⟨_, count, _, hc, _, _⟩ := WebAssembly.Binary.DataEncoding.init_vector h
  simpa only [Source.dataEntry, Source.bytes, List.length_map] using (Source.readerLeb hc).value_lt

theorem data_encoding_prefix_unique : PrefixUnique DataEncoding :=
  PrefixUnique.of_source WebAssembly.Binary.DataEncoding.prefix_unique Source.dataEntryInjective

end Itasca.Binary

end

end
