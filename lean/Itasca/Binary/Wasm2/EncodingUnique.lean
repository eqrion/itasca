import Itasca.Binary.Wasm2.References
import Itasca.Binary.Wasm2.Bulk
import Itasca.Binary.PrefixUnique
import Itasca.Binary.Wasm2.Encoding
import Itasca.Binary.Wasm2.EncodingComplete
import Itasca.Binary.Wasm2.SyntaxUnique
import Itasca.Binary.Wasm2.Simd
import Itasca.Binary.Wasm1.PrefixUnique

/-!
# Uniqueness of Wasm 2.0 instruction decoding

Prefix uniqueness of the Wasm 2.0 immediates (`Immediate.prefix_unique`), including reference,
bulk memory and block type immediates, and of tokens (`token_prefix_unique`). It gives `At.unique`
for one token, `Consumed.unique` for a token sequence and `BodyEncoding.unique` for a complete
body, as in `Binary/Wasm1/PrefixUnique` and `Binary/Wasm1/EncodingUnique`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

open ModuleBinary

/-- Reference instruction immediates are prefix-unique. -/
theorem ReferencesBinary.Immediate.prefix_unique (opcode : U8) :
    PrefixUnique (ReferencesBinary.Immediate opcode) := by
  intro x y a b rest tail hx hy he
  cases hx <;> cases hy
  case refNull.refNull =>
    rename_i x y
    obtain ⟨hv, rfl⟩ := List.cons.inj he
    have heq : x = y := by cases x <;> cases y <;> simp_all [ReferencesBinary.referenceByte]
    subst y
    exact ⟨rfl, rfl, rfl⟩
  case refIsNull.refIsNull => exact ⟨rfl, rfl, he⟩
  case refFunc.refFunc | tableGet.tableGet | tableSet.tableSet =>
    rename_i x hx y hy
    obtain ⟨hv, rfl, rfl⟩ := leb_prefix_unique hx hy he
    obtain rfl := UScalar.eq_of_val_eq hv
    exact ⟨rfl, rfl, rfl⟩
  case selectTyped.selectTyped =>
    rename_i x count hx y count' hy
    obtain ⟨_, rfl, hrest⟩ := leb_prefix_unique hx hy (by simpa [List.append_assoc] using he)
    obtain ⟨hv, rfl⟩ := List.cons.inj hrest
    obtain rfl := valueByte_injective hv
    exact ⟨rfl, rfl, rfl⟩
  case callIndirect.callIndirect =>
    rename_i tx ix tbs ibs ht hi ty iy tbs' ibs' ht' hi'
    obtain ⟨hv, rfl, hrest⟩ := leb_prefix_unique ht ht' (by simpa [List.append_assoc] using he)
    obtain ⟨hv', rfl, rfl⟩ := leb_prefix_unique hi hi' hrest
    obtain rfl := UScalar.eq_of_val_eq hv
    obtain rfl := UScalar.eq_of_val_eq hv'
    exact ⟨rfl, rfl, rfl⟩

/-- Bulk instruction immediates are prefix-unique. -/
theorem BulkBinary.Immediate.prefix_unique (opcode : U32) :
    PrefixUnique (BulkBinary.Immediate opcode) := by
  intro x y a b rest tail hx hy he
  cases hx <;> cases hy
  case memoryInit.memoryInit =>
    rename_i x bs hx y bs' hy
    obtain ⟨hv, rfl, hrest⟩ := leb_prefix_unique hx hy (by simpa [List.append_assoc] using he)
    obtain rfl := UScalar.eq_of_val_eq hv
    exact ⟨rfl, rfl, (List.cons.inj hrest).2⟩
  case dataDrop.dataDrop | elemDrop.elemDrop | tableGrow.tableGrow |
      tableSize.tableSize | tableFill.tableFill =>
    rename_i x hx y hy
    obtain ⟨hv, rfl, rfl⟩ := leb_prefix_unique hx hy he
    obtain rfl := UScalar.eq_of_val_eq hv
    exact ⟨rfl, rfl, rfl⟩
  case memoryCopy.memoryCopy => exact ⟨rfl, rfl, (List.cons.inj (List.cons.inj he).2).2⟩
  case memoryFill.memoryFill => exact ⟨rfl, rfl, (List.cons.inj he).2⟩
  case tableInit.tableInit | tableCopy.tableCopy =>
    rename_i ax bx abs bbs ha hb ay by_ abs' bbs' ha' hb'
    obtain ⟨hv, rfl, hrest⟩ := leb_prefix_unique ha ha' (by simpa [List.append_assoc] using he)
    obtain ⟨hv', rfl, rfl⟩ := leb_prefix_unique hb hb' hrest
    obtain rfl := UScalar.eq_of_val_eq hv
    obtain rfl := UScalar.eq_of_val_eq hv'
    exact ⟨rfl, rfl, rfl⟩

end Itasca.Wasm2

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

open ModuleBinary

private theorem indexed_prefix_not_negative {index : U32} {bytes rest tail : List U8} {tag : U8}
    (h : SignedLeb33.Encoding bytes index.val) (he : bytes ++ rest = tag :: tail)
    (hlo : 64 ≤ tag.val) (hhi : tag.val < 128) : False := by
  obtain ⟨before, last, rfl, _, hbefore, _, hv, _⟩ := h
  cases before with
  | nil =>
    have hhead := (List.cons.inj he).1
    subst last
    simp [SignedLeb.finalValue, Leb128.payload, hlo] at hv
    omega
  | cons b bs =>
    have hhead := (List.cons.inj he).1
    have hb := hbefore b (by simp)
    rw [hhead] at hb
    omega

/-- Block type encodings are prefix-unique: a tag byte cannot start a nonnegative signed 33-bit
index. -/
theorem BlockEncoding.prefix_unique : PrefixUnique BlockEncoding := by
  intro x y a b rest tail hx hy he
  cases x <;> cases y
  all_goals simp only [BlockEncoding] at hx hy
  case Empty.Empty =>
    subst a; subst b
    exact ⟨rfl, rfl, (List.cons.inj he).2⟩
  case Empty.Value t | Value.Empty t =>
    subst a; subst b
    have hh := (List.cons.inj he).1
    cases t <;> contradiction
  case Value.Value t u =>
    subst a; subst b
    obtain ⟨hv, rfl⟩ := List.cons.inj he
    obtain rfl := valueByte_injective hv
    exact ⟨rfl, rfl, rfl⟩
  case Empty.TypeIndex i =>
    subst a
    exact False.elim (indexed_prefix_not_negative hy he.symm (by decide) (by decide))
  case Value.TypeIndex t i =>
    subst a
    exact False.elim (indexed_prefix_not_negative hy he.symm (valueByte_negative t).1 (valueByte_negative t).2)
  case TypeIndex.Empty i =>
    subst b
    exact False.elim (indexed_prefix_not_negative hx he (by decide) (by decide))
  case TypeIndex.Value i t =>
    subst b
    exact False.elim (indexed_prefix_not_negative hx he (valueByte_negative t).1 (valueByte_negative t).2)
  case TypeIndex.TypeIndex i j =>
    obtain ⟨rfl, hv⟩ := SignedLeb33.Encoding.prefix_unique hx hy he
    have hv' : i = j := UScalar.eq_of_val_eq (by omega)
    subst j
    exact ⟨rfl, rfl, List.append_cancel_left he⟩

private theorem plain_opcode {opcode op bytes} (h : Wasm1.Immediate opcode (.plain op) bytes) :
    opcode.val < 192 ∧ opcode.val ∉ [2, 3, 4, 5, 11, 28, 37, 38, 208, 209, 210, 252, 253] := by
  cases h with
  | numeric opcode operation hmap =>
    have := Numeric.NumericOp.bounds hmap
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    omega
  | memory opcode operation arg hmap ha ho =>
    unfold MemoryMeaning.opcodeMeaning at hmap
    split at hmap <;> simp_all
  | _ => decide

private theorem sign_range {opcode op} (h : NumericExtensions.signMeaning opcode = some op) :
    192 ≤ opcode.val ∧ opcode.val ≤ 196 := by
  unfold NumericExtensions.signMeaning at h
  split at h <;> simp_all

private theorem saturating_range {opcode op} (h : NumericExtensions.saturatingMeaning opcode = some op) :
    opcode.val < 8 := by
  unfold NumericExtensions.saturatingMeaning at h
  split at h <;> simp_all

private theorem reference_opcodes {opcode op bytes} (h : ReferencesBinary.Immediate opcode op bytes) :
    opcode.val ∈ [17, 28, 37, 38, 208, 209, 210] := by
  cases h <;> decide

private theorem plain_reference_prefix {opcode x y a b rest tail}
    (hx : Wasm1.Immediate opcode (.plain x) a) (hy : ReferencesBinary.Immediate opcode y b)
    (he : a ++ rest = b ++ tail) : x = y ∧ a = b ∧ rest = tail := by
  have hop := plain_opcode hx
  have hyr := reference_opcodes hy
  have ho : opcode = 17#u8 := by
    apply UScalar.eq_of_val_eq
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hop hyr
    change opcode.val = 17
    omega
  subst opcode
  cases hx <;> cases hy
  all_goals try contradiction
  case callIndirect.callIndirect =>
    rename_i idx ibs hi tid tab tbs tabs ht htab
    obtain ⟨hv, rfl, hrest⟩ := leb_prefix_unique hi ht (by simpa [List.append_assoc] using he)
    have hz : Leb128.Encoding [0#u8] 0 :=
      ⟨[], 0#u8, rfl, by decide, by simp, by decide, by simp, rfl⟩
    obtain ⟨hv', hbs, htail⟩ := leb_prefix_unique hz htab hrest
    have htid : idx = tid := UScalar.eq_of_val_eq hv
    subst tid
    refine ⟨?_, by rw [hbs], htail⟩
    simp only [← hv']

set_option maxHeartbeats 2000000 in
/-- The immediate bytes of a Wasm 2.0 token are determined by its opcode and leading bytes. -/
theorem Immediate.prefix_unique (opcode : U8) : PrefixUnique (Immediate opcode) := by
  intro x y a b rest tail hx hy he
  cases hx <;> cases hy
  all_goals try { exact ⟨rfl, rfl, he⟩ }
  all_goals try { have hb := plain_opcode (by assumption); norm_num at hb }
  all_goals try { have hb := sign_range (by assumption); norm_num at hb }
  all_goals try { have hb := reference_opcodes (by assumption); norm_num at hb }
  case plain.plain =>
    rename_i op hp op' hp'
    obtain ⟨hh, rfl, rfl⟩ := Wasm1.Immediate.prefix_unique opcode hp hp' he
    exact ⟨congrArg Token.plain (Wasm1.Token.plain.inj hh), rfl, rfl⟩
  case plain.reference =>
    rename_i op hp op' hp'
    obtain ⟨rfl, rfl, rfl⟩ := plain_reference_prefix hp hp' he
    exact ⟨rfl, rfl, rfl⟩
  case reference.plain =>
    rename_i op hp op' hp'
    obtain ⟨rfl, rfl, rfl⟩ := plain_reference_prefix hp' hp he.symm
    exact ⟨rfl, rfl, rfl⟩
  case signExtension.signExtension =>
    rename_i op hp op' hp'
    obtain rfl := Option.some.inj (hp.symm.trans hp')
    exact ⟨rfl, rfl, he⟩
  case reference.reference =>
    rename_i op hp op' hp'
    obtain ⟨rfl, rfl, rfl⟩ := ReferencesBinary.Immediate.prefix_unique opcode hp hp' he
    exact ⟨rfl, rfl, rfl⟩
  case saturating.saturating =>
    rename_i sub op hmap hb sub' op' hmap' hb'
    obtain ⟨hv, rfl, rfl⟩ := leb_prefix_unique hb hb' he
    obtain rfl := UScalar.eq_of_val_eq hv
    obtain rfl := Option.some.inj (hmap.symm.trans hmap')
    exact ⟨rfl, rfl, rfl⟩
  case saturating.bulk =>
    rename_i sub op hmap hb sub' pbs op' bs hb' hi
    have hr := saturating_range hmap
    have hr' := hi.subopcode_range
    obtain ⟨hv, _, _⟩ := leb_prefix_unique hb hb' (by simpa [List.append_assoc] using he)
    omega
  case bulk.saturating =>
    rename_i sub pbs op bs hb hi sub' op' hmap hb'
    have hr := saturating_range hmap
    have hr' := hi.subopcode_range
    obtain ⟨hv, _, _⟩ := leb_prefix_unique hb hb' (by simpa [List.append_assoc] using he)
    omega
  case bulk.bulk | simd.simd =>
    rename_i sub pbs op bs hb hi sub' pbs' op' bs' hb' hi'
    obtain ⟨hv, rfl, hrest⟩ := leb_prefix_unique hb hb' (by simpa [List.append_assoc] using he)
    obtain rfl := UScalar.eq_of_val_eq hv
    obtain ⟨rfl, rfl, rfl⟩ := (by first
      | exact BulkBinary.Immediate.prefix_unique sub hi hi' hrest
      | exact Simd.Immediate.prefix_unique sub hi hi' hrest)
    exact ⟨rfl, rfl, rfl⟩
  case block.block | loop.loop | if_.if_ =>
    rename_i bt hb bt' hb'
    obtain ⟨rfl, rfl, rfl⟩ := BlockEncoding.prefix_unique hb hb' he
    exact ⟨rfl, rfl, rfl⟩
  all_goals
    first
      | (have hp := plain_opcode (by assumption); have hs := sign_range (by assumption); omega)
      | (have hr := reference_opcodes (by assumption); have hs := sign_range (by assumption)
         simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; omega)

/-- Token encodings are prefix-unique. -/
theorem token_prefix_unique : PrefixUnique TokenEncoding := by
  rintro x y a b rest tail ⟨op, ai, rfl, hx⟩ ⟨op', bi, rfl, hy⟩ he
  obtain ⟨rfl, htail⟩ := List.cons.inj he
  obtain ⟨rfl, rfl, rfl⟩ := Immediate.prefix_unique op hx hy htail
  exact ⟨rfl, rfl, rfl⟩

/-- A byte string is the encoding of at most one token sequence. -/
theorem tokens_unique : Unique (Rep TokenEncoding) :=
  token_prefix_unique.rep_unique (by rintro _ _ ⟨op, immediate, rfl, _⟩; simp)

/-- The token read at a cursor and its end cursor are determined by `data` and `start`. -/
theorem At.unique {data start t u next last}
    (ht : At data start t next) (hu : At data start u last) : t = u ∧ next = last := by
  obtain ⟨bs, ht, hb⟩ := ht
  obtain ⟨cs, hu, hc⟩ := hu
  obtain ⟨rfl, rfl, _⟩ := token_prefix_unique ht hu (hb.suffix.symm.trans hc.suffix)
  exact ⟨rfl, UScalar.eq_of_val_eq (hb.length.trans hc.length.symm)⟩

/-- A consumed span that ends where it starts has no tokens. -/
theorem Consumed.nil_of_equal_cursor {data start tokens next}
    (h : Consumed data start tokens next) (hp : start = next) : tokens = [] := by
  cases h with
  | nil => rfl
  | snoc hs ht => have := hs.span; have := ht.span; subst next; omega

/-- Two consumed spans over the same interval have the same tokens. -/
theorem Consumed.unique {data start xs ys next}
    (hx : Consumed data start xs next) (hy : Consumed data start ys next) : xs = ys := by
  induction xs generalizing start ys with
  | nil =>
    have hn := hx.empty_eq rfl
    exact (hy.nil_of_equal_cursor hn.symm).symm
  | cons x xs ih =>
    obtain ⟨p, hp, hxs⟩ := Consumed.cons_iff.mp hx
    cases ys with
    | nil =>
      have hn := hy.empty_eq rfl
      have := hp.span
      have := hxs.span
      subst next
      omega
    | cons y ys =>
      obtain ⟨q, hq, hys⟩ := Consumed.cons_iff.mp hy
      obtain ⟨rfl, rfl⟩ := hp.unique hq
      rw [ih hxs hys]

/-- A complete body encoding determines one instruction tree, regardless of typing. -/
theorem BodyEncoding.unique {data xs ys}
    (hx : BodyEncoding data xs) (hy : BodyEncoding data ys) : xs = ys := by
  obtain ⟨xt, xp, hx, hxp, hxs⟩ := hx
  obtain ⟨yt, yp, hy, hyp, hys⟩ := hy
  have hp : xp = yp := UScalar.eq_of_val_eq (hxp.trans hyp.symm)
  subst yp
  have ht := hx.unique hy
  subst yt
  exact hxs.unique hys

end Itasca.Wasm2
