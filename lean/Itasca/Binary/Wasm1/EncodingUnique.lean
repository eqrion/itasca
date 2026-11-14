import Itasca.Binary.UnicodeUnique
import Itasca.Binary.Wasm2.SyntaxUnique
import Itasca.Binary.Wasm1.EncodingComplete

/-!
Sections, each formerly its own module: PrefixUnique, EncodingUnique.
-/

/-! ## PrefixUnique -/

section

/-!
# Prefix uniqueness of Wasm 1.0 tokens

`Immediate.prefix_unique` and `token_prefix_unique` show that a Wasm 1.0 token and its encoding
are determined by the leading bytes, and `tokens_unique` extends this to token sequences,
independent of typing and implementation limits.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm1

open ModuleBinary

/-- An index vector is a sequence of `IndexEncoding`s. -/
theorem IndicesEncoding.rep {indices bytes} (h : IndicesEncoding indices bytes) :
    Rep IndexEncoding indices bytes := by
  induction h with
  | nil => exact .nil
  | cons hn _ ih => exact .cons hn ih

private theorem memory_numeric_disjoint (opcode : U8) (m : MemoryMeaning.Operation)
    (n : Numeric.Operation) (hm : MemoryMeaning.opcodeMeaning opcode = some m)
    (hn : Numeric.opcodeMeaning opcode = some n) : False := by
  have hb := Numeric.NumericOp.bounds hn
  unfold MemoryMeaning.opcodeMeaning at hm
  split at hm <;> (first | contradiction | omega)

set_option maxHeartbeats 1200000 in
/-- The immediate bytes of a token are determined by its opcode and leading bytes. -/
theorem Immediate.prefix_unique (opcode : U8) : PrefixUnique (Immediate opcode) := by
  intro t u bs cs rest tail ht hu heq
  cases ht <;> cases hu
  all_goals try { contradiction }
  all_goals try { exact ⟨rfl, rfl, heq⟩ }
  case block.block | loop.loop | if_.if_ =>
    rename_i _ _ hx _ _ hy
    obtain ⟨hbt, rfl⟩ := List.cons.inj heq
    obtain ⟨rfl, rfl⟩ := hx.unique hy (.inl hbt)
    exact ⟨rfl, rfl, rfl⟩
  case br.br | brIf.brIf | call.call | localGet.localGet | localSet.localSet |
      localTee.localTee | globalGet.globalGet | globalSet.globalSet =>
    rename_i x hx y hy
    obtain ⟨hv, rfl, rfl⟩ := leb_prefix_unique hx hy heq
    obtain rfl := UScalar.eq_of_val_eq hv
    exact ⟨rfl, rfl, rfl⟩
  case brTable.brTable =>
    rename_i xs x count entries final hn he hf ys y count' entries' final' hn' he' hf'
    obtain ⟨hl, rfl, hrest⟩ := leb_prefix_unique hn hn' (by simpa [List.append_assoc] using heq)
    obtain ⟨rfl, rfl, hentries⟩ := index_prefix_unique.rep he.rep he'.rep hl
      (by simpa [List.append_assoc] using hrest)
    obtain ⟨rfl, rfl, rfl⟩ := index_prefix_unique hf hf' hentries
    exact ⟨rfl, rfl, rfl⟩
  case callIndirect.callIndirect =>
    rename_i x bytes hx y bytes' hy
    obtain ⟨rfl, rfl, hrest⟩ := index_prefix_unique hx hy (by simpa [List.append_assoc] using heq)
    obtain rfl := (List.cons.inj hrest).2
    exact ⟨rfl, rfl, rfl⟩
  case memory.memory =>
    rename_i m a align offset ha ho hm n b align' offset' ha' ho' hn
    obtain rfl := Option.some.inj (hm.symm.trans hn)
    obtain ⟨haeq, rfl, hrest⟩ := leb_prefix_unique ha ha' (by simpa [List.append_assoc] using heq)
    obtain ⟨hoeq, rfl, rfl⟩ := leb_prefix_unique ho ho' hrest
    have haeq := UScalar.eq_of_val_eq haeq
    have hoeq := UScalar.eq_of_val_eq hoeq
    have hab : a = b := by cases a; cases b; simp_all
    subst b
    exact ⟨rfl, rfl, rfl⟩
  case memory.numeric =>
    rename_i m a align offset ha ho hm n hn
    exact False.elim (memory_numeric_disjoint opcode m n hm hn)
  case numeric.memory =>
    rename_i n hn m a align offset ha ho hm
    exact False.elim (memory_numeric_disjoint opcode m n hm hn)
  case numeric.numeric =>
    rename_i m hm n hn
    obtain rfl := Option.some.inj (hm.symm.trans hn)
    exact ⟨rfl, rfl, heq⟩
  case memorySize.memorySize | memoryGrow.memoryGrow =>
    exact ⟨rfl, rfl, (List.cons.inj heq).2⟩
  case i32Const.i32Const =>
    rename_i x hx y hy
    obtain ⟨hv, rfl, rfl⟩ := signed32_prefix_unique hx hy heq
    obtain rfl := IScalar.eq_of_val_eq hv
    exact ⟨rfl, rfl, rfl⟩
  case i64Const.i64Const =>
    rename_i x hx y hy
    obtain ⟨hv, rfl, rfl⟩ := signed64_prefix_unique hx hy heq
    obtain rfl := IScalar.eq_of_val_eq hv
    exact ⟨rfl, rfl, rfl⟩
  case f32Const.f32Const =>
    rename_i x hx y hy
    obtain ⟨hv, rfl, rfl⟩ := float_prefix_unique 4 hx hy heq
    obtain rfl := UScalar.eq_of_val_eq hv
    exact ⟨rfl, rfl, rfl⟩
  case f64Const.f64Const =>
    rename_i x hx y hy
    obtain ⟨hv, rfl, rfl⟩ := float_prefix_unique 8 hx hy heq
    obtain rfl := UScalar.eq_of_val_eq hv
    exact ⟨rfl, rfl, rfl⟩

/-- Token encodings are prefix-unique. -/
theorem token_prefix_unique : PrefixUnique TokenEncoding := by
  rintro x y a b rest tail ⟨op, ai, rfl, hx⟩ ⟨op', bi, rfl, hy⟩ he
  obtain ⟨rfl, htail⟩ := List.cons.inj he
  obtain ⟨rfl, rfl, rfl⟩ := Immediate.prefix_unique op hx hy htail
  exact ⟨rfl, rfl, rfl⟩

/-- A byte string is the encoding of at most one token sequence. -/
theorem tokens_unique : Unique (Rep TokenEncoding) :=
  token_prefix_unique.rep_unique (by rintro _ _ ⟨op, immediate, rfl, _⟩; simp)

end Itasca.Wasm1

end

/-! ## EncodingUnique -/

section

/-!
# Uniqueness of Wasm 1.0 decoding at a cursor

Shows that LEB128 indices and `br_table` label vectors determine their decoded values
(`Leb128.Decoded.unique`, `BrTable.LabelsDecoded.unique`, `BrTable.Decoded.unique`).
-/

open Aeneas Aeneas.Std

namespace Itasca

/-- A decoded unsigned LEB128 value and cursor are determined by the start. -/
theorem Leb128.Decoded.unique {data start x y next last}
    (hx : Leb128.Decoded data start x next) (hy : Leb128.Decoded data start y last) :
    x = y ∧ next = last :=
  Leb128.Decoded.deterministic data start x y next last hx hy

/-- A label run of known length is determined by the start. -/
theorem BrTable.LabelsDecoded.unique {data start xs ys next last}
    (hx : BrTable.LabelsDecoded data start xs next)
    (hy : BrTable.LabelsDecoded data start ys last) (hlen : xs.length = ys.length) :
    xs = ys ∧ next = last := by
  have empty : ∀ {p q}, BrTable.LabelsDecoded data p [] q → q = p := by
    intro p q h
    generalize he : [] = zs at h
    cases h with
    | nil => rfl
    | snoc => simp at he
  induction xs generalizing start ys with
  | nil =>
      have he : ys = [] := List.length_eq_zero_iff.mp (by simpa using hlen.symm)
      subst ys
      exact ⟨rfl, (empty hx).trans (empty hy).symm⟩
  | cons x xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          obtain ⟨p, hxp, hxs⟩ := BrTable.LabelsDecoded.cons_iff.mp hx
          obtain ⟨q, hyq, hys⟩ := BrTable.LabelsDecoded.cons_iff.mp hy
          obtain ⟨rfl, rfl⟩ := hxp.unique hyq
          obtain ⟨rfl, rfl⟩ := ih hxs hys (by simpa using hlen)
          exact ⟨rfl, rfl⟩

/-- A decoded `br_table` immediate is determined by the start. -/
theorem BrTable.Decoded.unique {data start xs ys x y next last}
    (hx : BrTable.Decoded data start xs x next) (hy : BrTable.Decoded data start ys y last) :
    xs = ys ∧ x = y ∧ next = last := by
  obtain ⟨n, p, q, hn, hlen, hs, ht⟩ := hx
  obtain ⟨m, r, s, hm, hlen', hs', ht'⟩ := hy
  obtain ⟨rfl, rfl⟩ := hn.unique hm
  obtain ⟨rfl, rfl⟩ := hs.unique hs' (hlen.trans hlen'.symm)
  exact ⟨rfl, ht.unique ht'⟩

end Itasca

namespace Itasca.Wasm1

end Itasca.Wasm1

end
