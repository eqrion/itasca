import Itasca.Binary.PrefixUnique
import Itasca.Binary.Wasm1.SyntaxUnique
import Itasca.Binary.Wasm1.Encoding

open Aeneas Aeneas.Std

namespace Itasca.Wasm1

open ModuleBinary

private theorem blockByte_injective : Function.Injective Control.blockByte := by
  intro a b h
  cases a <;> cases b
  all_goals first
    | rfl
    | rename_i x y; cases x <;> cases y <;> simp_all [Control.blockByte]
    | rename_i x; cases x <;> simp_all [Control.blockByte]

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
theorem Immediate.prefix_unique (opcode : U8) : PrefixUnique (Immediate opcode) := by
  intro t u bs cs rest tail ht hu heq
  cases ht <;> cases hu
  all_goals try { contradiction }
  all_goals try { exact ⟨rfl, rfl, heq⟩ }
  case block.block | loop.loop | if_.if_ =>
    obtain ⟨hbt, rfl⟩ := List.cons.inj heq
    obtain rfl := blockByte_injective hbt
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

theorem token_prefix_unique : PrefixUnique TokenEncoding := by
  rintro x y a b rest tail ⟨op, ai, rfl, hx⟩ ⟨op', bi, rfl, hy⟩ he
  obtain ⟨rfl, htail⟩ := List.cons.inj he
  obtain ⟨rfl, rfl, rfl⟩ := Immediate.prefix_unique op hx hy htail
  exact ⟨rfl, rfl, rfl⟩

theorem tokens_unique : Unique (Rep TokenEncoding) :=
  token_prefix_unique.rep_unique (by rintro _ _ ⟨op, immediate, rfl, _⟩; simp)

end Itasca.Wasm1

namespace Itasca.ModuleBinary

/-- Raw body lists have unique trees even when they exceed implementation or
host-size bounds. Neither encoding needs to be well typed. -/
theorem BodyEncoding.unique : Unique BodyEncoding := by
  rintro xs ys bytes ⟨xt, hx, hxs⟩ ⟨yt, hy, hys⟩
  obtain rfl := Wasm1.tokens_unique hx hy
  exact hxs.unique hys

end Itasca.ModuleBinary
