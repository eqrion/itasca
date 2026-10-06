import Itasca.WasmBinaryComplete
import Itasca.BrTableComplete
import Itasca.AllNumeric

open Aeneas Aeneas.Std

namespace Itasca

theorem Leb128.Decoded.unique {data start x y next last}
    (hx : Leb128.Decoded data start x next) (hy : Leb128.Decoded data start y last) :
    x = y ∧ next = last := by
  have h := (reader.read_u32_leb.complete data start x next hx).symm.trans
    (reader.read_u32_leb.complete data start y last hy)
  simpa using h

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

theorem BrTable.Decoded.unique {data start xs ys x y next last}
    (hx : BrTable.Decoded data start xs x next) (hy : BrTable.Decoded data start ys y last) :
    xs = ys ∧ x = y ∧ next = last := by
  obtain ⟨n, p, q, hn, hlen, hs, ht⟩ := hx
  obtain ⟨m, r, s, hm, hlen', hs', ht'⟩ := hy
  obtain ⟨rfl, rfl⟩ := hn.unique hm
  obtain ⟨rfl, rfl⟩ := hs.unique hs' (hlen.trans hlen'.symm)
  exact ⟨rfl, ht.unique ht'⟩

end Itasca

namespace Itasca.Wasm

private theorem memory_numeric_disjoint (opcode : U8) (m : MemoryMeaning.Operation)
    (n : Numeric.Operation) (hm : MemoryMeaning.opcodeMeaning opcode = some m)
    (hn : Numeric.opcodeMeaning opcode = some n) : False := by
  have hb := Numeric.NumericOp.bounds hn
  unfold MemoryMeaning.opcodeMeaning at hm
  split at hm <;> (first | contradiction | omega)

set_option maxHeartbeats 1200000 in
theorem Immediate.unique {data start opcode t u bs cs next last}
    (ht : Immediate opcode t bs) (hu : Immediate opcode u cs)
    (hb : BytesAt data start bs next) (hc : BytesAt data start cs last) :
    t = u ∧ next = last := by
  cases ht <;> cases hu
  all_goals try { contradiction }
  all_goals try { exact ⟨rfl, hb.empty.trans hc.empty.symm⟩ }
  case block.block | loop.loop | if_.if_ =>
    have he := (hb.read_block_type _).symm.trans (hc.read_block_type _)
    simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨rfl, rfl⟩
  case br.br | brIf.brIf | call.call | localGet.localGet | localSet.localSet |
      localTee.localTee | globalGet.globalGet | globalSet.globalSet =>
    rename_i x hx y hy
    have he := (hb.read_u32 x hx).symm.trans (hc.read_u32 y hy)
    simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨rfl, rfl⟩
  case brTable.brTable =>
    rename_i xs x count entries final hn he hf ys y count' entries' final' hn' he' hf'
    obtain ⟨rfl, rfl, rfl⟩ := (hb.br_table_decoded xs x hn he hf).unique
      (hc.br_table_decoded ys y hn' he' hf')
    exact ⟨rfl, rfl⟩
  case callIndirect.callIndirect =>
    rename_i x bytes hx y bytes' hy
    obtain ⟨p, hp, hzero, _⟩ := hb.index_zero x hx
    obtain ⟨q, hq, hzero', _⟩ := hc.index_zero y hy
    have he := hp.symm.trans hq
    simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have he := hzero.symm.trans hzero'
    simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq, true_and] at he
    exact ⟨rfl, he⟩
  case memory.memory =>
    rename_i m a align offset ha ho hm n b align' offset' ha' ho' hn
    have he : m = n := Option.some.inj (hm.symm.trans hn)
    subst n
    let st : code.OpIterState := { vals := alloc.vec.Vec.new _, ctrls := alloc.vec.Vec.new _, pos := start }
    have he := (hb.read_memarg st a ha ho).symm.trans (hc.read_memarg st b ha' ho')
    simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at he
    have hp : next = last := congrArg code.OpIterState.pos he.2
    obtain ⟨rfl, _⟩ := he
    exact ⟨rfl, hp⟩
  case memory.numeric =>
    rename_i m a align offset ha ho hm n hn
    exact False.elim (memory_numeric_disjoint opcode m n hm hn)
  case numeric.memory =>
    rename_i n hn m a align offset ha ho hm
    exact False.elim (memory_numeric_disjoint opcode m n hm hn)
  case numeric.numeric =>
    rename_i m hm n hn
    have he : m = n := Option.some.inj (hm.symm.trans hn)
    subst n
    exact ⟨rfl, hb.empty.trans hc.empty.symm⟩
  case memorySize.memorySize | memoryGrow.memoryGrow =>
    exact ⟨rfl, UScalar.eq_of_val_eq (hb.length.trans hc.length.symm)⟩
  case i32Const.i32Const =>
    rename_i x hx y hy
    have he := (hb.read_s32 x hx).symm.trans (hc.read_s32 y hy)
    simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨rfl, rfl⟩
  case i64Const.i64Const =>
    rename_i x hx y hy
    have he := (hb.read_s64 x hx).symm.trans (hc.read_s64 y hy)
    simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨rfl, rfl⟩
  case f32Const.f32Const =>
    rename_i x hx y hy
    have he := (hb.read_f32 x hx).symm.trans (hc.read_f32 y hy)
    simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨rfl, rfl⟩
  case f64Const.f64Const =>
    rename_i x hx y hy
    have he := (hb.read_f64 x hx).symm.trans (hc.read_f64 y hy)
    simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨rfl, rfl⟩

/-- The independent binary relation determines both its token and end cursor. -/
theorem At.unique {data start t u next last}
    (ht : At data start t next) (hu : At data start u last) : t = u ∧ next = last := by
  let st := { Body.initial .Empty with pos := start }
  obtain ⟨op, p, bs, hr, _, hi, hb⟩ := ht.read_op st rfl
  obtain ⟨op', q, cs, hr', _, hj, hc⟩ := hu.read_op st rfl
  have he := hr.symm.trans hr'
  simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at he
  have hp : p = q := congrArg code.OpIterState.pos he.2
  obtain ⟨rfl, _⟩ := he
  subst q
  exact hi.unique hj hb hc

theorem Consumed.nil_of_equal_cursor {data start tokens next}
    (h : Consumed data start tokens next) (hp : start = next) : tokens = [] := by
  cases h with
  | nil => rfl
  | snoc hs ht => have := hs.span; have := ht.span; subst next; omega

/-- Two complete parses of the same byte interval have the same flat tokens. -/
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

end Itasca.Wasm
