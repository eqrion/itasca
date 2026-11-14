import Itasca.Wasm2.Simd.LaneReaders
import Itasca.Binary.Wasm1.DeclaredReferences
import Itasca.Binary.Wasm2.SyntaxUnique
import Itasca.Visitor.RunTrace

/-!
Sections, each formerly its own module: MemoryReaders, Shuffle, Visitor.
-/

/-! ## MemoryReaders -/

section

/-!
# Constant and memory reader factorization

Factors the extracted `code.read_simd_const`, `code.read_load`/`code.read_store` at `v128` and
`code.read_simd_memory_lane` into a decode followed by `carryFixed` (`const_fixed`,
`full_memory_fixed`, `memory_lane_fixed`). `MemoryOperation.conditions` and
`MemoryOperation.typed_runtime` connect the typing of SIMD memory operations to the runtime memory
and alignment checks.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2.Simd

/-- Reads the sixteen immediate bytes of `v128.const` and pushes a `v128`. -/
def constReader (st : code.OpIterState) (data : Slice U8) :
    Result (core.result.Result (U64 × U64) error.OpError × code.OpIterState) := do
  let (r, s) ← code.take_simd_bits st data
  match r with
  | .Err e => .ok (.Err e, s)
  | .Ok bits => carryFixed bits s [] (some .V128)

theorem const_fixed (st : code.OpIterState) (data : Slice U8) :
    code.read_simd_const st data = constReader st data := by
  simp only [code.read_simd_const, constReader]
  congr 1
  funext pair
  obtain ⟨r, s⟩ := pair
  cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    carryFixed, readFixed, Std.bind_assoc]

/-- Operand types of a full-width `v128` load (an address) or store (a vector and an address). -/
def fullMemoryInputs (store : Bool) : List wasm_types.ValueType :=
  if store then [.V128, .I32] else [.I32]

/-- Result type of a `v128` memory operation: nothing for stores, a vector otherwise. -/
def memoryOutput (store : Bool) : Option wasm_types.ValueType :=
  if store then none else some .V128

/-- Reads a memory argument, checks that memory zero exists and the alignment bound, then applies
the operand effect of a full-width `v128` load or store. -/
def fullMemoryReader (st : code.OpIterState) (data : Slice U8) (env : metadata.Env)
    (align : U32) (store : Bool) :
    Result (core.result.Result code.MemArg error.OpError × code.OpIterState) := do
  let (r, s) ← code.read_memarg st data
  match r with
  | .Err e => .ok (.Err e, s)
  | .Ok arg =>
    let r ← code.check_memory_and_alignment env arg align
    match r with
    | .Err e => .ok (.Err e, s)
    | .Ok _ => carryFixed arg s (fullMemoryInputs store) (memoryOutput store)

theorem full_memory_fixed (st : code.OpIterState) (data : Slice U8) (env : metadata.Env)
    (align : U32) (store : Bool) :
    (if store then code.read_store st data env .V128 align else code.read_load st data env .V128 align) =
      fullMemoryReader st data env align store := by
  cases store <;> simp only [Bool.false_eq_true, if_true, if_false,
    code.read_store, code.read_load, fullMemoryReader, fullMemoryInputs, memoryOutput]
  all_goals congr 1
  all_goals funext pair
  all_goals obtain ⟨r, s⟩ := pair
  all_goals cases r with
    | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok arg =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Std.uncurry]
      congr 1
      funext r
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok u =>
        simp only [bind_ok, carryFixed, readFixed, Std.bind_assoc, Std.uncurry]
        repeat' first
          | rfl
          | (congr 1
             funext pair
             obtain ⟨res, state⟩ := pair
             cases res <;> simp [
               core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
               Std.bind_assoc])

/-- Reads a memory argument and a lane index, checks memory and alignment, then applies the
operand effect of a `v128` load or store lane operation. -/
def memoryLaneReader (st : code.OpIterState) (data : Slice U8) (env : metadata.Env)
    (align : U32) (store : Bool) (count : U8) :
    Result (core.result.Result (code.MemArg × U8) error.OpError × code.OpIterState) := do
  let (r, s) ← code.read_memarg st data
  match r with
  | .Err e => .ok (.Err e, s)
  | .Ok arg =>
    let (r, s) ← code.take_simd_lane s data count
    match r with
    | .Err e => .ok (.Err e, s)
    | .Ok lane =>
      let r ← code.check_memory_and_alignment env arg align
      match r with
      | .Err e => .ok (.Err e, s)
      | .Ok _ => carryFixed (arg, lane) s [.V128, .I32] (memoryOutput store)

theorem memory_lane_fixed (st : code.OpIterState) (data : Slice U8) (env : metadata.Env)
    (align : U32) (store : Bool) (count : U8) :
    code.read_simd_memory_lane st data env align store count = memoryLaneReader st data env align store count := by
  simp only [code.read_simd_memory_lane, memoryLaneReader]
  congr 1
  funext pair
  obtain ⟨r, s⟩ := pair
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok arg =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Std.uncurry]
    congr 1
    funext pair
    obtain ⟨r, s⟩ := pair
    cases r with
    | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok lane =>
      simp only [bind_ok, Std.uncurry]
      congr 1
      funext r
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok u =>
        cases store <;> simp only [bind_ok,
          carryFixed, readFixed, memoryOutput, Std.bind_assoc, Std.uncurry,
          Bool.false_eq_true, if_true, if_false]
        all_goals repeat' first
          | rfl
          | (congr 1
             funext pair
             obtain ⟨res, state⟩ := pair
             cases res <;> simp [
               core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
               Std.bind_assoc])

theorem MemoryOperation.inputs_full (op : MemoryOperation) (h : op.laneCount = 0) :
    inputTypes (fullMemoryInputs op.store) = op.inputs := by cases op <;> first | rfl | contradiction

theorem MemoryOperation.inputs_lane (op : MemoryOperation) (h : op.laneCount ≠ 0) :
    inputTypes [.V128, .I32] = op.inputs := by cases op <;> first | rfl | contradiction

theorem MemoryOperation.outputs_pop (op : MemoryOperation) :
    outputTypes (memoryOutput op.store) = op.outputs := by cases op <;> rfl

end Itasca.Wasm2.Simd

open Aeneas Aeneas.Std

namespace Itasca.Wasm2.Simd

theorem MemoryOperation.conditions (op : MemoryOperation) (C : context)
    (arg : code.MemArg) (lane : U8) (ins outs : List valtype)
    (ht : Instr_ok C (op.instruction (MemoryMeaning.memArg arg) (.mk_uN lane.val))
      (.mk_functype (.mk_list ins) (.mk_list outs))) :
    0 < C.MEMS.length ∧ arg.align.val ≤ op.naturalAlign ∧
      (op.laneCount ≠ 0 → lane.val < op.laneCount) := by
  have hp : 0 < C.MEMS.length ∧
      (2 : Rat) ^ arg.align.val ≤ 2 ^ op.naturalAlign ∧
      (op.laneCount ≠ 0 → lane.val < op.laneCount) := by
    cases op <;> simp only [instruction] at ht <;> cases ht
    all_goals refine ⟨by assumption, ?_, ?_⟩
    all_goals norm_num [naturalAlign, laneCount, MemoryMeaning.memArg, proj_uN_0, size] at *
    all_goals norm_cast at *
  exact ⟨hp.1, (pow_le_pow_iff_right₀ (a := (2 : Rat)) (by norm_num)).mp hp.2.1, hp.2.2⟩

theorem MemoryOperation.typed_runtime (op : MemoryOperation) (C : context)
    (env : metadata.Env) (ctx : code.Context) (hC : wf_context C)
    (hm : EnvTranslation.Matches env ctx C) (arg : code.MemArg) (lane : U8)
    (hmem : 0 < env.mem_types.val.length) (ha : arg.align.val ≤ op.naturalAlign)
    (hl : op.laneCount ≠ 0 → lane.val < op.laneCount) :
    Instr_ok C (op.instruction (MemoryMeaning.memArg arg) (.mk_uN lane.val))
      (.mk_functype (.mk_list op.inputs) (.mk_list op.outputs)) := by
  have hlen : 0 < C.MEMS.length := by simpa [hm.mems] using hmem
  apply op.typed C (MemoryMeaning.memArg arg) (.mk_uN lane.val) C.MEMS[0]!
    hlen rfl hC ?_ (MemoryMeaning.memArg_wf arg) (by constructor; scalar_tac)
    (MemoryMeaning.alignment_mono _ _ ha) hl
  rw [hm.mems]
  cases he : env.mem_types.val with
  | nil => simp [he] at hmem
  | cons mt rest => simpa [he] using EnvTranslation.memType_wf mt

end Itasca.Wasm2.Simd

end

/-! ## Shuffle -/

section

/-!
# The `i8x16.shuffle` reader

Specs of the extracted `code.read_simd_shuffle`: `shuffle_scan` and `shuffle_complete` show that
the operand reader runs only after all sixteen lane bytes are range checked below 32, and
`shuffle_segment` gives its stack effect and the encoding of the accepted words. `shuffleFinish`
is the operand step that follows the scan.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2.Simd

/-- Operand validation after the sixteen shuffle bytes have been range checked. -/
def shuffleFinish (st : code.OpIterState) (data : Slice U8) :
    Result (core.result.Result (U64 × U64) error.OpError × code.OpIterState) := do
  let (r, s) ← code.take_simd_bits st data
  match r with
  | .Err e => .ok (.Err e, s)
  | .Ok bits => carryFixed bits s [.V128, .V128] (some .V128)

private theorem finish_body (st : code.OpIterState) (data : Slice U8) (pos : Usize) (i : I32)
    (hi : ¬ i < 16#i32) :
    code.read_simd_shuffle_loop.body st.vals st.ctrls st.pos data pos i = (do
      let r ← shuffleFinish st data
      .ok (.done r)) := by
  simp only [code.read_simd_shuffle_loop.body, hi, if_false, shuffleFinish, Std.bind_assoc, Std.uncurry]
  congr 1
  funext pair
  obtain ⟨r, s⟩ := pair
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok bits =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, binary_fixed, carryFixed,
      Std.bind_assoc, Std.uncurry]
    congr 1
    funext pair
    obtain ⟨r, s⟩ := pair
    cases r <;> simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- The scanner reaches its operand reader only after checking all sixteen bytes. -/
theorem shuffle_scan (st : code.OpIterState) (data : Slice U8)
    (hpos : st.pos.val ≤ data.length)
    (Q : core.result.Result (U64 × U64) error.OpError × code.OpIterState → Prop)
    (herr : ∀ e, Q (.Err e, st))
    (hfinish : ∀ bytes next, Wasm1.BytesAt data st.pos bytes next → bytes.length = 16 →
      (∀ b ∈ bytes, b.val < 32) → shuffleFinish st data ⦃ Q ⦄) :
    code.read_simd_shuffle st data ⦃ Q ⦄ := by
  unfold code.read_simd_shuffle code.read_simd_shuffle_loop
  apply loop.spec_decr_nat (fun p => (16 - p.2.val).toNat)
    (fun p => 0 ≤ p.2.val ∧ p.2.val ≤ 16 ∧ ∃ before : List U8,
      Wasm1.BytesAt data st.pos before p.1 ∧ before.length = p.2.val.toNat ∧
      ∀ b ∈ before, b.val < 32)
  · rintro ⟨pos, i⟩ ⟨hi, hn, before, hb, hl, hbefore⟩
    dsimp only at *
    by_cases hlt : i < 16#i32
    · simp only [code.read_simd_shuffle_loop.body, hlt, if_true]
      by_cases hp : pos.val < data.length
      · obtain ⟨_, hr, next, rfl, hnext⟩ := WP.spec_imp_exists (reader.read_byte.spec data pos hp)
        simp only [hr, bind_ok, core.result.Result.Insts.CoreOpsTry.branch, Std.uncurry]
        split
        · simpa using herr error.OpError.InvalidLane
        · rename_i hsmall
          step
          refine ⟨by scalar_tac, by scalar_tac, ⟨before ++ [data.val[pos.val]],
            hb.append (Wasm1.BytesAt.byte data pos next _ hp rfl hnext), ?_, ?_⟩, ?_⟩
          · simp only [List.length_append, List.length_singleton]
            scalar_tac
          · intro b hm
            simp only [List.mem_append, List.mem_singleton] at hm
            rcases hm with hm | rfl
            · exact hbefore b hm
            · scalar_tac
          · scalar_tac
      · simp [reader.read_byte.eof data pos (by omega),
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, herr]
    · rw [finish_body st data pos i hlt]
      apply WP.spec_mono (WP.spec_bind (hfinish before pos hb (by scalar_tac) hbefore) ?_)
      · intro r hr; exact hr
      · intro r hr
        simpa using hr
  · dsimp only
    exact ⟨by decide, by decide, [], Wasm1.BytesAt.nil data st.pos hpos, by simp, by simp⟩

/-- Every independently valid shuffle immediate reaches the operand reader. -/
theorem shuffle_complete (st : code.OpIterState) (data : Slice U8)
    (bytes : List U8) (next : Usize) (hb : Wasm1.BytesAt data st.pos bytes next)
    (hl : bytes.length = 16) (hbound : ∀ b ∈ bytes, b.val < 32)
    (r : core.result.Result (U64 × U64) error.OpError × code.OpIterState)
    (hfinish : shuffleFinish st data = .ok r) :
    code.read_simd_shuffle st data = .ok r := by
  have hrun : code.read_simd_shuffle st data ⦃ result => result = r ⦄ := by
    unfold code.read_simd_shuffle code.read_simd_shuffle_loop
    apply loop.spec_decr_nat (fun p => (16 - p.2.val).toNat)
      (fun p => 0 ≤ p.2.val ∧ ∃ rest : List U8,
        Wasm1.BytesAt data p.1 rest next ∧ p.2.val + (rest.length : Int) = 16 ∧
        ∀ b ∈ rest, b.val < 32)
    · rintro ⟨pos, i⟩ ⟨hi, rest, hrest, hlen, hsmall⟩
      dsimp only at *
      by_cases hlt : i < 16#i32
      · cases rest with
        | nil => simp only [List.length_nil] at hlen; scalar_tac
        | cons b rest =>
          obtain ⟨middle, hb1, hb2⟩ := (show Wasm1.BytesAt data pos ([b] ++ rest) next from hrest).split
          have hblt : ¬ b ≥ 32#u8 := by have := hsmall b (by simp); scalar_tac
          simp only [code.read_simd_shuffle_loop.body, hlt, if_true, hb1.read_byte,
            bind_ok, core.result.Result.Insts.CoreOpsTry.branch, Std.uncurry, hblt, if_false]
          step
          refine ⟨by scalar_tac, ⟨rest, hb2, ?_, fun b hb => hsmall b (by simp [hb])⟩, ?_⟩
          · simp only [List.length_cons] at hlen
            scalar_tac
          · simp only [List.length_cons] at hlen
            scalar_tac
      · rw [finish_body st data pos i hlt, hfinish]
        simp
    · dsimp only
      exact ⟨by decide, bytes, hb, by simp [hl], hbound⟩
  obtain ⟨result, he, rfl⟩ := WP.spec_imp_exists hrun
  exact he

/-- The scanner's accepted words encode exactly the bounded lane vector and its stack effect. -/
theorem shuffle_segment (st : code.OpIterState) (data : Slice U8)
    (outer segment : List code.StackType) (hv : st.vals.val = outer ++ segment)
    (hb : (Control.base st).val = outer.length) (hsize : st.vals.val.length < Usize.max)
    (hpos : st.pos.val ≤ data.length) :
    code.read_simd_shuffle st data ⦃ r => ∀ low high, r.1 = .Ok (low, high) →
      r.2.ctrls = st.ctrls ∧ ∃ after, r.2.vals.val = outer ++ after ∧
        BitsDecoded data st.pos low high r.2.pos ∧
        (∀ lane ∈ shuffleIndices low high, proj_uN_0 lane < 32) ∧
        FixedEffect (Control.polymorphic st) segment [.V128, .V128] (some .V128) after ⦄ := by
  apply shuffle_scan st data hpos
  · intro e; simp
  · intro bytes next hbytes hlen hbounds
    obtain ⟨⟨r, decoded⟩, hd, hc, hvals, hbits⟩ := WP.spec_imp_exists (take_bits_spec st data)
    dsimp only at hc hvals hbits
    simp only [shuffleFinish, hd, bind_ok, Std.uncurry]
    cases r with
    | Err e => simp
    | Ok bits =>
      obtain ⟨low, high⟩ := bits
      have hdecoded := hbits low high rfl
      obtain ⟨lower, upper, hlo, hhi, hspan⟩ := hdecoded
      have he : decoded.pos = next := by
        apply UScalar.eq_of_val_eq
        have h1 := hspan.length
        have h2 := hbytes.length
        simp only [List.length_append, hlo.1, hhi.1] at h1
        omega
      have hbytesEq : lower ++ upper = bytes := by
        have h1 := hspan.suffix
        rw [he, hbytes.suffix] at h1
        exact (List.append_cancel_right h1).symm
      have hbounded : ∀ lane ∈ shuffleIndices low high, proj_uN_0 lane < 32 := by
        rw [shuffleIndices_encoding low high lower upper hlo hhi, hbytesEq]
        intro lane hm
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hm
        exact hbounds b hb
      apply WP.spec_mono (carryFixed.segment (low, high) decoded [.V128, .V128] (some .V128)
        outer segment (by simpa [hvals] using hv) (by simpa [Control.base, hc] using hb)
        (by simpa [hvals] using hsize))
      rintro ⟨res, s⟩ ⟨hctrl, hposition, after, hstack, _, heffect⟩ lo hi hok
      dsimp only at hctrl hposition hstack heffect hok
      obtain ⟨heq, heff⟩ := heffect (lo, hi) hok
      cases heq
      refine ⟨hctrl.trans hc, after, hstack, ?_, hbounded, ?_⟩
      · simpa only [hposition] using hbits low high rfl
      · simpa only [Control.polymorphic, hc] using heff

end Itasca.Wasm2.Simd

end

/-! ## Visitor -/

section

/-!
# Visitor transfer for SIMD instructions

`simd_transfer` shows that if `code.step_simd` accepts with one visitor, it accepts with any
replacement visitor whose callbacks accept, reaching the same reader state.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2.Simd

private theorem sub_transfer {V W : Type} (visitor : code.OpVisitor V)
    (replacement : code.OpVisitor W) (ha : FullVisitor.Accepts replacement)
    (st final : code.OpIterState) (data : Slice U8) (env : metadata.Env)
    (subopcode : U32) (v v' : V) (w : W)
    (h : subStep visitor st data env subopcode v = .ok (.Ok (), final, v')) :
    ∃ w', subStep replacement st data env subopcode w = .ok (.Ok (), final, w') := by
  unfold subStep at h ⊢
  rw [pure_table] at h ⊢
  cases hm : pureMeaning subopcode.val with
  | some op =>
    simp only [hm, Option.map_some, bind_ok] at h ⊢
    exact CoreVisitor.run.accepted_lift _ _ _ v w final v' h (fun _ => ha.on_simd w final subopcode)
  | none =>
    simp only [hm, Option.map_none, bind_ok] at h ⊢
    rw [lane_table] at h ⊢
    cases hl : laneMeaning subopcode.val with
    | some lane =>
      simp only [hl, Option.map_some, bind_ok] at h ⊢
      rcases he : lane.runtime with ⟨ty, count, replace⟩
      simp only [he] at h ⊢
      exact CoreVisitor.run.accepted_lift _ _ _ v w final v' h
        (fun a => ha.on_simd_lane w final subopcode a)
    | none =>
      simp only [hl, Option.map_none, bind_ok] at h ⊢
      rw [memory_table] at h ⊢
      cases hm : memoryMeaning subopcode.val with
      | some mem =>
        simp only [hm, Option.map_some, bind_ok] at h ⊢
        rcases he : mem.runtime with ⟨align, store, count⟩
        simp only [he] at h ⊢
        split at h
        · rename_i hc
          simp only [hc, if_true]
          exact CoreVisitor.run.accepted_lift _ _ _ v w final v' h
            (fun a => ha.on_simd_memory_lane w final subopcode a.1 a.2)
        · rename_i hc
          simp only [hc]
          cases store <;> simp only [Bool.false_eq_true, if_true, if_false] at h ⊢
          all_goals exact CoreVisitor.run.accepted_lift _ _ _ v w final v' h (fun a => ha.on_simd_memory w final subopcode a)
      | none =>
        simp only [hm, Option.map_none, bind_ok] at h ⊢
        split at h
        · exact CoreVisitor.run.accepted_lift _ _ _ v w final v' h
            (fun a => ha.on_simd_const w final a.1 a.2)
        · exact CoreVisitor.run.accepted_lift _ _ _ v w final v' h
            (fun a => ha.on_simd_shuffle w final a.1 a.2)
        · simp at h

/-- Accepting hooks preserve every successful SIMD state and immediate. -/
theorem simd_transfer {V W : Type} (visitor : code.OpVisitor V)
    (replacement : code.OpVisitor W) (ha : FullVisitor.Accepts replacement)
    (st final : code.OpIterState) (data : Slice U8) (env : metadata.Env)
    (v v' : V) (w : W)
    (h : code.step_simd visitor st data env v = .ok (.Ok (), final, v')) :
    ∃ w', code.step_simd replacement st data env w = .ok (.Ok (), final, w') := by
  rw [code.step_simd.eq_runs] at h ⊢
  unfold prefixStep at h ⊢
  obtain ⟨r, hr⟩ := reader.read_u32_leb.total data st.pos
  simp only [hr, bind_ok] at h ⊢
  cases r with
  | Err e => simp at h
  | Ok pair =>
    obtain ⟨subopcode, next⟩ := pair
    exact sub_transfer visitor replacement ha _ final data env subopcode v v' w h

end Itasca.Wasm2.Simd

end
