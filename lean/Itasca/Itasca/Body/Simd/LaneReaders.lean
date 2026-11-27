import Itasca.Body.Scalar.Env
import Itasca.Visitor.Total
import Itasca.Binary.Body.Encoding
import Mathlib.Tactic.IntervalCases
import Itasca.Binary.Scalar.Encoding
import Itasca.Body.LoopDispatch
import Itasca.Binary.Scalar.MemoryMeaning
import Itasca.Visitor.RunTrace

open WebAssembly

/-!
Proofs for Body / Simd.

This module collects LaneReaders, Visitor.
Each section documents its contracts and consumers.
-/

/-! ## LaneReaders -/

section

/-!
# Lane Readers

SIMD lane readers combine table lookup, immediate decoding, operand effects and cursor carry. Their dispatch contracts cover both success and normal-return error paths.
-/

/-! ## ReadersTotal -/

section

/-!
# Totality of SIMD readers

`@[step]` lemmas showing that the extracted SIMD readers (`code.take_simd_bits`,
`code.take_simd_lane`, `code.read_simd_signature`, `code.read_simd_lane`, memory loads and stores,
`code.read_simd_const` and `code.read_simd_shuffle`) never panic. `ReaderPost` is the shared
postcondition: structural shape, unchanged controls, forward cursor and bounded operand growth.
-/

open Aeneas Aeneas.Std

set_option maxHeartbeats 2000000

namespace Itasca.Body.Simd

def ReaderPost (st s : code.OpIterState) : Prop :=
  Body.Control.Shape s ∧ s.ctrls = st.ctrls ∧ st.pos.val ≤ s.pos.val ∧
    s.vals.val.length ≤ st.vals.val.length + 1

attribute [local step] code.pop_with_type.total code.pop_stack_type.total
  code.push_val.shape_total ScalarReaders.memarg code.check_memory_and_alignment.spec

@[local step] private theorem conversion_total (st : code.OpIterState) (input output : wasm_types.ValueType)
    (hs : Body.Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
    code.read_conversion st input output ⦃ r => ReaderPost st r.2 ⦄ := by
  unfold code.read_conversion ReaderPost
  step*

@[local step] private theorem binary_total (st : code.OpIterState) (input output : wasm_types.ValueType)
    (hs : Body.Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
    code.read_binary st input output ⦃ r => ReaderPost st r.2 ⦄ := by
  unfold code.read_binary ReaderPost
  step*

@[local step] private theorem byte_total (data : Slice U8) (pos : Usize) :
    reader.read_byte data pos ⦃ _ => True ⦄ := by
  by_cases hp : pos.val < data.length
  · exact WP.spec_mono (reader.read_byte.spec data pos hp) (by simp)
  · simp [reader.read_byte.eof data pos (by omega)]

@[local step] private theorem bits_forward (data : Slice U8) (pos : Usize) :
    reader.read_f64_bits data pos ⦃ r => match r with
      | .Ok (_, next) => pos.val ≤ next.val
      | .Err _ => True ⦄ := by
  apply WP.spec_mono (reader.read_f64_bits.spec data pos)
  intro r hr
  cases r with
  | Err _ => trivial
  | Ok pair => obtain ⟨bytes, _, hn, _⟩ := hr; omega

@[step] theorem take_bits_total (st : code.OpIterState) (data : Slice U8) (hs : Body.Control.Shape st) :
    code.take_simd_bits st data ⦃ r => Body.Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ∧ r.2.vals = st.vals ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (bits_forward data st.pos)
  cases r with
  | Err e =>
    simp [code.take_simd_bits, hr, hs, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
    obtain ⟨low, middle⟩ := pair
    obtain ⟨r, hr2, hp2⟩ := WP.spec_imp_exists (bits_forward data middle)
    cases r with
    | Err e =>
      simp [code.take_simd_bits, hr, hr2, hs, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok pair =>
      obtain ⟨high, last⟩ := pair
      simp only [code.take_simd_bits, hr, hr2, core.result.Result.Insts.CoreOpsTry.branch,
        bind_ok, Std.uncurry, WP.spec_ok]
      exact ⟨⟨hs.ordered, hs.bounded⟩, trivial, by omega, trivial⟩

@[step] theorem lane_total (st : code.OpIterState) (data : Slice U8) (count : U8)
    (hs : Body.Control.Shape st) :
    code.take_simd_lane st data count ⦃ r => Body.Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ∧ r.2.vals = st.vals ⦄ := by
  by_cases hp : st.pos.val < data.length
  · obtain ⟨_, hr, next, rfl, hn⟩ := WP.spec_imp_exists (reader.read_byte.spec data st.pos hp)
    simp only [code.take_simd_lane, hr, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    simp only [Std.uncurry]
    split <;> simp only [WP.spec_ok] <;> exact ⟨⟨hs.ordered, hs.bounded⟩, trivial, by omega, trivial⟩
  · simp [code.take_simd_lane, reader.read_byte.eof data st.pos (by omega), hs,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

@[step] theorem signature_total (st : code.OpIterState) (sig : code.SimdSignature)
    (hs : Body.Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
    code.read_simd_signature st sig ⦃ r => ReaderPost st r.2 ⦄ := by
  cases sig <;> unfold code.read_simd_signature
  all_goals step* <;> simp_all [ReaderPost] <;> omega

@[step] theorem read_lane_total (st : code.OpIterState) (data : Slice U8)
    (ty : wasm_types.ValueType) (count : U8) (replace : Bool)
    (hs : Body.Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
    code.read_simd_lane st data ty count replace ⦃ r => ReaderPost st r.2 ⦄ := by
  unfold code.read_simd_lane ReaderPost
  step* <;> simp_all [ReaderPost] <;> omega

@[step] theorem memory_lane_total (st : code.OpIterState) (data : Slice U8) (env : metadata.CodeMetadata)
    (alignment : U32) (store : Bool) (count : U8)
    (hs : Body.Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
    code.read_simd_memory_lane st data env alignment store count ⦃ r => ReaderPost st r.2 ⦄ := by
  unfold code.read_simd_memory_lane ReaderPost
  step*

@[step] theorem load_total (st : code.OpIterState) (data : Slice U8) (env : metadata.CodeMetadata)
    (ty : wasm_types.ValueType) (alignment : U32)
    (hs : Body.Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
    code.read_load st data env ty alignment ⦃ r => ReaderPost st r.2 ⦄ := by
  unfold code.read_load ReaderPost
  step*

@[step] theorem store_total (st : code.OpIterState) (data : Slice U8) (env : metadata.CodeMetadata)
    (ty : wasm_types.ValueType) (alignment : U32)
    (hs : Body.Control.Shape st) :
    code.read_store st data env ty alignment ⦃ r => ReaderPost st r.2 ⦄ := by
  unfold code.read_store ReaderPost
  step*

@[step] theorem constant_total (st : code.OpIterState) (data : Slice U8)
    (hs : Body.Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
    code.read_simd_const st data ⦃ r => ReaderPost st r.2 ⦄ := by
  unfold code.read_simd_const ReaderPost
  step*

@[local step] private theorem shuffle_loop_total (st : code.OpIterState) (data : Slice U8)
    (pos : Usize) (i : I32) (hi : 0 ≤ i.val ∧ i.val ≤ 16)
    (hs : Body.Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
    code.read_simd_shuffle_loop st.vals st.ctrls st.pos data pos i ⦃ r => ReaderPost st r.2 ⦄ := by
  unfold code.read_simd_shuffle_loop
  apply loop.spec_decr_nat (fun p => (16 - p.2.val).toNat)
    (fun p => 0 ≤ p.2.val ∧ p.2.val ≤ 16)
  · rintro ⟨pos, i⟩ ⟨hi, hn⟩
    unfold code.read_simd_shuffle_loop.body
    step* <;> simp_all [ReaderPost]
    all_goals try (cases val; step* <;> simp_all)
    all_goals scalar_tac
  · exact hi

@[step] theorem shuffle_total (st : code.OpIterState) (data : Slice U8)
    (hs : Body.Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
    code.read_simd_shuffle st data ⦃ r => ReaderPost st r.2 ⦄ :=
  shuffle_loop_total st data st.pos 0#i32 (by decide) hs hsize

end Itasca.Body.Simd

end

/-! ## Tables -/

section

/-!
# SIMD opcode tables

`pure_table`, `lane_table` and `memory_table` show that the extracted tables `code.simd_signature`,
`code.simd_lane_info` and `code.simd_memory_info` agree with the independent meanings
`pureMeaning`, `laneMeaning` and `memoryMeaning`, for every `u32` subopcode.
`Signature.runtime`, `LaneOperation.runtime` and `MemoryOperation.runtime` map the independent
classification to the extracted representation.
-/

open Aeneas Aeneas.Std

namespace Itasca.Body.Simd

/-- The extracted `code.SimdSignature` for an independent pure SIMD signature. -/
def Signature.runtime : Signature → code.SimdSignature
  | .unary => .Unary
  | .binary => .Binary
  | .ternary => .Ternary
  | .test => .Test
  | .shift => .Shift
  | .splatI32 => .SplatI32
  | .splatI64 => .SplatI64
  | .splatF32 => .SplatF32
  | .splatF64 => .SplatF64

/-- The scalar type, lane count and replace flag that `code.simd_lane_info` returns for a lane
operation. -/
def LaneOperation.runtime (op : LaneOperation) : wasm_types.ValueType × U8 × Bool :=
  (match op.scalar with
   | .I32 => .I32 | .I64 => .I64 | .F32 => .F32 | .F64 => .F64,
   U8.ofNatCore op.count (by cases op <;> decide), op.replace)

/-- The natural alignment, store flag and lane count that `code.simd_memory_info` returns for a
memory operation. -/
def MemoryOperation.runtime (op : MemoryOperation) : U32 × Bool × U8 :=
  (U32.ofNatCore op.naturalAlign (by cases op <;> decide), op.store,
   U8.ofNatCore op.laneCount (by cases op <;> decide))

end Itasca.Body.Simd

open Aeneas Aeneas.Std

namespace Itasca.Body.Simd

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
/-- The runtime pure signature table agrees with independent instruction meanings. -/
theorem pure_table (opcode : U32) :
    code.simd_signature opcode = .ok ((pureMeaning opcode.val).map (fun op => op.signature.runtime)) := by
  by_cases hb : opcode.val < 256
  · rcases opcode with ⟨⟨n, hn⟩⟩
    change n < 256 at hb
    interval_cases n <;> (with_unfolding_all rfl)
  · have hnone : pureMeaning opcode.val = none := by
      cases hm : pureMeaning opcode.val with
      | none => rfl
      | some op => exact False.elim (hb (pure_bound hm))
    rw [hnone]
    simp only [Option.map_none]
    have hn : opcode ≥ 256#u32 := by scalar_tac
    unfold code.simd_signature
    rw [if_pos hn]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- The runtime lane table agrees with independent lane operation meanings. -/
theorem lane_table (opcode : U32) :
    code.simd_lane_info opcode = .ok ((laneMeaning opcode.val).map LaneOperation.runtime) := by
  by_cases hb : opcode.val < 256
  · rcases opcode with ⟨⟨n, hn⟩⟩
    change n < 256 at hb
    interval_cases n <;> (with_unfolding_all rfl)
  · have hnone : laneMeaning opcode.val = none := by
      unfold laneMeaning
      split <;> first | rfl | omega
    rw [hnone]
    simp only [Option.map_none]
    unfold code.simd_lane_info
    split <;> first | rfl | (exfalso; apply hb; decide)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- The runtime memory table agrees with independent memory operation meanings. -/
theorem memory_table (opcode : U32) :
    code.simd_memory_info opcode = .ok ((memoryMeaning opcode.val).map MemoryOperation.runtime) := by
  by_cases hb : opcode.val < 256
  · rcases opcode with ⟨⟨n, hn⟩⟩
    change n < 256 at hb
    interval_cases n <;> (with_unfolding_all rfl)
  · have hnone : memoryMeaning opcode.val = none := by
      unfold memoryMeaning
      split <;> first | rfl | omega
    rw [hnone]
    simp only [Option.map_none]
    unfold code.simd_memory_info
    split <;> first | rfl | (exfalso; apply hb; decide)

end Itasca.Body.Simd

end

/-! ## Dispatch -/

section

/-!
# Dispatch of SIMD instructions

`Simd.prefixStep` and `Simd.subStep` unfold the extracted `code.step_simd` (opcode `0xFD`) into
`Visitor.Core.run` applied to the reader for each operation class. `code.step_simd.eq_runs` proves
the two equal, and the `subStep.*` equations specialize it to pure, lane, memory, memory lane,
constant and shuffle subopcodes using the table agreement of `Body/Simd/LaneReaders`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Body.Simd

/-- Factorization of the SIMD subopcode dispatcher around its readers and visitor callbacks. -/
def subStep {V : Type} (visitor : code.OpVisitor V) (st : code.OpIterState)
    (data : Slice U8) (env : metadata.CodeMetadata) (subopcode : U32) (v : V) :
    Result (core.result.Result Unit error.OpError × code.OpIterState × V) := do
  let sig ← code.simd_signature subopcode
  match sig with
  | some sig =>
    Visitor.Core.run (code.read_simd_signature st sig)
      (fun v s _ => visitor.on_simd v s subopcode) v
  | none =>
    let lane ← code.simd_lane_info subopcode
    match lane with
    | some (ty, count, replace) =>
      Visitor.Core.run (code.read_simd_lane st data ty count replace)
        (fun v s lane => visitor.on_simd_lane v s subopcode lane) v
    | none =>
      let memory ← code.simd_memory_info subopcode
      match memory with
      | some (align, store, count) =>
        if count != 0#u8 then
          Visitor.Core.run (code.read_simd_memory_lane st data env align store count)
            (fun v s a => visitor.on_simd_memory_lane v s subopcode a.1 a.2) v
        else if store then
          Visitor.Core.run (code.read_store st data env .V128 align)
            (fun v s arg => visitor.on_simd_memory v s subopcode arg) v
        else
          Visitor.Core.run (code.read_load st data env .V128 align)
            (fun v s arg => visitor.on_simd_memory v s subopcode arg) v
      | none =>
        match subopcode with
        | 12#uscalar =>
          Visitor.Core.run (code.read_simd_const st data)
            (fun v s a => visitor.on_simd_const v s a.1 a.2) v
        | 13#uscalar =>
          Visitor.Core.run (code.read_simd_shuffle st data)
            (fun v s a => visitor.on_simd_shuffle v s a.1 a.2) v
        | _ => .ok (.Err .UnrecognizedOpcode, st, v)

/-- Reads the subopcode after `0xFD` and continues with `subStep`. -/
def prefixStep {V : Type} (visitor : code.OpVisitor V) (st : code.OpIterState)
    (data : Slice U8) (env : metadata.CodeMetadata) (v : V) :
    Result (core.result.Result Unit error.OpError × code.OpIterState × V) := do
  let r ← reader.read_u32_leb data st.pos
  match r with
  | .Err e => .ok (.Err e, st, v)
  | .Ok (subopcode, next) => subStep visitor {st with pos := next} data env subopcode v

end Itasca.Body.Simd

namespace Itasca

theorem code.step_wasm2.simd {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.CodeMetadata) (ctx : code.Context) (v : V) :
    code.step_wasm2 visitor st data env ctx 0xFD#u8 v = code.step_simd visitor st data env v := rfl

macro "finish_simd_run" : tactic => `(tactic| (
  simp only [Visitor.Core.run]
  congr 1
  funext pair
  obtain ⟨r, s⟩ := pair
  cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  all_goals congr 1
  all_goals funext pair
  all_goals obtain ⟨reply, w⟩ := pair
  all_goals cases reply <;> simp [code.visit, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
))

/-- `code.step_simd` equals its unfolded form `Body.Simd.prefixStep`. -/
theorem code.step_simd.eq_runs {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.CodeMetadata) (v : V) :
    code.step_simd visitor st data env v = Body.Simd.prefixStep visitor st data env v := by
  unfold code.step_simd Body.Simd.prefixStep
  congr 1
  funext r
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
    obtain ⟨subopcode, next⟩ := pair
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Std.uncurry, Body.Simd.subStep]
    congr 1
    funext sig
    cases sig with
    | some sig => finish_simd_run
    | none =>
      simp only
      congr 1
      funext lane
      cases lane with
      | some triple =>
        obtain ⟨ty, count, replace⟩ := triple
        finish_simd_run
      | none =>
        simp only
        congr 1
        funext mem
        cases mem with
        | some triple =>
          obtain ⟨align, store, count⟩ := triple
          simp only
          split
          · finish_simd_run
          · split <;> finish_simd_run
        | none =>
          simp only
          split
          · finish_simd_run
          · finish_simd_run
          · split <;> simp_all

end Itasca

open Aeneas Aeneas.Std

namespace Itasca.Body.Simd

theorem subStep.pure {V : Type} (visitor : code.OpVisitor V) (st : code.OpIterState)
    (data : Slice U8) (env : metadata.CodeMetadata) (opcode : U32) (v : V) (op : Operation)
    (h : pureMeaning opcode.val = some op) :
    subStep visitor st data env opcode v = Visitor.Core.run (code.read_simd_signature st op.signature.runtime)
      (fun v s _ => visitor.on_simd v s opcode) v := by
  simp only [subStep, pure_table, h, Option.map_some, bind_ok]

theorem subStep.lane {V : Type} (visitor : code.OpVisitor V) (st : code.OpIterState)
    (data : Slice U8) (env : metadata.CodeMetadata) (opcode : U32) (v : V) (op : LaneOperation)
    (h : laneMeaning opcode.val = some op) :
    subStep visitor st data env opcode v = Visitor.Core.run
      (code.read_simd_lane st data op.runtime.1 op.runtime.2.1 op.replace)
      (fun v s a => visitor.on_simd_lane v s opcode a) v := by
  simp only [subStep, pure_table, lane_pure_none h, lane_table, h, Option.map_none,
    Option.map_some, bind_ok, LaneOperation.runtime]

theorem subStep.memory {V : Type} (visitor : code.OpVisitor V) (st : code.OpIterState)
    (data : Slice U8) (env : metadata.CodeMetadata) (opcode : U32) (v : V) (op : MemoryOperation)
    (h : memoryMeaning opcode.val = some op) (hc : op.laneCount = 0) :
    subStep visitor st data env opcode v = Visitor.Core.run
      (if op.store then code.read_store st data env .V128 op.runtime.1
        else code.read_load st data env .V128 op.runtime.1)
      (fun v s a => visitor.on_simd_memory v s opcode a) v := by
  simp only [subStep, pure_table, memory_pure_none h, lane_table, memory_lane_none h,
    memory_table, h, Option.map_none, Option.map_some, bind_ok, MemoryOperation.runtime, hc]
  cases op.store <;> rfl

theorem subStep.memory_lane {V : Type} (visitor : code.OpVisitor V) (st : code.OpIterState)
    (data : Slice U8) (env : metadata.CodeMetadata) (opcode : U32) (v : V) (op : MemoryOperation)
    (h : memoryMeaning opcode.val = some op) (hc : op.laneCount ≠ 0) :
    subStep visitor st data env opcode v = Visitor.Core.run
      (code.read_simd_memory_lane st data env op.runtime.1 op.store op.runtime.2.2)
      (fun v s a => visitor.on_simd_memory_lane v s opcode a.1 a.2) v := by
  simp only [subStep, pure_table, memory_pure_none h, lane_table, memory_lane_none h,
    memory_table, h, Option.map_none, Option.map_some, bind_ok, MemoryOperation.runtime]
  have hn : (U8.ofNatCore op.laneCount (by cases op <;> decide) != 0#u8) = true := by
    cases op <;> first | contradiction | rfl
  rw [if_pos hn]

theorem subStep.constant {V : Type} (visitor : code.OpVisitor V) (st : code.OpIterState)
    (data : Slice U8) (env : metadata.CodeMetadata) (v : V) :
    subStep visitor st data env 12#u32 v = Visitor.Core.run (code.read_simd_const st data)
      (fun v s a => visitor.on_simd_const v s a.1 a.2) v := by
  have hp : pureMeaning (12#u32).val = none := by with_unfolding_all rfl
  have hl : laneMeaning (12#u32).val = none := by with_unfolding_all rfl
  have hm : memoryMeaning (12#u32).val = none := by with_unfolding_all rfl
  simp only [subStep, pure_table, lane_table, memory_table, hp, hl, hm, Option.map_none, bind_ok]
  with_unfolding_all rfl

theorem subStep.shuffle {V : Type} (visitor : code.OpVisitor V) (st : code.OpIterState)
    (data : Slice U8) (env : metadata.CodeMetadata) (v : V) :
    subStep visitor st data env 13#u32 v = Visitor.Core.run (code.read_simd_shuffle st data)
      (fun v s a => visitor.on_simd_shuffle v s a.1 a.2) v := by
  have hp : pureMeaning (13#u32).val = none := by with_unfolding_all rfl
  have hl : laneMeaning (13#u32).val = none := by with_unfolding_all rfl
  have hm : memoryMeaning (13#u32).val = none := by with_unfolding_all rfl
  simp only [subStep, pure_table, lane_table, memory_table, hp, hl, hm, Option.map_none, bind_ok]
  with_unfolding_all rfl

end Itasca.Body.Simd

end

/-! ## DispatchTotal -/

section

/-!
# Totality of the SIMD dispatcher

`simd_total` shows that the extracted `code.step_simd` never panics under a total visitor, keeps
the control stack and moves the cursor forward, for every subopcode and immediate.
-/

open Aeneas Aeneas.Std

namespace Itasca.Body.Simd

private theorem run_total {A V : Type}
    (read : Result (core.result.Result A error.OpError × code.OpIterState))
    (hook : V → code.OpIterState → A → Result (core.result.Result Unit error.VisitError × V))
    (v : V) (st : code.OpIterState)
    (hr : read ⦃ r => ReaderPost st r.2 ⦄)
    (hh : ∀ s a, ∃ res v', hook v s a = .ok (res, v')) :
    Visitor.Core.run read hook v ⦃ r => ReaderPost st r.2.1 ⦄ := by
  apply WP.spec_mono (Visitor.Core.run.spec read hook v (ReaderPost st) (fun _ _ => True) ?_ hh)
  · exact fun _ h => h.1
  · exact WP.spec_mono hr (fun _ h => ⟨h, by simp⟩)

theorem sub_total {V : Type} (visitor : code.OpVisitor V) (st : code.OpIterState)
    (data : Slice U8) (env : metadata.CodeMetadata) (subopcode : U32) (v : V)
    (hs : Body.Control.Shape st) (hsize : st.vals.val.length < Usize.max)
    (hv : Visitor.Total visitor) :
    subStep visitor st data env subopcode v ⦃ r => ReaderPost st r.2.1 ⦄ := by
  unfold subStep
  rw [pure_table]
  cases hm : pureMeaning subopcode.val with
  | some op =>
    simp only [Option.map_some, bind_ok]
    exact run_total _ _ v st (signature_total _ _ hs hsize) (fun s _ => hv.on_simd v s subopcode)
  | none =>
    simp only [Option.map_none, bind_ok]
    rw [lane_table]
    cases hl : laneMeaning subopcode.val with
    | some lane =>
      simp only [Option.map_some, bind_ok]
      rcases he : lane.runtime with ⟨ty, count, replace⟩
      simp only
      exact run_total _ _ v st (read_lane_total _ _ _ _ _ hs hsize)
        (fun s a => hv.on_simd_lane v s subopcode a)
    | none =>
      simp only [Option.map_none, bind_ok]
      rw [memory_table]
      cases hm : memoryMeaning subopcode.val with
      | some mem =>
        simp only [Option.map_some, bind_ok]
        rcases he : mem.runtime with ⟨align, store, count⟩
        simp only
        split
        · exact run_total _ _ v st (memory_lane_total _ _ _ _ _ _ hs hsize)
            (fun s a => hv.on_simd_memory_lane v s subopcode a.1 a.2)
        · split
          · exact run_total _ _ v st (store_total _ _ _ _ _ hs)
              (fun s a => hv.on_simd_memory v s subopcode a)
          · exact run_total _ _ v st (load_total _ _ _ _ _ hs hsize)
              (fun s a => hv.on_simd_memory v s subopcode a)
      | none =>
        simp only [Option.map_none, bind_ok]
        split
        · exact run_total _ _ v st (constant_total _ _ hs hsize)
            (fun s a => hv.on_simd_const v s a.1 a.2)
        · exact run_total _ _ v st (shuffle_total _ _ hs hsize)
            (fun s a => hv.on_simd_shuffle v s a.1 a.2)
        · simp [ReaderPost, hs]

/-- Every SIMD prefix terminates, preserves controls, and advances monotonically. -/
theorem simd_total {V : Type} (visitor : code.OpVisitor V) (st : code.OpIterState)
    (data : Slice U8) (env : metadata.CodeMetadata) (v : V)
    (hs : Body.Control.Shape st) (hsize : st.vals.val.length < Usize.max)
    (hv : Visitor.Total visitor) :
    code.step_simd visitor st data env v ⦃ r => Body.Control.Shape r.2.1 ∧
      r.2.1.ctrls = st.ctrls ∧ st.pos.val ≤ r.2.1.pos.val ∧
      r.2.1.vals.val.length ≤ st.vals.val.length + 1 ⦄ := by
  rw [code.step_simd.eq_runs]
  unfold prefixStep
  obtain ⟨r, hr, hd⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data st.pos)
  rw [hr]
  simp only [bind_ok]
  cases r with
  | Err e => simp [hs]
  | Ok pair =>
    obtain ⟨subopcode, next⟩ := pair
    apply WP.spec_mono (sub_total visitor {st with pos := next} data env subopcode v
      ⟨hs.ordered, hs.bounded⟩ hsize hv)
    intro r h
    have hp := (Binary.Leb128.Decoded.span data st.pos subopcode next hd).1
    have hn : next.val ≤ r.2.1.pos.val := h.2.2.1
    exact ⟨h.1, h.2.1, by omega, h.2.2.2⟩

end Itasca.Body.Simd

end

/-! ## Decode -/

section

/-!
# Decoding SIMD lane indices and 128-bit immediates

Specs and completeness for the extracted `code.take_simd_lane` and `code.take_simd_bits`.
Accepted lane bytes lie below the instruction's lane count (`take_lane_spec`), and accepted
immediates decode to low and high 64-bit words (`take_bits_spec`, `BitsDecoded`). The `*_complete`
lemmas give the converse.
-/

open Aeneas Aeneas.Std

namespace Itasca.Body.Simd

theorem state_of_stacks (s st : code.OpIterState) (hv : s.vals = st.vals) (hc : s.ctrls = st.ctrls) :
    s = {st with pos := s.pos} := by cases s; cases st; simp_all

/-- Accepted lane bytes satisfy their instruction-specific lane limit. -/
theorem take_lane_spec (st : code.OpIterState) (data : Slice U8) (count : U8) :
    code.take_simd_lane st data count ⦃ r => r.2.ctrls = st.ctrls ∧ r.2.vals = st.vals ∧
      (∀ lane, r.1 = .Ok lane → lane.val < count.val ∧
        Body.Scalar.BytesAt data st.pos [lane] r.2.pos) ⦄ := by
  by_cases hp : st.pos.val < data.length
  · obtain ⟨_, hr, next, rfl, hn⟩ := WP.spec_imp_exists (reader.read_byte.spec data st.pos hp)
    simp only [code.take_simd_lane, hr, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    simp only [Std.uncurry]
    split
    · simp
    · rename_i hl
      rw [WP.spec_ok]
      refine ⟨rfl, rfl, ?_⟩
      intro lane he
      cases he
      exact ⟨by scalar_tac, Body.Scalar.BytesAt.byte data st.pos next _ hp rfl hn⟩
  · simp [code.take_simd_lane, reader.read_byte.eof data st.pos (by omega),
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

theorem take_lane_complete (st : code.OpIterState) (data : Slice U8) (count lane : U8)
    (next : Usize) (hb : Body.Scalar.BytesAt data st.pos [lane] next) (hl : lane.val < count.val) :
    code.take_simd_lane st data count = .ok (.Ok lane, {st with pos := next}) := by
  have hn : ¬ lane ≥ count := by scalar_tac
  simp [code.take_simd_lane, hb.read_byte, hl, core.result.Result.Insts.CoreOpsTry.branch]

/-- Sixteen accepted bytes split into their exact low and high words. -/
def BitsDecoded (data : Slice U8) (start : Usize) (low high : U64) (next : Usize) : Prop :=
  ∃ lower upper, Binary.FloatBits.Encoding 8 lower low.val ∧ Binary.FloatBits.Encoding 8 upper high.val ∧
    Body.Scalar.BytesAt data start (lower ++ upper) next

theorem take_bits_spec (st : code.OpIterState) (data : Slice U8) :
    code.take_simd_bits st data ⦃ r => r.2.ctrls = st.ctrls ∧ r.2.vals = st.vals ∧
      (∀ low high, r.1 = .Ok (low, high) → BitsDecoded data st.pos low high r.2.pos) ⦄ := by
  obtain ⟨r, hr, hd⟩ := WP.spec_imp_exists (reader.read_f64_bits.spec data st.pos)
  cases r with
  | Err e =>
    simp [code.take_simd_bits, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
    obtain ⟨low, middle⟩ := pair
    obtain ⟨r, hr2, hd2⟩ := WP.spec_imp_exists (reader.read_f64_bits.spec data middle)
    cases r with
    | Err e =>
      simp [code.take_simd_bits, hr, hr2, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok pair =>
      obtain ⟨high, last⟩ := pair
      simp only [code.take_simd_bits, hr, hr2, core.result.Result.Insts.CoreOpsTry.branch,
        bind_ok, Std.uncurry, WP.spec_ok]
      obtain ⟨lower, hls, hll, hlb, hle⟩ := hd
      obtain ⟨upper, hus, hul, hub, hue⟩ := hd2
      refine ⟨trivial, trivial, ?_⟩
      intro lo hi he
      cases he
      exact ⟨lower, upper, hle, hue,
        (show Body.Scalar.BytesAt data st.pos lower middle from ⟨hls, by simpa [hle.1] using hll, hlb⟩).append
          ⟨hus, by simpa [hue.1] using hul, hub⟩⟩

theorem take_bits_complete (st : code.OpIterState) (data : Slice U8)
    (low high : U64) (lower upper : List U8) (next : Usize)
    (hl : Binary.FloatBits.Encoding 8 lower low.val) (hh : Binary.FloatBits.Encoding 8 upper high.val)
    (hb : Body.Scalar.BytesAt data st.pos (lower ++ upper) next) :
    code.take_simd_bits st data = .ok (.Ok (low, high), {st with pos := next}) := by
  obtain ⟨middle, hfirst, hlast⟩ := hb.split
  simp [code.take_simd_bits, hfirst.read_f64 low hl, hlast.read_f64 high hh,
    core.result.Result.Insts.CoreOpsTry.branch]

end Itasca.Body.Simd

end

/-! ## Carry -/

section

/-!
# Fixed operand effects that carry an immediate

`carryFixed` applies `readFixed` and then returns an already parsed immediate. Its segment,
completeness and visitor-runner lemmas (`carryFixed.segment`, `carryFixed.complete`,
`carryFixed.run`) are the shared interface for the SIMD lane, constant, shuffle and memory readers.
-/

open Aeneas Aeneas.Std

namespace Itasca.Body.Simd

/-- Applies a fixed operand effect and returns the already parsed immediate. -/
def carryFixed {A : Type} (a : A) (st : code.OpIterState) (inputs : List wasm_types.ValueType)
    (output : Option wasm_types.ValueType) : Result (core.result.Result A error.OpError × code.OpIterState) := do
  let (r, s) ← readFixed st inputs output
  match r with
  | .Err e => .ok (.Err e, s)
  | .Ok _ => .ok (.Ok a, s)

theorem carryFixed.segment {A : Type} (a : A) (st : code.OpIterState)
    (inputs : List wasm_types.ValueType) (output : Option wasm_types.ValueType)
    (outer segment : List code.StackType)
    (hv : st.vals.val = outer ++ segment) (hb : (Body.Control.base st).val = outer.length)
    (hsize : st.vals.val.length < Usize.max) :
    carryFixed a st inputs output ⦃ r => r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ∧
      ∃ after, r.2.vals.val = outer ++ after ∧ after.length ≤ segment.length + 1 ∧
        (∀ value, r.1 = .Ok value → value = a ∧
          FixedEffect (Body.Control.polymorphic st) segment inputs output after) ⦄ := by
  obtain ⟨⟨res, s⟩, hr, hc, hp, after, hv, hl, he⟩ := WP.spec_imp_exists
    (readFixed.segment st inputs output outer segment hv hb hsize)
  cases res with
  | Err e => simpa [carryFixed, hr] using ⟨hc, hp, after, hv, hl⟩
  | Ok u =>
    cases u
    simp only [carryFixed, hr, bind_ok]
    exact ⟨hc, hp, after, hv, hl, fun _ h => by cases h; exact ⟨rfl, he rfl⟩⟩

theorem carryFixed.complete {A : Type} (a : A) (st : code.OpIterState)
    (inputs : List wasm_types.ValueType) (output : Option wasm_types.ValueType)
    (outer segment : List code.StackType) (front : List valtype)
    (hv : st.vals.val = outer ++ segment) (hb : (Body.Control.base st).val = outer.length)
    (hsize : st.vals.val.length < Usize.max)
    (ht : Body.Stack.Realizes (Body.Control.polymorphic st) segment (front ++ inputTypes inputs)) :
    ∃ s after, carryFixed a st inputs output = .ok (.Ok a, s) ∧
      s.ctrls = st.ctrls ∧ s.pos = st.pos ∧ s.vals.val = outer ++ after ∧
      after.length ≤ segment.length + 1 ∧
      Body.Stack.Realizes (Body.Control.polymorphic st) after (front ++ outputTypes output) := by
  obtain ⟨s, after, hr, hc, hp, hv, hl, ht⟩ := readFixed.complete st inputs output
    outer segment front hv hb hsize ht
  exact ⟨s, after, by simp [carryFixed, hr], hc, hp, hv, hl, ht⟩

/-- Returning a decoded payload commutes with the visitor's fixed stack runner. -/
theorem carryFixed.run {A V : Type} (a : A) (st : code.OpIterState)
    (inputs : List wasm_types.ValueType) (output : Option wasm_types.ValueType)
    (hook : V → code.OpIterState → A → Result (core.result.Result Unit error.VisitError × V))
    (v : V) :
    Visitor.Core.run (carryFixed a st inputs output) hook v =
      Visitor.Core.run (readFixed st inputs output) (fun v s _ => hook v s a) v := by
  simp only [carryFixed, Visitor.Core.run, Std.bind_assoc, Std.uncurry]
  congr 1
  funext pair
  obtain ⟨r, s⟩ := pair
  cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

end Itasca.Body.Simd

end

/-! ## Operands -/

section

/-!
# Operand types of SIMD signatures

Gives the popped and pushed value types of each pure SIMD `Signature` and shows that the
extracted `code.read_simd_signature` equals `readFixed` at those types (`signature_fixed`).
-/

open Aeneas Aeneas.Std

namespace Itasca.Body.Simd

/-- Operand types popped by a pure SIMD signature, listed from the top of the stack. -/
def Signature.popTypes : Signature → List wasm_types.ValueType
  | .unary | .test => [.V128]
  | .binary => [.V128, .V128]
  | .ternary => [.V128, .V128, .V128]
  | .shift => [.I32, .V128]
  | .splatI32 => [.I32]
  | .splatI64 => [.I64]
  | .splatF32 => [.F32]
  | .splatF64 => [.F64]

/-- Result type pushed by a pure SIMD signature. -/
def Signature.output : Signature → wasm_types.ValueType
  | .test => .I32
  | _ => .V128

theorem Signature.inputs_pop (sig : Signature) : inputTypes sig.popTypes = sig.inputs := by
  cases sig <;> rfl

theorem Signature.outputs_pop (sig : Signature) : outputTypes (some sig.output) = sig.outputs := by
  cases sig <;> rfl

theorem conversion_fixed (st : code.OpIterState) (input output : wasm_types.ValueType) :
    code.read_conversion st input output = readFixed st [input] (some output) := by
  simp only [code.read_conversion, readFixed]
  congr 1
  funext pair
  obtain ⟨res, s⟩ := pair
  cases res <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

theorem binary_fixed (st : code.OpIterState) (input output : wasm_types.ValueType) :
    code.read_binary st input output = readFixed st [input, input] (some output) := by
  simp only [code.read_binary, readFixed]
  congr 1
  funext pair
  obtain ⟨res, s⟩ := pair
  cases res <;> simp only [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, bind_ok, Std.uncurry, core.convert.FromSame.from]
  · congr 1
    funext pair
    obtain ⟨res, s⟩ := pair
    cases res <;> simp
  · simp

/-- The extracted SIMD operand checker is the independently normalized fixed checker. -/
theorem signature_fixed (st : code.OpIterState) (sig : Signature) :
    code.read_simd_signature st sig.runtime = readFixed st sig.popTypes (some sig.output) := by
  cases sig <;> simp only [Signature.runtime, Signature.popTypes, Signature.output,
    code.read_simd_signature]
  all_goals first | exact conversion_fixed .. | exact binary_fixed .. | skip
  all_goals simp only [readFixed]
  all_goals congr 1; funext pair; obtain ⟨res, s⟩ := pair
  all_goals cases res <;> simp only [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, bind_ok, Std.uncurry, core.convert.FromSame.from]
  all_goals first | exact conversion_fixed .. | exact binary_fixed .. | simp

end Itasca.Body.Simd

end

/-! ## LaneReaders -/

section

/-!
# Lane reader factorization

`laneReader` is a lane-index decode followed by `carryFixed`, and `lane_fixed` shows that the
extracted `code.read_simd_lane` equals it. `laneInputs` and `laneOutput` give the stack effect of
extract and replace lane operations.
-/

open Aeneas Aeneas.Std

namespace Itasca.Body.Simd

theorem carryFixed.cons {A : Type} (a : A) (st : code.OpIterState) (ty : wasm_types.ValueType)
    (rest : List wasm_types.ValueType) (output : Option wasm_types.ValueType) :
    carryFixed a st (ty :: rest) output = (do
      let (r, s) ← code.pop_with_type st ty
      match r with
      | .Err e => .ok (.Err e, s)
      | .Ok _ => carryFixed a s rest output) := by
  simp only [carryFixed, readFixed, Std.bind_assoc, Std.uncurry]
  congr 1
  funext pair
  obtain ⟨r, s⟩ := pair
  cases r <;> simp

/-- Operand types of a lane operation: a vector, preceded by the replacement scalar if any. -/
def laneInputs (ty : wasm_types.ValueType) (replace : Bool) : List wasm_types.ValueType :=
  if replace then [ty, .V128] else [.V128]

/-- Result type of a lane operation: a vector when replacing, otherwise the scalar. -/
def laneOutput (ty : wasm_types.ValueType) (replace : Bool) : Option wasm_types.ValueType :=
  if replace then some .V128 else some ty

/-- Reads a lane index below `count` and applies the lane operation's stack effect. -/
def laneReader (st : code.OpIterState) (data : Slice U8)
    (ty : wasm_types.ValueType) (count : U8) (replace : Bool) :
    Result (core.result.Result U8 error.OpError × code.OpIterState) := do
  let (r, s) ← code.take_simd_lane st data count
  match r with
  | .Err e => .ok (.Err e, s)
  | .Ok lane => carryFixed lane s (laneInputs ty replace) (laneOutput ty replace)

theorem lane_fixed (st : code.OpIterState) (data : Slice U8)
    (ty : wasm_types.ValueType) (count : U8) (replace : Bool) :
    code.read_simd_lane st data ty count replace = laneReader st data ty count replace := by
  unfold code.read_simd_lane laneReader
  congr 1
  funext pair
  obtain ⟨r, s⟩ := pair
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok lane =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Std.uncurry]
    cases replace with
    | false =>
      simp only [Bool.false_eq_true, if_false, laneInputs, laneOutput]
      rw [conversion_fixed]
      unfold carryFixed
      congr 1
      funext pair
      obtain ⟨r, s⟩ := pair
      cases r <;> simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | true =>
      simp only [if_true, laneInputs, laneOutput]
      rw [carryFixed.cons]
      congr 1
      funext pair
      obtain ⟨r, s⟩ := pair
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok value =>
        simp only [bind_ok, Std.uncurry]
        rw [conversion_fixed]
        unfold carryFixed
        congr 1
        funext pair
        obtain ⟨r, s⟩ := pair
        cases r <;> simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

theorem LaneOperation.inputs_pop (op : LaneOperation) :
    inputTypes (laneInputs op.runtime.1 op.replace) = op.inputs := by cases op <;> rfl

theorem LaneOperation.outputs_pop (op : LaneOperation) :
    outputTypes (laneOutput op.runtime.1 op.replace) = op.outputs := by cases op <;> rfl

end Itasca.Body.Simd

end

end

/-! ## Visitor -/

section

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

namespace Itasca.Body.Simd

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
def fullMemoryReader (st : code.OpIterState) (data : Slice U8) (env : metadata.CodeMetadata)
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

theorem full_memory_fixed (st : code.OpIterState) (data : Slice U8) (env : metadata.CodeMetadata)
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
def memoryLaneReader (st : code.OpIterState) (data : Slice U8) (env : metadata.CodeMetadata)
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

theorem memory_lane_fixed (st : code.OpIterState) (data : Slice U8) (env : metadata.CodeMetadata)
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

end Itasca.Body.Simd

open Aeneas Aeneas.Std

namespace Itasca.Body.Simd

theorem MemoryOperation.conditions (op : MemoryOperation) (C : context)
    (arg : code.MemArg) (lane : U8) (ins outs : List valtype)
    (ht : Instr_ok C (op.instruction (Body.MemoryMeaning.memArg arg) (.mk_uN lane.val))
      (.mk_functype (.mk_list ins) (.mk_list outs))) :
    0 < C.MEMS.length ∧ arg.align.val ≤ op.naturalAlign ∧
      (op.laneCount ≠ 0 → lane.val < op.laneCount) := by
  have hp : 0 < C.MEMS.length ∧
      (2 : Rat) ^ arg.align.val ≤ 2 ^ op.naturalAlign ∧
      (op.laneCount ≠ 0 → lane.val < op.laneCount) := by
    cases op <;> simp only [instruction] at ht <;> cases ht
    all_goals refine ⟨by assumption, ?_, ?_⟩
    all_goals norm_num [naturalAlign, laneCount, WebAssembly.Binary.Simd.MemoryOperation.laneCount,
      Body.MemoryMeaning.memArg, proj_uN_0, size] at *
    all_goals norm_cast at *
  exact ⟨hp.1, (pow_le_pow_iff_right₀ (a := (2 : Rat)) (by norm_num)).mp hp.2.1, hp.2.2⟩

theorem MemoryOperation.typed_runtime (op : MemoryOperation) (C : context)
    (env : metadata.CodeMetadata) (ctx : code.Context) (hC : wf_context C)
    (hm : Translation.Environment.Matches env ctx C) (arg : code.MemArg) (lane : U8)
    (hmem : 0 < env.memories.val.length) (ha : arg.align.val ≤ op.naturalAlign)
    (hl : op.laneCount ≠ 0 → lane.val < op.laneCount) :
    Instr_ok C (op.instruction (Body.MemoryMeaning.memArg arg) (.mk_uN lane.val))
      (.mk_functype (.mk_list op.inputs) (.mk_list op.outputs)) := by
  have hlen : 0 < C.MEMS.length := by simpa [hm.mems] using hmem
  apply op.typed C (Body.MemoryMeaning.memArg arg) (.mk_uN lane.val) C.MEMS[0]!
    hlen rfl hC ?_ (Body.MemoryMeaning.mem_arg_wf arg) (by constructor; scalar_tac)
    (Body.MemoryMeaning.alignment_mono _ _ ha) hl
  rw [hm.mems]
  cases he : env.memories.val with
  | nil => simp [he] at hmem
  | cons mt rest => simpa [he] using Translation.Environment.mem_type_wf mt.ty

end Itasca.Body.Simd

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

namespace Itasca.Body.Simd

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
    (hfinish : ∀ bytes next, Body.Scalar.BytesAt data st.pos bytes next → bytes.length = 16 →
      (∀ b ∈ bytes, b.val < 32) → shuffleFinish st data ⦃ Q ⦄) :
    code.read_simd_shuffle st data ⦃ Q ⦄ := by
  unfold code.read_simd_shuffle code.read_simd_shuffle_loop
  apply loop.spec_decr_nat (fun p => (16 - p.2.val).toNat)
    (fun p => 0 ≤ p.2.val ∧ p.2.val ≤ 16 ∧ ∃ before : List U8,
      Body.Scalar.BytesAt data st.pos before p.1 ∧ before.length = p.2.val.toNat ∧
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
            hb.append (Body.Scalar.BytesAt.byte data pos next _ hp rfl hnext), ?_, ?_⟩, ?_⟩
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
    exact ⟨by decide, by decide, [], Body.Scalar.BytesAt.nil data st.pos hpos, by simp, by simp⟩

/-- Every independently valid shuffle immediate reaches the operand reader. -/
theorem shuffle_complete (st : code.OpIterState) (data : Slice U8)
    (bytes : List U8) (next : Usize) (hb : Body.Scalar.BytesAt data st.pos bytes next)
    (hl : bytes.length = 16) (hbound : ∀ b ∈ bytes, b.val < 32)
    (r : core.result.Result (U64 × U64) error.OpError × code.OpIterState)
    (hfinish : shuffleFinish st data = .ok r) :
    code.read_simd_shuffle st data = .ok r := by
  have hrun : code.read_simd_shuffle st data ⦃ result => result = r ⦄ := by
    unfold code.read_simd_shuffle code.read_simd_shuffle_loop
    apply loop.spec_decr_nat (fun p => (16 - p.2.val).toNat)
      (fun p => 0 ≤ p.2.val ∧ ∃ rest : List U8,
        Body.Scalar.BytesAt data p.1 rest next ∧ p.2.val + (rest.length : Int) = 16 ∧
        ∀ b ∈ rest, b.val < 32)
    · rintro ⟨pos, i⟩ ⟨hi, rest, hrest, hlen, hsmall⟩
      dsimp only at *
      by_cases hlt : i < 16#i32
      · cases rest with
        | nil => simp only [List.length_nil] at hlen; scalar_tac
        | cons b rest =>
          obtain ⟨middle, hb1, hb2⟩ := (show Body.Scalar.BytesAt data pos ([b] ++ rest) next from hrest).split
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
    (hb : (Body.Control.base st).val = outer.length) (hsize : st.vals.val.length < Usize.max)
    (hpos : st.pos.val ≤ data.length) :
    code.read_simd_shuffle st data ⦃ r => ∀ low high, r.1 = .Ok (low, high) →
      r.2.ctrls = st.ctrls ∧ ∃ after, r.2.vals.val = outer ++ after ∧
        BitsDecoded data st.pos low high r.2.pos ∧
        (∀ lane ∈ shuffleIndices low high, proj_uN_0 lane < 32) ∧
        FixedEffect (Body.Control.polymorphic st) segment [.V128, .V128] (some .V128) after ⦄ := by
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
        rw [shuffle_indices_encoding low high lower upper hlo hhi, hbytesEq]
        intro lane hm
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hm
        exact hbounds b hb
      apply WP.spec_mono (carryFixed.segment (low, high) decoded [.V128, .V128] (some .V128)
        outer segment (by simpa [hvals] using hv) (by simpa [Body.Control.base, hc] using hb)
        (by simpa [hvals] using hsize))
      rintro ⟨res, s⟩ ⟨hctrl, hposition, after, hstack, _, heffect⟩ lo hi hok
      dsimp only at hctrl hposition hstack heffect hok
      obtain ⟨heq, heff⟩ := heffect (lo, hi) hok
      cases heq
      refine ⟨hctrl.trans hc, after, hstack, ?_, hbounded, ?_⟩
      · simpa only [hposition] using hbits low high rfl
      · simpa only [Body.Control.polymorphic, hc] using heff

end Itasca.Body.Simd

end

/-! ## Visitor -/

section

/-!
# Visitor transfer for SIMD instructions

`simd_transfer` shows that if `code.step_simd` accepts with one visitor, it accepts with any
replacement visitor whose callbacks accept, reaching the same reader state.
-/

open Aeneas Aeneas.Std

namespace Itasca.Body.Simd

private theorem sub_transfer {V W : Type} (visitor : code.OpVisitor V)
    (replacement : code.OpVisitor W) (ha : Visitor.Accepts replacement)
    (st final : code.OpIterState) (data : Slice U8) (env : metadata.CodeMetadata)
    (subopcode : U32) (v v' : V) (w : W)
    (h : subStep visitor st data env subopcode v = .ok (.Ok (), final, v')) :
    ∃ w', subStep replacement st data env subopcode w = .ok (.Ok (), final, w') := by
  unfold subStep at h ⊢
  rw [pure_table] at h ⊢
  cases hm : pureMeaning subopcode.val with
  | some op =>
    simp only [hm, Option.map_some, bind_ok] at h ⊢
    exact Visitor.Core.run.accepted_lift _ _ _ v w final v' h (fun _ => ha.on_simd w final subopcode)
  | none =>
    simp only [hm, Option.map_none, bind_ok] at h ⊢
    rw [lane_table] at h ⊢
    cases hl : laneMeaning subopcode.val with
    | some lane =>
      simp only [hl, Option.map_some, bind_ok] at h ⊢
      rcases he : lane.runtime with ⟨ty, count, replace⟩
      simp only [he] at h ⊢
      exact Visitor.Core.run.accepted_lift _ _ _ v w final v' h
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
          exact Visitor.Core.run.accepted_lift _ _ _ v w final v' h
            (fun a => ha.on_simd_memory_lane w final subopcode a.1 a.2)
        · rename_i hc
          simp only [hc]
          cases store <;> simp only [Bool.false_eq_true, if_true, if_false] at h ⊢
          all_goals exact Visitor.Core.run.accepted_lift _ _ _ v w final v' h (fun a => ha.on_simd_memory w final subopcode a)
      | none =>
        simp only [hm, Option.map_none, bind_ok] at h ⊢
        split at h
        · exact Visitor.Core.run.accepted_lift _ _ _ v w final v' h
            (fun a => ha.on_simd_const w final a.1 a.2)
        · exact Visitor.Core.run.accepted_lift _ _ _ v w final v' h
            (fun a => ha.on_simd_shuffle w final a.1 a.2)
        · simp at h

/-- Accepting hooks preserve every successful SIMD state and immediate. -/
theorem simd_transfer {V W : Type} (visitor : code.OpVisitor V)
    (replacement : code.OpVisitor W) (ha : Visitor.Accepts replacement)
    (st final : code.OpIterState) (data : Slice U8) (env : metadata.CodeMetadata)
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

end Itasca.Body.Simd

end

end
