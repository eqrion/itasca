import Itasca.Wasm2.Scalar.Env
import Itasca.Visitor.Accepts
import Itasca.Binary.Wasm2.SyntaxUnique
import Mathlib.Tactic.IntervalCases
import Itasca.Visitor.Total
import Itasca.Binary.Wasm1.EncodingComplete
import Itasca.Wasm2.SuffixTyping

/-!
Sections, each formerly its own module: ReadersTotal, Tables, Dispatch, DispatchTotal, Decode, Carry, Operands, LaneReaders.
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

namespace Itasca.Wasm2.Simd

def ReaderPost (st s : code.OpIterState) : Prop :=
  Control.Shape s ∧ s.ctrls = st.ctrls ∧ st.pos.val ≤ s.pos.val ∧
    s.vals.val.length ≤ st.vals.val.length + 1

attribute [local step] code.pop_with_type.total code.pop_stack_type.total
  code.push_val.shape_total ScalarReaders.memarg code.check_memory_and_alignment.spec

@[local step] private theorem conversion_total (st : code.OpIterState) (input output : wasm_types.ValueType)
    (hs : Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
    code.read_conversion st input output ⦃ r => ReaderPost st r.2 ⦄ := by
  unfold code.read_conversion ReaderPost
  step*

@[local step] private theorem binary_total (st : code.OpIterState) (input output : wasm_types.ValueType)
    (hs : Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
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

@[step] theorem take_bits_total (st : code.OpIterState) (data : Slice U8) (hs : Control.Shape st) :
    code.take_simd_bits st data ⦃ r => Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
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
    (hs : Control.Shape st) :
    code.take_simd_lane st data count ⦃ r => Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
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
    (hs : Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
    code.read_simd_signature st sig ⦃ r => ReaderPost st r.2 ⦄ := by
  cases sig <;> unfold code.read_simd_signature
  all_goals step* <;> simp_all [ReaderPost] <;> omega

@[step] theorem read_lane_total (st : code.OpIterState) (data : Slice U8)
    (ty : wasm_types.ValueType) (count : U8) (replace : Bool)
    (hs : Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
    code.read_simd_lane st data ty count replace ⦃ r => ReaderPost st r.2 ⦄ := by
  unfold code.read_simd_lane ReaderPost
  step* <;> simp_all [ReaderPost] <;> omega

@[step] theorem memory_lane_total (st : code.OpIterState) (data : Slice U8) (env : metadata.Env)
    (alignment : U32) (store : Bool) (count : U8)
    (hs : Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
    code.read_simd_memory_lane st data env alignment store count ⦃ r => ReaderPost st r.2 ⦄ := by
  unfold code.read_simd_memory_lane ReaderPost
  step*

@[step] theorem load_total (st : code.OpIterState) (data : Slice U8) (env : metadata.Env)
    (ty : wasm_types.ValueType) (alignment : U32)
    (hs : Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
    code.read_load st data env ty alignment ⦃ r => ReaderPost st r.2 ⦄ := by
  unfold code.read_load ReaderPost
  step*

@[step] theorem store_total (st : code.OpIterState) (data : Slice U8) (env : metadata.Env)
    (ty : wasm_types.ValueType) (alignment : U32)
    (hs : Control.Shape st) :
    code.read_store st data env ty alignment ⦃ r => ReaderPost st r.2 ⦄ := by
  unfold code.read_store ReaderPost
  step*

@[step] theorem constant_total (st : code.OpIterState) (data : Slice U8)
    (hs : Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
    code.read_simd_const st data ⦃ r => ReaderPost st r.2 ⦄ := by
  unfold code.read_simd_const ReaderPost
  step*

@[local step] private theorem shuffle_loop_total (st : code.OpIterState) (data : Slice U8)
    (pos : Usize) (i : I32) (hi : 0 ≤ i.val ∧ i.val ≤ 16)
    (hs : Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
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
    (hs : Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
    code.read_simd_shuffle st data ⦃ r => ReaderPost st r.2 ⦄ :=
  shuffle_loop_total st data st.pos 0#i32 (by decide) hs hsize

end Itasca.Wasm2.Simd

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

namespace Itasca.Wasm2.Simd

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

end Itasca.Wasm2.Simd

open Aeneas Aeneas.Std

namespace Itasca.Wasm2.Simd

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

end Itasca.Wasm2.Simd

end

/-! ## Dispatch -/

section

/-!
# Dispatch of SIMD instructions

`Simd.prefixStep` and `Simd.subStep` unfold the extracted `code.step_simd` (opcode `0xFD`) into
`CoreVisitor.run` applied to the reader for each operation class. `code.step_simd.eq_runs` proves
the two equal, and the `subStep.*` equations specialize it to pure, lane, memory, memory lane,
constant and shuffle subopcodes using the table agreement of `Wasm2/Simd/Tables`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2.Simd

/-- Factorization of the SIMD subopcode dispatcher around its readers and visitor callbacks. -/
def subStep {V : Type} (visitor : code.OpVisitor V) (st : code.OpIterState)
    (data : Slice U8) (env : metadata.Env) (subopcode : U32) (v : V) :
    Result (core.result.Result Unit error.OpError × code.OpIterState × V) := do
  let sig ← code.simd_signature subopcode
  match sig with
  | some sig =>
    CoreVisitor.run (code.read_simd_signature st sig)
      (fun v s _ => visitor.on_simd v s subopcode) v
  | none =>
    let lane ← code.simd_lane_info subopcode
    match lane with
    | some (ty, count, replace) =>
      CoreVisitor.run (code.read_simd_lane st data ty count replace)
        (fun v s lane => visitor.on_simd_lane v s subopcode lane) v
    | none =>
      let memory ← code.simd_memory_info subopcode
      match memory with
      | some (align, store, count) =>
        if count != 0#u8 then
          CoreVisitor.run (code.read_simd_memory_lane st data env align store count)
            (fun v s a => visitor.on_simd_memory_lane v s subopcode a.1 a.2) v
        else if store then
          CoreVisitor.run (code.read_store st data env .V128 align)
            (fun v s arg => visitor.on_simd_memory v s subopcode arg) v
        else
          CoreVisitor.run (code.read_load st data env .V128 align)
            (fun v s arg => visitor.on_simd_memory v s subopcode arg) v
      | none =>
        match subopcode with
        | 12#uscalar =>
          CoreVisitor.run (code.read_simd_const st data)
            (fun v s a => visitor.on_simd_const v s a.1 a.2) v
        | 13#uscalar =>
          CoreVisitor.run (code.read_simd_shuffle st data)
            (fun v s a => visitor.on_simd_shuffle v s a.1 a.2) v
        | _ => .ok (.Err .UnrecognizedOpcode, st, v)

/-- Reads the subopcode after `0xFD` and continues with `subStep`. -/
def prefixStep {V : Type} (visitor : code.OpVisitor V) (st : code.OpIterState)
    (data : Slice U8) (env : metadata.Env) (v : V) :
    Result (core.result.Result Unit error.OpError × code.OpIterState × V) := do
  let r ← reader.read_u32_leb data st.pos
  match r with
  | .Err e => .ok (.Err e, st, v)
  | .Ok (subopcode, next) => subStep visitor {st with pos := next} data env subopcode v

end Itasca.Wasm2.Simd

namespace Itasca

theorem code.step_wasm2.simd {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (v : V) :
    code.step_wasm2 visitor st data env ctx 0xFD#u8 v = code.step_simd visitor st data env v := rfl

macro "finish_simd_run" : tactic => `(tactic| (
  simp only [CoreVisitor.run]
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

/-- `code.step_simd` equals its unfolded form `Wasm2.Simd.prefixStep`. -/
theorem code.step_simd.eq_runs {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (v : V) :
    code.step_simd visitor st data env v = Wasm2.Simd.prefixStep visitor st data env v := by
  unfold code.step_simd Wasm2.Simd.prefixStep
  congr 1
  funext r
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
    obtain ⟨subopcode, next⟩ := pair
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Std.uncurry, Wasm2.Simd.subStep]
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

namespace Itasca.Wasm2.Simd

theorem subStep.pure {V : Type} (visitor : code.OpVisitor V) (st : code.OpIterState)
    (data : Slice U8) (env : metadata.Env) (opcode : U32) (v : V) (op : Operation)
    (h : pureMeaning opcode.val = some op) :
    subStep visitor st data env opcode v = CoreVisitor.run (code.read_simd_signature st op.signature.runtime)
      (fun v s _ => visitor.on_simd v s opcode) v := by
  simp only [subStep, pure_table, h, Option.map_some, bind_ok]

theorem subStep.lane {V : Type} (visitor : code.OpVisitor V) (st : code.OpIterState)
    (data : Slice U8) (env : metadata.Env) (opcode : U32) (v : V) (op : LaneOperation)
    (h : laneMeaning opcode.val = some op) :
    subStep visitor st data env opcode v = CoreVisitor.run
      (code.read_simd_lane st data op.runtime.1 op.runtime.2.1 op.replace)
      (fun v s a => visitor.on_simd_lane v s opcode a) v := by
  simp only [subStep, pure_table, lane_pure_none h, lane_table, h, Option.map_none,
    Option.map_some, bind_ok, LaneOperation.runtime]

theorem subStep.memory {V : Type} (visitor : code.OpVisitor V) (st : code.OpIterState)
    (data : Slice U8) (env : metadata.Env) (opcode : U32) (v : V) (op : MemoryOperation)
    (h : memoryMeaning opcode.val = some op) (hc : op.laneCount = 0) :
    subStep visitor st data env opcode v = CoreVisitor.run
      (if op.store then code.read_store st data env .V128 op.runtime.1
        else code.read_load st data env .V128 op.runtime.1)
      (fun v s a => visitor.on_simd_memory v s opcode a) v := by
  simp only [subStep, pure_table, memory_pure_none h, lane_table, memory_lane_none h,
    memory_table, h, Option.map_none, Option.map_some, bind_ok, MemoryOperation.runtime, hc]
  cases op.store <;> rfl

theorem subStep.memoryLane {V : Type} (visitor : code.OpVisitor V) (st : code.OpIterState)
    (data : Slice U8) (env : metadata.Env) (opcode : U32) (v : V) (op : MemoryOperation)
    (h : memoryMeaning opcode.val = some op) (hc : op.laneCount ≠ 0) :
    subStep visitor st data env opcode v = CoreVisitor.run
      (code.read_simd_memory_lane st data env op.runtime.1 op.store op.runtime.2.2)
      (fun v s a => visitor.on_simd_memory_lane v s opcode a.1 a.2) v := by
  simp only [subStep, pure_table, memory_pure_none h, lane_table, memory_lane_none h,
    memory_table, h, Option.map_none, Option.map_some, bind_ok, MemoryOperation.runtime]
  have hn : (U8.ofNatCore op.laneCount (by cases op <;> decide) != 0#u8) = true := by
    cases op <;> first | contradiction | rfl
  rw [if_pos hn]

theorem subStep.constant {V : Type} (visitor : code.OpVisitor V) (st : code.OpIterState)
    (data : Slice U8) (env : metadata.Env) (v : V) :
    subStep visitor st data env 12#u32 v = CoreVisitor.run (code.read_simd_const st data)
      (fun v s a => visitor.on_simd_const v s a.1 a.2) v := by
  have hp : pureMeaning (12#u32).val = none := by with_unfolding_all rfl
  have hl : laneMeaning (12#u32).val = none := by with_unfolding_all rfl
  have hm : memoryMeaning (12#u32).val = none := by with_unfolding_all rfl
  simp only [subStep, pure_table, lane_table, memory_table, hp, hl, hm, Option.map_none, bind_ok]
  with_unfolding_all rfl

theorem subStep.shuffle {V : Type} (visitor : code.OpVisitor V) (st : code.OpIterState)
    (data : Slice U8) (env : metadata.Env) (v : V) :
    subStep visitor st data env 13#u32 v = CoreVisitor.run (code.read_simd_shuffle st data)
      (fun v s a => visitor.on_simd_shuffle v s a.1 a.2) v := by
  have hp : pureMeaning (13#u32).val = none := by with_unfolding_all rfl
  have hl : laneMeaning (13#u32).val = none := by with_unfolding_all rfl
  have hm : memoryMeaning (13#u32).val = none := by with_unfolding_all rfl
  simp only [subStep, pure_table, lane_table, memory_table, hp, hl, hm, Option.map_none, bind_ok]
  with_unfolding_all rfl

end Itasca.Wasm2.Simd

end

/-! ## DispatchTotal -/

section

/-!
# Totality of the SIMD dispatcher

`simd_total` shows that the extracted `code.step_simd` never panics under a total visitor, keeps
the control stack and moves the cursor forward, for every subopcode and immediate.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2.Simd

private theorem run_total {A V : Type}
    (read : Result (core.result.Result A error.OpError × code.OpIterState))
    (hook : V → code.OpIterState → A → Result (core.result.Result Unit error.VisitError × V))
    (v : V) (st : code.OpIterState)
    (hr : read ⦃ r => ReaderPost st r.2 ⦄)
    (hh : ∀ s a, ∃ res v', hook v s a = .ok (res, v')) :
    CoreVisitor.run read hook v ⦃ r => ReaderPost st r.2.1 ⦄ := by
  apply WP.spec_mono (CoreVisitor.run.spec read hook v (ReaderPost st) (fun _ _ => True) ?_ hh)
  · exact fun _ h => h.1
  · exact WP.spec_mono hr (fun _ h => ⟨h, by simp⟩)

theorem sub_total {V : Type} (visitor : code.OpVisitor V) (st : code.OpIterState)
    (data : Slice U8) (env : metadata.Env) (subopcode : U32) (v : V)
    (hs : Control.Shape st) (hsize : st.vals.val.length < Usize.max)
    (hv : FullVisitor.Total visitor) :
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
    (data : Slice U8) (env : metadata.Env) (v : V)
    (hs : Control.Shape st) (hsize : st.vals.val.length < Usize.max)
    (hv : FullVisitor.Total visitor) :
    code.step_simd visitor st data env v ⦃ r => Control.Shape r.2.1 ∧
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
    have hp := (Leb128.Decoded.span data st.pos subopcode next hd).1
    have hn : next.val ≤ r.2.1.pos.val := h.2.2.1
    exact ⟨h.1, h.2.1, by omega, h.2.2.2⟩

end Itasca.Wasm2.Simd

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

namespace Itasca.Wasm2.Simd

theorem state_of_stacks (s st : code.OpIterState) (hv : s.vals = st.vals) (hc : s.ctrls = st.ctrls) :
    s = {st with pos := s.pos} := by cases s; cases st; simp_all

/-- Accepted lane bytes satisfy their instruction-specific lane limit. -/
theorem take_lane_spec (st : code.OpIterState) (data : Slice U8) (count : U8) :
    code.take_simd_lane st data count ⦃ r => r.2.ctrls = st.ctrls ∧ r.2.vals = st.vals ∧
      (∀ lane, r.1 = .Ok lane → lane.val < count.val ∧
        Wasm1.BytesAt data st.pos [lane] r.2.pos) ⦄ := by
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
      exact ⟨by scalar_tac, Wasm1.BytesAt.byte data st.pos next _ hp rfl hn⟩
  · simp [code.take_simd_lane, reader.read_byte.eof data st.pos (by omega),
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

theorem take_lane_complete (st : code.OpIterState) (data : Slice U8) (count lane : U8)
    (next : Usize) (hb : Wasm1.BytesAt data st.pos [lane] next) (hl : lane.val < count.val) :
    code.take_simd_lane st data count = .ok (.Ok lane, {st with pos := next}) := by
  have hn : ¬ lane ≥ count := by scalar_tac
  simp [code.take_simd_lane, hb.read_byte, hl, core.result.Result.Insts.CoreOpsTry.branch]

/-- Sixteen accepted bytes split into their exact low and high words. -/
def BitsDecoded (data : Slice U8) (start : Usize) (low high : U64) (next : Usize) : Prop :=
  ∃ lower upper, FloatBits.Encoding 8 lower low.val ∧ FloatBits.Encoding 8 upper high.val ∧
    Wasm1.BytesAt data start (lower ++ upper) next

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
        (show Wasm1.BytesAt data st.pos lower middle from ⟨hls, by simpa [hle.1] using hll, hlb⟩).append
          ⟨hus, by simpa [hue.1] using hul, hub⟩⟩

theorem take_bits_complete (st : code.OpIterState) (data : Slice U8)
    (low high : U64) (lower upper : List U8) (next : Usize)
    (hl : FloatBits.Encoding 8 lower low.val) (hh : FloatBits.Encoding 8 upper high.val)
    (hb : Wasm1.BytesAt data st.pos (lower ++ upper) next) :
    code.take_simd_bits st data = .ok (.Ok (low, high), {st with pos := next}) := by
  obtain ⟨middle, hfirst, hlast⟩ := hb.split
  simp [code.take_simd_bits, hfirst.read_f64 low hl, hlast.read_f64 high hh,
    core.result.Result.Insts.CoreOpsTry.branch]

end Itasca.Wasm2.Simd

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

namespace Itasca.Wasm2.Simd

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
    (hv : st.vals.val = outer ++ segment) (hb : (Control.base st).val = outer.length)
    (hsize : st.vals.val.length < Usize.max) :
    carryFixed a st inputs output ⦃ r => r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ∧
      ∃ after, r.2.vals.val = outer ++ after ∧ after.length ≤ segment.length + 1 ∧
        (∀ value, r.1 = .Ok value → value = a ∧
          FixedEffect (Control.polymorphic st) segment inputs output after) ⦄ := by
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
    (hv : st.vals.val = outer ++ segment) (hb : (Control.base st).val = outer.length)
    (hsize : st.vals.val.length < Usize.max)
    (ht : Sequence.Realizes (Control.polymorphic st) segment (front ++ inputTypes inputs)) :
    ∃ s after, carryFixed a st inputs output = .ok (.Ok a, s) ∧
      s.ctrls = st.ctrls ∧ s.pos = st.pos ∧ s.vals.val = outer ++ after ∧
      after.length ≤ segment.length + 1 ∧
      Sequence.Realizes (Control.polymorphic st) after (front ++ outputTypes output) := by
  obtain ⟨s, after, hr, hc, hp, hv, hl, ht⟩ := readFixed.complete st inputs output
    outer segment front hv hb hsize ht
  exact ⟨s, after, by simp [carryFixed, hr], hc, hp, hv, hl, ht⟩

/-- Returning a decoded payload commutes with the visitor's fixed stack runner. -/
theorem carryFixed.run {A V : Type} (a : A) (st : code.OpIterState)
    (inputs : List wasm_types.ValueType) (output : Option wasm_types.ValueType)
    (hook : V → code.OpIterState → A → Result (core.result.Result Unit error.VisitError × V))
    (v : V) :
    CoreVisitor.run (carryFixed a st inputs output) hook v =
      CoreVisitor.run (readFixed st inputs output) (fun v s _ => hook v s a) v := by
  simp only [carryFixed, CoreVisitor.run, Std.bind_assoc, Std.uncurry]
  congr 1
  funext pair
  obtain ⟨r, s⟩ := pair
  cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]


end Itasca.Wasm2.Simd

end

/-! ## Operands -/

section

/-!
# Operand types of SIMD signatures

Gives the popped and pushed value types of each pure SIMD `Signature` and shows that the
extracted `code.read_simd_signature` equals `readFixed` at those types (`signature_fixed`).
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2.Simd

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

end Itasca.Wasm2.Simd

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

namespace Itasca.Wasm2.Simd

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

end Itasca.Wasm2.Simd

end
