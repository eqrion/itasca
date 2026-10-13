import Itasca.Wasm2.Simd.LaneReaders
import Itasca.Binary.Wasm1.MemoryTyping

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
def fullMemoryInputs (store : Bool) : List types.ValueType :=
  if store then [.V128, .I32] else [.I32]

/-- Result type of a `v128` memory operation: nothing for stores, a vector otherwise. -/
def memoryOutput (store : Bool) : Option types.ValueType :=
  if store then none else some .V128

/-- Reads a memory argument, checks that memory zero exists and the alignment bound, then applies
the operand effect of a full-width `v128` load or store. -/
def fullMemoryReader (st : code.OpIterState) (data : Slice U8) (env : module.Env)
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

theorem full_memory_fixed (st : code.OpIterState) (data : Slice U8) (env : module.Env)
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
def memoryLaneReader (st : code.OpIterState) (data : Slice U8) (env : module.Env)
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

theorem memory_lane_fixed (st : code.OpIterState) (data : Slice U8) (env : module.Env)
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
    (env : module.Env) (ctx : code.Context) (hC : wf_context C)
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
