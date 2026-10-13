import Itasca.Wasm2.Simd.LaneReaders

open Aeneas Aeneas.Std

namespace Itasca.Wasm2.Simd

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

def fullMemoryInputs (store : Bool) : List types.ValueType :=
  if store then [.V128, .I32] else [.I32]

def memoryOutput (store : Bool) : Option types.ValueType :=
  if store then none else some .V128

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
  cases store <;> simp only [Bool.false_eq_true, Bool.true_eq, if_true, if_false,
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
      | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok u =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, carryFixed, readFixed,
          Std.bind_assoc, Std.uncurry, Bool.false_eq_true, Bool.true_eq, if_true, if_false]
        repeat' first
          | rfl
          | (congr 1
             funext pair
             obtain ⟨res, state⟩ := pair
             cases res <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
               core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
               readFixed, Std.bind_assoc])

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
    | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok lane =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Std.uncurry]
      congr 1
      funext r
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok u =>
        cases store <;> simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
          carryFixed, readFixed, memoryOutput, Std.bind_assoc, Std.uncurry,
          Bool.false_eq_true, Bool.true_eq, if_true, if_false]
        all_goals repeat' first
          | rfl
          | (congr 1
             funext pair
             obtain ⟨res, state⟩ := pair
             cases res <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
               core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
               readFixed, Std.bind_assoc])

theorem MemoryOperation.inputs_full (op : MemoryOperation) (h : op.laneCount = 0) :
    inputTypes (fullMemoryInputs op.store) = op.inputs := by cases op <;> first | rfl | contradiction

theorem MemoryOperation.inputs_lane (op : MemoryOperation) (h : op.laneCount ≠ 0) :
    inputTypes [.V128, .I32] = op.inputs := by cases op <;> first | rfl | contradiction

theorem MemoryOperation.outputs_pop (op : MemoryOperation) :
    outputTypes (memoryOutput op.store) = op.outputs := by cases op <;> rfl

end Itasca.Wasm2.Simd
