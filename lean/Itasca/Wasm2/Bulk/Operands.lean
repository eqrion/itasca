import Itasca.Wasm2.References.Operands

open Aeneas Aeneas.Std

noncomputable section

local instance : DecidableEq Itasca.types.ValueType := Classical.decEq _

namespace Itasca.Wasm2

/-- Read a data-segment index and the reserved memory-zero byte before operands. -/
def memoryInitMetadata (st : code.OpIterState) (data : Slice U8) (env : module.Env) :
    Result (core.result.Result U32 error.OpError × code.OpIterState) := do
  let (r, s) ← code.take_data_index st data env
  match r with
  | .Err e => .ok (.Err e, s)
  | .Ok idx =>
    let (r, out) ← code.read_bulk_memory s data env
    match r with
    | .Err e => .ok (.Err e, out)
    | .Ok () => .ok (.Ok idx, out)

/-- Core 2 memory.copy uses two reserved literal memory-zero bytes. -/
def memoryCopyMetadata (st : code.OpIterState) (data : Slice U8) (env : module.Env) :
    Result (core.result.Result Unit error.OpError × code.OpIterState) := do
  let (r, s) ← code.read_bulk_memory st data env
  match r with
  | .Err e => .ok (.Err e, s)
  | .Ok () => code.read_reserved_zero s data

/-- Both table.copy and table.init compare the actual resolved reference types. -/
def referencePairMetadata
    (first : Result (core.result.Result (U32 × types.ValueType) error.OpError × code.OpIterState))
    (data : Slice U8) (env : module.Env) :
    Result (core.result.Result (U32 × U32) error.OpError × code.OpIterState) := do
  let (r, s) ← first
  match r with
  | .Err e => .ok (.Err e, s)
  | .Ok (firstIdx, firstTy) =>
    let (r, out) ← code.take_table s data env
    match r with
    | .Err e => .ok (.Err e, out)
    | .Ok (secondIdx, secondTy) =>
      if firstTy = secondTy then .ok (.Ok (firstIdx, secondIdx), out)
      else .ok (.Err .TypeMismatch, out)

end Itasca.Wasm2

namespace Itasca

theorem types.ValueType.ne.eq (a b : types.ValueType) :
    core.cmp.PartialEq.ne.trait_default types.ValueType.Insts.CoreCmpPartialEqValueType a b =
      .ok (decide (a ≠ b)) := by
  cases a <;> cases b <;> simp [core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
    types.ValueType.Insts.CoreCmpPartialEqValueType.eq]

theorem code.read_bulk_operands.fixed (st : code.OpIterState) :
    code.read_bulk_operands st = Wasm2.Simd.readFixed st [.I32, .I32, .I32] none := by
  simp only [code.read_bulk_operands, Wasm2.Simd.readFixed]
  repeat' first
    | rfl
    | (congr 1
       funext pair
       obtain ⟨res, state⟩ := pair
       cases res <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
         core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
         Wasm2.Simd.readFixed, Std.bind_assoc])

theorem code.read_memory_fill.fixed (st : code.OpIterState) (data : Slice U8) (env : module.Env) :
    code.read_memory_fill st data env = Wasm2.metadataOperands (code.read_bulk_memory st data env)
      (fun _ => [.I32, .I32, .I32]) (fun _ => none) id := by
  simp only [code.read_memory_fill, Wasm2.metadataOperands, 
    code.read_bulk_operands.fixed, Std.bind_assoc]
  repeat' first
    | rfl
    | (congr 1
       funext pair
       obtain ⟨res, state⟩ := pair
       cases res <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
         core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
         Wasm2.Simd.readFixed, Std.bind_assoc, Std.uncurry])
    | (rename_i a; cases (show U32 × types.ValueType from a))
    | (simp only [types.ValueType.ne.eq, bind_ok]; split <;> simp_all)

theorem code.read_memory_init.fixed (st : code.OpIterState) (data : Slice U8) (env : module.Env) :
    code.read_memory_init st data env = Wasm2.metadataOperands (Wasm2.memoryInitMetadata st data env)
      (fun _ => [.I32, .I32, .I32]) (fun _ => none) id := by
  simp only [code.read_memory_init, Wasm2.metadataOperands, Wasm2.memoryInitMetadata,
    code.read_bulk_operands.fixed, Std.bind_assoc]
  repeat' first
    | rfl
    | (congr 1
       funext pair
       obtain ⟨res, state⟩ := pair
       cases res <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
         core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
         Wasm2.Simd.readFixed, Std.bind_assoc, Std.uncurry])
    | (rename_i a; cases (show U32 × types.ValueType from a))
    | (simp only [types.ValueType.ne.eq, bind_ok]; split <;> simp_all)

theorem code.read_memory_copy.fixed (st : code.OpIterState) (data : Slice U8) (env : module.Env) :
    code.read_memory_copy st data env = Wasm2.metadataOperands (Wasm2.memoryCopyMetadata st data env)
      (fun _ => [.I32, .I32, .I32]) (fun _ => none) id := by
  simp only [code.read_memory_copy, Wasm2.metadataOperands, Wasm2.memoryCopyMetadata,
    code.read_bulk_operands.fixed, Std.bind_assoc]
  repeat' first
    | rfl
    | (congr 1
       funext pair
       obtain ⟨res, state⟩ := pair
       cases res <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
         core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
         Wasm2.Simd.readFixed, Std.bind_assoc, Std.uncurry])
    | (rename_i a; cases (show U32 × types.ValueType from a))
    | (simp only [types.ValueType.ne.eq, bind_ok]; split <;> simp_all)

theorem code.read_table_init.fixed (st : code.OpIterState) (data : Slice U8) (env : module.Env) :
    code.read_table_init st data env = Wasm2.metadataOperands (Wasm2.referencePairMetadata (code.take_element st data env) data env)
      (fun _ => [.I32, .I32, .I32]) (fun _ => none) id := by
  simp only [code.read_table_init, Wasm2.metadataOperands, Wasm2.referencePairMetadata,
    code.read_bulk_operands.fixed, Std.bind_assoc]
  repeat' first
    | rfl
    | (congr 1
       funext pair
       obtain ⟨res, state⟩ := pair
       cases res <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
         core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
         Wasm2.Simd.readFixed, Std.bind_assoc, Std.uncurry])
    | (rename_i a; cases (show U32 × types.ValueType from a))
    | (simp only [types.ValueType.ne.eq, bind_ok]; split <;> simp_all)

theorem code.read_table_copy.fixed (st : code.OpIterState) (data : Slice U8) (env : module.Env) :
    code.read_table_copy st data env = Wasm2.metadataOperands (Wasm2.referencePairMetadata (code.take_table st data env) data env)
      (fun _ => [.I32, .I32, .I32]) (fun _ => none) id := by
  simp only [code.read_table_copy, Wasm2.metadataOperands, Wasm2.referencePairMetadata,
    code.read_bulk_operands.fixed, Std.bind_assoc]
  repeat' first
    | rfl
    | (congr 1
       funext pair
       obtain ⟨res, state⟩ := pair
       cases res <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
         core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
         Wasm2.Simd.readFixed, Std.bind_assoc, Std.uncurry])
    | (rename_i a; cases (show U32 × types.ValueType from a))
    | (simp only [types.ValueType.ne.eq, bind_ok]; split <;> simp_all)

end Itasca
