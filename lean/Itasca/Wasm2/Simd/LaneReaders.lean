import Itasca.Wasm2.Simd.Operands
import Itasca.Wasm2.Simd.Carry

/-!
# Lane reader factorization

`laneReader` is a lane-index decode followed by `carryFixed`, and `lane_fixed` shows that the
extracted `code.read_simd_lane` equals it. `laneInputs` and `laneOutput` give the stack effect of
extract and replace lane operations.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2.Simd

theorem carryFixed.cons {A : Type} (a : A) (st : code.OpIterState) (ty : types.ValueType)
    (rest : List types.ValueType) (output : Option types.ValueType) :
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
def laneInputs (ty : types.ValueType) (replace : Bool) : List types.ValueType :=
  if replace then [ty, .V128] else [.V128]

/-- Result type of a lane operation: a vector when replacing, otherwise the scalar. -/
def laneOutput (ty : types.ValueType) (replace : Bool) : Option types.ValueType :=
  if replace then some .V128 else some ty

/-- Reads a lane index below `count` and applies the lane operation's stack effect. -/
def laneReader (st : code.OpIterState) (data : Slice U8)
    (ty : types.ValueType) (count : U8) (replace : Bool) :
    Result (core.result.Result U8 error.OpError × code.OpIterState) := do
  let (r, s) ← code.take_simd_lane st data count
  match r with
  | .Err e => .ok (.Err e, s)
  | .Ok lane => carryFixed lane s (laneInputs ty replace) (laneOutput ty replace)

theorem lane_fixed (st : code.OpIterState) (data : Slice U8)
    (ty : types.ValueType) (count : U8) (replace : Bool) :
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
