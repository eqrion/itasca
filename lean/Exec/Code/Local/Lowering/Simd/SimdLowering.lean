import Exec.Code.Local.Relations.Common.PairSuccess
import Exec.Code.Local.Relations.Common.StatefulSuccess
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Aeneas.Std.Result Itasca.ResultFacts
set_option maxRecDepth 4096

noncomputable def simdLowering {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (opcode : U16) (a : U32) (bits : U128) :
    Result (core.result.Result Unit Itasca.error.VisitError × runtime.compiler.FunctionCompiler A) := do
  let i ← opcode - 512#u16
  let sub ← lift (UScalar.cast .U32 i)
  let store ←
    if sub = 11#u32
    then ok true
    else if 88#u32 <= sub
    then ok (sub <= 91#u32)
    else ok false
  let outputs ← if store
                  then ok 0#usize
                  else ok 1#usize
  let i1 := alloc.vec.Vec.len before.before
  let o ← lift (Usize.checked_add i1 outputs)
  let r ←
    core.option.Option.ok_or o _root_.Itasca.error.VisitError.OutOfMemory
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let i2 := alloc.vec.Vec.len state.vals
    let o1 ← lift (Usize.checked_sub val i2)
    let r1 ←
      core.option.Option.ok_or o1
        _root_.Itasca.error.VisitError.OutOfMemory
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let r2 ←
        runtime.compiler.FunctionCompiler.operand ops before
          val1
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val2 =>
        let i3 := alloc.vec.Vec.len before.function.simd
        let r3 ← runtime.compiler.bounded_index i3
        let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue val3 =>
          let lane ←
            if 84#u32 <= sub
            then
              if sub <= 91#u32
              then ok (UScalar.cast .U32 bits)
              else ok a
            else ok a
          let (r4, b, v) ←
            runtime.compiler.Budget.push ops before.budget
              before.function.simd ({ offset := a, lane, bits } :
              _root_.Itasca.runtime.bytecode.SimdImmediate)
          let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
          match cf4 with
          | core.ops.control_flow.ControlFlow.Continue _ =>
            let o2 ←
              runtime.bytecode.Instr.make_simd sub val2 val2 val3
            let r5 ←
              core.option.Option.ok_or o2
                _root_.Itasca.error.VisitError.OutOfMemory
            let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r5
            match cf5 with
            | core.ops.control_flow.ControlFlow.Continue val4 =>
              let (r6, before1) ←
                runtime.compiler.FunctionCompiler.emit ops
                  {
                    before
                      with
                      budget := b,
                      function := { before.function with simd := v }
                  } val4
              let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r6
              match cf6 with
              | core.ops.control_flow.ControlFlow.Continue _ =>
                runtime.compiler.FunctionCompiler.observe
                  ops before1 state
              | core.ops.control_flow.ControlFlow.Break residual =>
                let r7 ←
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                    Unit (core.convert.FromSame
                    _root_.Itasca.error.VisitError) residual
                ok (r7, before1)
            | core.ops.control_flow.ControlFlow.Break residual =>
              let r6 ←
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                  Unit (core.convert.FromSame
                  _root_.Itasca.error.VisitError) residual
              ok (r6,
                {
                  before
                    with
                    budget := b,
                    function := { before.function with simd := v }
                })
          | core.ops.control_flow.ControlFlow.Break residual =>
            let r5 ←
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                Unit (core.convert.FromSame
                _root_.Itasca.error.VisitError) residual
            ok (r5,
              {
                before
                  with
                  budget := b,
                  function := { before.function with simd := v }
              })
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r4 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
              residual
          ok (r4, before)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r3 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
            residual
        ok (r3, before)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r2 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
          residual
      ok (r2, before)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
        residual
    ok (r1, before)

theorem compiler_simd_nonconstant_eq {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (opcode : U16) (a : U32) (bits : U128)
    (notConstant : opcode ≠ 524#u16) (lower : 512 ≤ opcode.val) (upper : opcode.val ≤ 767) :
    runtime.compiler.simd.FunctionCompiler.simd_op ops before state opcode a bits =
      simdLowering ops before state opcode a bits := by
  unfold runtime.compiler.simd.FunctionCompiler.simd_op
  split
  · contradiction
  · have lo : 512#u16 ≤ opcode := by scalar_tac
    have hi : opcode ≤ 767#u16 := by scalar_tac
    rw [if_pos lo,if_pos hi]
    rfl

end Itasca.Runtime.Code
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Aeneas.Std.Result Itasca.ResultFacts

def simdStores (sub : U32) : Bool :=
  if sub = 11#u32 then true else if 88#u32 ≤ sub then sub ≤ 91#u32 else false

def simdLane (sub a : U32) (bits : U128) : U32 :=
  if 84#u32 ≤ sub then if sub ≤ 91#u32 then UScalar.cast .U32 bits else a else a

def simdImmediate (sub a : U32) (bits : U128) : runtime.bytecode.SimdImmediate :=
  {offset := a,lane := simdLane sub a bits,bits}

theorem simd_stores_eq (sub : U32) :
    (if sub = 11#u32 then Result.ok true else if 88#u32 ≤ sub then Result.ok (decide (sub ≤ 91#u32)) else Result.ok false) =
      Result.ok (simdStores sub) := by unfold simdStores; split_ifs <;> rfl

theorem simd_lane_eq (sub a : U32) (bits : U128) :
    (if 84#u32 ≤ sub then if sub ≤ 91#u32 then Result.ok (UScalar.cast .U32 bits) else Result.ok a else Result.ok a) =
      Result.ok (simdLane sub a bits) := by unfold simdLane; split_ifs <;> rfl

theorem simd_outputs_eq (sub : U32) :
    (if simdStores sub then Result.ok 0#usize else Result.ok 1#usize) =
      Result.ok (if simdStores sub then 0#usize else 1#usize) := by split <;> rfl

end Itasca.Runtime.Code
