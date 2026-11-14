import Mathlib.Tactic.IntervalCases
import Itasca.Runtime.Compiler.Local.Lowering.Emission.LoweringEmpty

/-! Canonical SIMD lowering contracts. The existing general-tail view and its
pure opcode helpers live beside their operational contracts. -/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Aeneas.Std.Result Itasca.ResultFacts

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


/-- The vector-constant arm publishes its pool entry and finishes one instruction. -/
theorem _root_.Itasca.runtime.compiler.simd.FunctionCompiler.simd_op.constant_eq {A : Type}
    (ops : runtime.platform.Alloc A) (before : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a : U32) (bits : U128) :
    runtime.compiler.simd.FunctionCompiler.simd_op ops before state 524#u16 a bits = (do
      let i := alloc.vec.Vec.len before.function.v128_pool
      let r ← runtime.compiler.bounded_index i
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val =>
        let (r1, b, v) ←
          runtime.compiler.Budget.push ops before.budget
            before.function.v128_pool bits
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          runtime.compiler.lower.FunctionCompiler.finish_op ops
            {before with budget := b, function := {before.function with v128_pool := v}}
            state (.ConstV128 before.height val)
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r2 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              Unit (core.convert.FromSame error.VisitError) residual
          ok (r2,
            {
              before
                with
                budget := b, function := { before.function with v128_pool := v }
            })
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r1 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame error.VisitError) residual
        ok (r1, before)) := by
  unfold runtime.compiler.simd.FunctionCompiler.simd_op
  split
  · rfl
  · contradiction

/-- Opcodes outside the SIMD range fail before changing compiler state. -/
theorem _root_.Itasca.runtime.compiler.simd.FunctionCompiler.simd_op.invalid_eq {A : Type}
    (ops : runtime.platform.Alloc A) (before : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (opcode : U16) (a : U32) (bits : U128)
    (outside : opcode.val < 512 ∨ 767 < opcode.val) :
    runtime.compiler.simd.FunctionCompiler.simd_op ops before state opcode a bits = .ok (.Err .OutOfMemory, before) := by
  have nonconstant : opcode ≠ 524#u16 := by
    intro same
    subst opcode
    rcases outside with low | high <;> scalar_tac
  unfold runtime.compiler.simd.FunctionCompiler.simd_op
  split
  · contradiction
  · by_cases lower : 512#u16 ≤ opcode
    · rw [if_pos lower]
      have upper : ¬ opcode ≤ 767#u16 := by
        rcases outside with low | high <;> scalar_tac
      rw [if_neg upper]
    · rw [if_neg lower]

/-- Pool publication followed by the existing emission/observation tail. -/
def SimdConstantEffect {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (bits : U128) (status : core.result.Result Unit Itasca.error.VisitError) : Prop :=
  ∃ answer, runtime.compiler.bounded_index (alloc.vec.Vec.len before.function.v128_pool) = .ok answer ∧
    match answer with
    | .Err error => status = .Err error ∧ after = before
    | .Ok entry => ∃ pushed budget values,
      runtime.compiler.Budget.push ops before.budget before.function.v128_pool bits = .ok (pushed, budget, values) ∧
      let staged := {before with budget, function := {before.function with v128_pool := values}}
      match pushed with
      | .Err error => status = .Err error ∧ after = staged
      | .Ok _ => runtime.compiler.lower.FunctionCompiler.finish_op ops staged state
          (.ConstV128 before.height entry) = .ok (status, after)

/-- Immediate publication and constructor choice retain their actual results. -/
def SimdAllocationEffect {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (sub a source : U32) (bits : U128) (status : core.result.Result Unit Itasca.error.VisitError) : Prop :=
  ∃ answer, runtime.compiler.bounded_index (alloc.vec.Vec.len before.function.simd) = .ok answer ∧
    match answer with
    | .Err error => status = .Err error ∧ after = before
    | .Ok entry => ∃ pushed budget values,
      runtime.compiler.Budget.push ops before.budget before.function.simd (simdImmediate sub a bits) = .ok (pushed, budget, values) ∧
      let staged := {before with budget, function := {before.function with simd := values}}
      match pushed with
      | .Err error => status = .Err error ∧ after = staged
      | .Ok _ => ∃ constructed, runtime.bytecode.Instr.make_simd sub source source entry = .ok constructed ∧
        match constructed with
        | none => status = .Err .OutOfMemory ∧ after = staged
        | some instruction => runtime.compiler.lower.FunctionCompiler.finish_op ops staged state instruction = .ok (status, after)

/-- Checked stack cardinalities determine the selected source operand before
immediate allocation; arithmetic and operand errors leave state unchanged. -/
def SimdOperandEffect {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (sub a : U32) (bits : U128) (status : core.result.Result Unit Itasca.error.VisitError) : Prop :=
  match Usize.checked_add (alloc.vec.Vec.len before.before) (if simdStores sub then 0#usize else 1#usize) with
  | none => status = .Err .OutOfMemory ∧ after = before
  | some total =>
    match Usize.checked_sub total (alloc.vec.Vec.len state.vals) with
    | none => status = .Err .OutOfMemory ∧ after = before
    | some consumed => ∃ answer, runtime.compiler.FunctionCompiler.operand ops before consumed = .ok answer ∧
      match answer with
      | .Err error => status = .Err error ∧ after = before
      | .Ok source => SimdAllocationEffect ops before after state sub a source bits status

/-- The general tail records opcode reduction before its staged effects. -/
def SimdLoweringEffect {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (opcode : U16) (a : U32) (bits : U128) (status : core.result.Result Unit Itasca.error.VisitError) : Prop :=
  ∃ reduced, (opcode - 512#u16 : Result U16) = .ok reduced ∧
    SimdOperandEffect ops before after state (UScalar.cast .U32 reduced) a bits status

/-- One inversion covers every arithmetic, allocation, and constructor exit. -/
theorem simdLowering.inv {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (opcode : U16) (a : U32) (bits : U128) (status : core.result.Result Unit Itasca.error.VisitError)
    (called : simdLowering ops before state opcode a bits = .ok (status, after)) :
    SimdLoweringEffect ops before after state opcode a bits status := by
  unfold simdLowering at called
  obtain ⟨reduced, number, rest⟩ := bind_ok_inv _ _ _ called
  refine ⟨reduced, number, ?_⟩
  simp only [lift, bind_ok, simd_stores_eq, simd_outputs_eq] at rest
  unfold SimdOperandEffect
  cases added : Usize.checked_add (alloc.vec.Vec.len before.before)
      (if simdStores (UScalar.cast .U32 reduced) then 0#usize else 1#usize) with
  | none =>
    simp only [added, core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
      bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
    exact ⟨rest.1.symm, rest.2.symm⟩
  | some total =>
    simp only [added, core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
    cases subtracted : Usize.checked_sub total (alloc.vec.Vec.len state.vals) with
    | none =>
      simp only [subtracted]
      simp only [subtracted, core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
        bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
      exact ⟨rest.1.symm, rest.2.symm⟩
    | some consumed =>
      simp only [subtracted]
      simp only [subtracted, core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
      obtain ⟨answer, read, rest⟩ := bind_ok_inv _ _ _ rest
      refine ⟨answer, read, ?_⟩
      cases answer with
      | Err error =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
          bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
        exact ⟨rest.1.symm, rest.2.symm⟩
      | Ok source =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
        obtain ⟨answer, indexCall, rest⟩ := bind_ok_inv _ _ _ rest
        refine ⟨answer, indexCall, ?_⟩
        cases answer with
        | Err error =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
            bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
          exact ⟨rest.1.symm, rest.2.symm⟩
        | Ok entry =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, simd_lane_eq] at rest
          obtain ⟨⟨pushed, budget, values⟩, pushCall, rest⟩ := bind_ok_inv _ _ _ rest
          refine ⟨pushed, budget, values, pushCall, ?_⟩
          cases pushed with
          | Err error =>
            simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
              bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
            exact ⟨rest.1.symm, rest.2.symm⟩
          | Ok value =>
            cases value
            simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
            obtain ⟨constructed, makeCall, rest⟩ := bind_ok_inv _ _ _ rest
            refine ⟨constructed, makeCall, ?_⟩
            cases constructed with
            | none =>
              simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
                bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
              exact ⟨rest.1.symm, rest.2.symm⟩
            | some instruction =>
              simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
              exact rest

theorem simd_constant_inv {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (a : U32) (bits : U128) (status : core.result.Result Unit Itasca.error.VisitError)
    (called : runtime.compiler.simd.FunctionCompiler.simd_op ops before state 524#u16 a bits = .ok (status, after)) :
    SimdConstantEffect ops before after state bits status := by
  rw [runtime.compiler.simd.FunctionCompiler.simd_op.constant_eq] at called
  obtain ⟨answer, indexCall, rest⟩ := bind_ok_inv _ _ _ called
  refine ⟨answer, indexCall, ?_⟩
  cases answer with
  | Err error =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
      bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
    exact ⟨rest.1.symm, rest.2.symm⟩
  | Ok entry =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
    obtain ⟨⟨pushed, budget, values⟩, pushCall, rest⟩ := bind_ok_inv _ _ _ rest
    refine ⟨pushed, budget, values, pushCall, ?_⟩
    cases pushed with
    | Err error =>
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
        bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
      exact ⟨rest.1.symm, rest.2.symm⟩
    | Ok value =>
      cases value
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
      exact rest

/-- SIMD dispatch selects literal publication, the general tail, or an unchanged
out-of-range rejection. No allocator premise is needed for this trace. -/
def SimdEffect {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (opcode : U16) (a : U32) (bits : U128) (status : core.result.Result Unit Itasca.error.VisitError) : Prop :=
  if opcode = 524#u16 then SimdConstantEffect ops before after state bits status
  else if 512 ≤ opcode.val ∧ opcode.val ≤ 767 then SimdLoweringEffect ops before after state opcode a bits status
  else status = .Err .OutOfMemory ∧ after = before

/-- Canonical SIMD inversion preserves the checked operands and publication path. -/
theorem _root_.Itasca.runtime.compiler.simd.FunctionCompiler.simd_op.inv {A : Type}
    (ops : runtime.platform.Alloc A) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (opcode : U16) (a : U32) (bits : U128)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (called : runtime.compiler.simd.FunctionCompiler.simd_op ops before state opcode a bits = .ok (status, after)) :
    SimdEffect ops before after state opcode a bits status := by
  unfold SimdEffect
  by_cases constant : opcode = 524#u16
  · subst opcode
    rw [if_pos rfl]
    exact simd_constant_inv ops before after state a bits status called
  · rw [if_neg constant]
    by_cases inside : 512 ≤ opcode.val ∧ opcode.val ≤ 767
    · rw [if_pos inside]
      rw [compiler_simd_nonconstant_eq ops before state opcode a bits constant inside.1 inside.2] at called
      exact simdLowering.inv ops before after state opcode a bits status called
    · rw [if_neg inside]
      have outside : opcode.val < 512 ∨ 767 < opcode.val := by omega
      rw [runtime.compiler.simd.FunctionCompiler.simd_op.invalid_eq ops before state opcode a bits outside] at called
      have same := Result.ok_injective called
      exact ⟨(congrArg Prod.fst same).symm, (congrArg Prod.snd same).symm⟩

private theorem make_simd_low_total (op dst source entry : U32) (bound : op.val < 128) :
    runtime.bytecode.Instr.make_simd op dst source entry ⦃ _ => True ⦄ := by
  rcases op with ⟨⟨n, hn⟩⟩
  change n < 128 at bound
  interval_cases n <;> with_unfolding_all (exact WP.spec.ret trivial)

private theorem make_simd_high_total (op dst source entry : U32)
    (lower : 128 ≤ op.val) (bound : op.val < 256) :
    runtime.bytecode.Instr.make_simd op dst source entry ⦃ _ => True ⦄ := by
  rcases op with ⟨⟨n, hn⟩⟩
  change 128 ≤ n at lower
  change n < 256 at bound
  interval_cases n <;> with_unfolding_all (exact WP.spec.ret trivial)

theorem make_simd_total (op dst source entry : U32) (bound : op.val < 256) :
    runtime.bytecode.Instr.make_simd op dst source entry ⦃ _ => True ⦄ := by
  by_cases low : op.val < 128
  · exact make_simd_low_total op dst source entry low
  · exact make_simd_high_total op dst source entry (by omega) bound

/-- The general SIMD tail returns normally when its append lengths are representable. -/
theorem simdLowering.total {A : Type} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState) (opcode : U16)
    (a : U32) (bits : U128) (lower : 512 ≤ opcode.val) (upper : opcode.val ≤ 767)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinate : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (tableFits : before.function.simd.val.length < Usize.max) :
    simdLowering ops before state opcode a bits ⦃ _ => True ⦄ := by
  unfold simdLowering
  step as ⟨reduced, number⟩
  simp only [lift, bind_ok, simd_stores_eq, simd_outputs_eq]
  generalize subEq : UScalar.cast .U32 reduced = sub
  have subBound : sub.val < 256 := by scalar_tac
  cases added : Usize.checked_add (alloc.vec.Vec.len before.before)
      (if simdStores sub then 0#usize else 1#usize) with
  | none =>
    simp only [added, core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, bind_ok, bind_tc_ok, WP.spec_ok]
  | some total =>
    simp only [added, core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    cases subtracted : Usize.checked_sub total (alloc.vec.Vec.len state.vals) with
    | none =>
      simp only [subtracted, core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame, bind_ok, bind_tc_ok, WP.spec_ok]
    | some consumed =>
      simp only [subtracted, core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step with compiler_operand_total ops before consumed as ⟨answer, _⟩
      cases answer with
      | Err error =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame, bind_ok, bind_tc_ok, WP.spec_ok]
      | Ok source =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        step with bounded_index (alloc.vec.Vec.len before.function.simd) as ⟨answer, _⟩
        cases answer with
        | Err error =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame, bind_ok, bind_tc_ok, WP.spec_ok]
        | Ok entry =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, simd_lane_eq]
          step with budget_push ops law before.budget before.function.simd
            ({offset := a, lane := simdLane sub a bits, bits} : runtime.bytecode.SimdImmediate) tableFits
            as ⟨answer, budget, values, _⟩
          cases answer with
          | Err error =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
              core.convert.FromSame, bind_ok, bind_tc_ok, WP.spec_ok]
          | Ok value =>
            cases value
            simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
            step with make_simd_total sub source source entry subBound as ⟨constructed, _⟩
            cases constructed with
            | none =>
              simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                core.convert.FromSame, bind_ok, bind_tc_ok, WP.spec_ok]
            | some instruction =>
              simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
              exact runtime.compiler.lower.FunctionCompiler.finish_op.total ops law _ state instruction codeFits sourceFits coordinate

/-- SIMD dispatch is normal under the append bound of its selected allocation
path. Invalid opcodes reject without requiring either table bound. -/
theorem _root_.Itasca.runtime.compiler.simd.FunctionCompiler.simd_op.total {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (opcode : U16) (a : U32) (bits : U128)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinate : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (poolFits : opcode = 524#u16 → before.function.v128_pool.val.length < Usize.max)
    (tableFits : opcode ≠ 524#u16 → 512 ≤ opcode.val → opcode.val ≤ 767 → before.function.simd.val.length < Usize.max) :
    runtime.compiler.simd.FunctionCompiler.simd_op ops before state opcode a bits ⦃ _ => True ⦄ := by
  by_cases constant : opcode = 524#u16
  · subst opcode
    rw [runtime.compiler.simd.FunctionCompiler.simd_op.constant_eq]
    step with bounded_index (alloc.vec.Vec.len before.function.v128_pool) as ⟨answer, _⟩
    cases answer with
    | Err error =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame, bind_ok, bind_tc_ok, WP.spec_ok]
    | Ok entry =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step with budget_push ops law before.budget before.function.v128_pool bits (poolFits rfl)
        as ⟨answer, budget, values, _⟩
      cases answer with
      | Err error =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame, bind_ok, bind_tc_ok, WP.spec_ok]
      | Ok value =>
        cases value
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        exact runtime.compiler.lower.FunctionCompiler.finish_op.total ops law _ state _ codeFits sourceFits coordinate
  · by_cases inside : 512 ≤ opcode.val ∧ opcode.val ≤ 767
    · rw [compiler_simd_nonconstant_eq ops before state opcode a bits constant inside.1 inside.2]
      exact simdLowering.total ops law before state opcode a bits inside.1 inside.2 codeFits sourceFits coordinate
        (tableFits constant inside.1 inside.2)
    · rw [runtime.compiler.simd.FunctionCompiler.simd_op.invalid_eq ops before state opcode a bits (by omega)]
      exact WP.spec.ret True.intro

/-- Exact checked operand preparation derived from source stack semantics. -/
structure SimdOperandInput {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState) (opcode : U16) where
  reduced : U16
  total : Usize
  consumed : Usize
  source : U32
  number : (opcode - 512#u16 : Result U16) = .ok reduced
  added : Usize.checked_add (alloc.vec.Vec.len before.before)
    (if simdStores (UScalar.cast .U32 reduced) then 0#usize else 1#usize) = some total
  subtracted : Usize.checked_sub total (alloc.vec.Vec.len state.vals) = some consumed
  operand : runtime.compiler.FunctionCompiler.operand ops before consumed = .ok (.Ok source)
  constructed : ∀ entry, ∃ instruction,
    runtime.bytecode.Instr.make_simd (UScalar.cast .U32 reduced) source source entry = .ok (some instruction)

/-- Independent capacity for one nonconstant SIMD immediate and instruction. -/
structure SimdTailDemand {A : Type} (before : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bound : Nat) : Prop extends CallbackDemand before state bound where
  tableIndex : before.function.simd.length ≤ U32.max
  tableCapacity : before.function.simd.length < Usize.max
  tableReserve : before.function.simd.length + 1 ≤ bound

/-- Available general lowering publishes one immediate and finishes one instruction. -/
theorem simdLowering.available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (before : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (opcode : U16) (a : U32) (bits : U128)
    (input : SimdOperandInput ops before state opcode) (demand : SimdTailDemand before state bound) :
    simdLowering ops before state opcode a bits ⦃ (status, after) =>
      status = .Ok () ∧ ∃ used, after.budget = {before.budget with instructions := used} ∧
        used.val = before.budget.instructions.val + 1 ⦄ := by
  unfold simdLowering
  simp only [input.number, lift, bind_ok, simd_stores_eq, simd_outputs_eq,
    input.added, input.subtracted, input.operand, core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch]
  step with bounded_index_available (alloc.vec.Vec.len before.function.simd) demand.tableIndex
    as ⟨answer, entry, accepted, _⟩
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, simd_lane_eq]
  step with budget_push_available ops bound available before.budget before.function.simd
    ({offset := a, lane := simdLane (UScalar.cast .U32 input.reduced) a bits, bits} : runtime.bytecode.SimdImmediate)
    demand.tableCapacity demand.tableReserve
    as ⟨answer, budget, values, accepted, same, _⟩
  subst answer budget
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  obtain ⟨instruction, constructed⟩ := input.constructed entry
  rw [constructed]
  simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  let staged : runtime.compiler.FunctionCompiler A := {before with function := {before.function with simd := values}}
  have ready : CallbackDemand staged state bound :=
    ⟨demand.pc, demand.codeCapacity, demand.sourceCapacity, demand.codeReserve, demand.sourceReserve,
      demand.coordinate, demand.instruction, demand.operands, demand.slots⟩
  exact runtime.compiler.lower.FunctionCompiler.finish_op.available ops bound available staged state ready instruction

/-- Availability selects only the numeric and source premises of the actual
SIMD arm. General operands are certified before any allocation is requested. -/
inductive SimdDemand {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState) (bound : Nat) : U16 → Prop where
  | constant (demand : CallbackDemand before state bound)
      (poolIndex : before.function.v128_pool.length ≤ U32.max)
      (poolCapacity : before.function.v128_pool.length < Usize.max)
      (poolReserve : before.function.v128_pool.length + 1 ≤ bound) : SimdDemand ops before state bound 524#u16
  | general (opcode : U16) (nonconstant : opcode ≠ 524#u16)
      (lower : 512 ≤ opcode.val) (upper : opcode.val ≤ 767)
      (input : SimdOperandInput ops before state opcode) (demand : SimdTailDemand before state bound) :
      SimdDemand ops before state bound opcode

/-- Available SIMD lowering succeeds and charges exactly one instruction. -/
theorem _root_.Itasca.runtime.compiler.simd.FunctionCompiler.simd_op.available {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (before : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (opcode : U16) (a : U32) (bits : U128) (demand : SimdDemand ops before state bound opcode) :
    runtime.compiler.simd.FunctionCompiler.simd_op ops before state opcode a bits ⦃ (status, after) =>
      status = .Ok () ∧ ∃ used, after.budget = {before.budget with instructions := used} ∧
        used.val = before.budget.instructions.val + 1 ⦄ := by
  cases demand with
  | constant demand poolIndex poolCapacity poolReserve =>
    rw [runtime.compiler.simd.FunctionCompiler.simd_op.constant_eq]
    step with bounded_index_available (alloc.vec.Vec.len before.function.v128_pool) poolIndex
      as ⟨answer, entry, accepted, _⟩
    rw [accepted]
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with budget_push_available ops bound available before.budget before.function.v128_pool bits poolCapacity poolReserve
      as ⟨answer, budget, values, accepted, same, _⟩
    subst answer budget
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    let staged : runtime.compiler.FunctionCompiler A := {before with function := {before.function with v128_pool := values}}
    have ready : CallbackDemand staged state bound :=
      ⟨demand.pc, demand.codeCapacity, demand.sourceCapacity, demand.codeReserve, demand.sourceReserve,
        demand.coordinate, demand.instruction, demand.operands, demand.slots⟩
    exact runtime.compiler.lower.FunctionCompiler.finish_op.available ops bound available staged state ready (.ConstV128 before.height entry)
  | general opcode nonconstant lower upper input demand =>
    rw [compiler_simd_nonconstant_eq ops before state opcode a bits nonconstant lower upper]
    exact simdLowering.available ops bound available before state opcode a bits input demand

/-- Before finishing an instruction, SIMD changes only its two allocation
vectors and allocation accounting. -/
def SimdAllocationFrame {A : Type} (before after : runtime.compiler.FunctionCompiler A) : Prop :=
  after = {before with
    budget := after.budget
    function := {before.function with
      simd := after.function.simd
      v128_pool := after.function.v128_pool}}

/-- Successful allocation retains the actual push and which vector was used. -/
inductive SimdAllocated {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.FunctionCompiler A) : Bool → runtime.compiler.FunctionCompiler A → Prop where
  | constant (bits : U128) (budget : runtime.compiler.Budget A) (values : alloc.vec.Vec U128)
      (pushed : runtime.compiler.Budget.push ops before.budget before.function.v128_pool bits = .ok (.Ok (), budget, values)) :
      SimdAllocated ops before true {before with budget, function := {before.function with v128_pool := values}}
  | general (immediate : runtime.bytecode.SimdImmediate) (budget : runtime.compiler.Budget A)
      (values : alloc.vec.Vec runtime.bytecode.SimdImmediate)
      (pushed : runtime.compiler.Budget.push ops before.budget before.function.simd immediate = .ok (.Ok (), budget, values)) :
      SimdAllocated ops before false {before with budget, function := {before.function with simd := values}}

theorem SimdAllocated.frame {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {constant}
    (allocated : SimdAllocated ops before constant after) : SimdAllocationFrame before after := by
  cases allocated <;> rfl

/-- Ordinary failures precede observation or return from the shared finishing
tail; successful executions always retain their exact allocated prefix. -/
def SimdExecution {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (constant : Bool) (status : core.result.Result Unit Itasca.error.VisitError) : Prop :=
  (∃ error, status = .Err error ∧ SimdAllocationFrame before after) ∨
    ∃ staged instruction, SimdAllocated ops before constant staged ∧
      runtime.compiler.lower.FunctionCompiler.finish_op ops staged state instruction = .ok (status, after)

theorem SimdConstantEffect.execution {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {state bits status}
    (effect : SimdConstantEffect ops before after state bits status) :
    SimdExecution ops before after state true status := by
  obtain ⟨answer, _, rest⟩ := effect
  cases answer with
  | Err error =>
    obtain ⟨same, rfl⟩ := rest
    exact Or.inl ⟨error, same, rfl⟩
  | Ok entry =>
    obtain ⟨answer, budget, values, pushed, rest⟩ := rest
    cases answer with
    | Err error =>
      obtain ⟨same, rfl⟩ := rest
      exact Or.inl ⟨error, same, rfl⟩
    | Ok value =>
      cases value
      exact Or.inr ⟨_, _, .constant bits budget values pushed, rest⟩

theorem SimdAllocationEffect.execution {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {state sub a source bits status}
    (effect : SimdAllocationEffect ops before after state sub a source bits status) :
    SimdExecution ops before after state false status := by
  obtain ⟨answer, _, rest⟩ := effect
  cases answer with
  | Err error =>
    obtain ⟨same, rfl⟩ := rest
    exact Or.inl ⟨error, same, rfl⟩
  | Ok entry =>
    obtain ⟨answer, budget, values, pushed, rest⟩ := rest
    cases answer with
    | Err error =>
      obtain ⟨same, rfl⟩ := rest
      exact Or.inl ⟨error, same, rfl⟩
    | Ok value =>
      cases value
      obtain ⟨constructed, _, rest⟩ := rest
      cases constructed with
      | none =>
        obtain ⟨same, rfl⟩ := rest
        exact Or.inl ⟨.OutOfMemory, same, rfl⟩
      | some instruction =>
        exact Or.inr ⟨_, instruction, .general (simdImmediate sub a bits) budget values pushed, rest⟩

theorem SimdLoweringEffect.execution {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {state opcode a bits status}
    (effect : SimdLoweringEffect ops before after state opcode a bits status) :
    SimdExecution ops before after state false status := by
  obtain ⟨reduced, _, rest⟩ := effect
  unfold SimdOperandEffect at rest
  cases added : Usize.checked_add (alloc.vec.Vec.len before.before)
      (if simdStores (UScalar.cast .U32 reduced) then 0#usize else 1#usize) with
  | none =>
    rw [added] at rest
    obtain ⟨same, rfl⟩ := rest
    exact Or.inl ⟨.OutOfMemory, same, rfl⟩
  | some total =>
    simp only [added] at rest
    cases subtracted : Usize.checked_sub total (alloc.vec.Vec.len state.vals) with
    | none =>
      rw [subtracted] at rest
      obtain ⟨same, rfl⟩ := rest
      exact Or.inl ⟨.OutOfMemory, same, rfl⟩
    | some consumed =>
      rw [subtracted] at rest
      obtain ⟨answer, _, rest⟩ := rest
      cases answer with
      | Err error =>
        obtain ⟨same, rfl⟩ := rest
        exact Or.inl ⟨error, same, rfl⟩
      | Ok source => exact rest.execution

theorem SimdEffect.execution {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {state opcode a bits status}
    (effect : SimdEffect ops before after state opcode a bits status) :
    SimdExecution ops before after state (decide (opcode = 524#u16)) status := by
  unfold SimdEffect at effect
  by_cases constant : opcode = 524#u16
  · rw [if_pos constant] at effect
    simpa only [constant, decide_true] using effect.execution
  · rw [if_neg constant] at effect
    by_cases inside : 512 ≤ opcode.val ∧ opcode.val ≤ 767
    · rw [if_pos inside] at effect
      simpa only [constant, decide_false] using effect.execution
    · rw [if_neg inside] at effect
      obtain ⟨same, rfl⟩ := effect
      exact Or.inl ⟨.OutOfMemory, same, rfl⟩

theorem SimdExecution.success {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {state constant}
    (effect : SimdExecution ops before after state constant (.Ok ())) :
    ∃ staged instruction, SimdAllocated ops before constant staged ∧
      runtime.compiler.lower.FunctionCompiler.finish_op ops staged state instruction = .ok (.Ok (), after) := by
  rcases effect with ⟨error, impossible, _⟩ | finished
  · cases impossible
  · exact finished

theorem SimdAllocated.bounds {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {constant}
    (allocated : SimdAllocated ops before constant after) (law : Platform.AllocCorrect ops) :
    after.function.simd.val.length ≤ before.function.simd.val.length + 1 ∧
    after.function.v128_pool.val.length ≤ before.function.v128_pool.val.length + 1 ∧
    (constant = false → after.function.v128_pool = before.function.v128_pool) := by
  cases allocated with
  | constant bits budget values pushed =>
    have appended := (budget_push_success ops law before.budget budget before.function.v128_pool values bits pushed).2
    refine ⟨?_, ?_, ?_⟩
    · change before.function.simd.val.length ≤ before.function.simd.val.length + 1
      omega
    · change values.val.length ≤ before.function.v128_pool.val.length + 1
      simp only [appended, List.length_append, List.length_singleton, Nat.le_refl]
    · intro impossible
      cases impossible
  | general immediate budget values pushed =>
    have appended := (budget_push_success ops law before.budget budget before.function.simd values immediate pushed).2
    refine ⟨?_, ?_, fun _ => rfl⟩
    · change values.val.length ≤ before.function.simd.val.length + 1
      simp only [appended, List.length_append, List.length_singleton, Nat.le_refl]
    · change before.function.v128_pool.val.length ≤ before.function.v128_pool.val.length + 1
      omega

theorem SimdConstantEffect.success {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {state bits}
    (effect : SimdConstantEffect ops before after state bits (.Ok ())) :
    ∃ entry budget values,
      runtime.compiler.bounded_index (alloc.vec.Vec.len before.function.v128_pool) = .ok (.Ok entry) ∧
      runtime.compiler.Budget.push ops before.budget before.function.v128_pool bits = .ok (.Ok (), budget, values) ∧
      runtime.compiler.lower.FunctionCompiler.finish_op ops
        {before with budget, function := {before.function with v128_pool := values}} state
        (.ConstV128 before.height entry) = .ok (.Ok (), after) := by
  obtain ⟨answer, indexCall, rest⟩ := effect
  cases answer with
  | Err error => cases rest.1
  | Ok entry =>
    obtain ⟨answer, budget, values, pushed, rest⟩ := rest
    cases answer with
    | Err error => cases rest.1
    | Ok value =>
      cases value
      exact ⟨entry, budget, values, indexCall, pushed, rest⟩

theorem SimdAllocationEffect.success {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {state sub a source bits}
    (effect : SimdAllocationEffect ops before after state sub a source bits (.Ok ())) :
    ∃ entry budget values instruction,
      runtime.compiler.bounded_index (alloc.vec.Vec.len before.function.simd) = .ok (.Ok entry) ∧
      runtime.compiler.Budget.push ops before.budget before.function.simd (simdImmediate sub a bits) = .ok (.Ok (), budget, values) ∧
      runtime.bytecode.Instr.make_simd sub source source entry = .ok (some instruction) ∧
      runtime.compiler.lower.FunctionCompiler.finish_op ops
        {before with budget, function := {before.function with simd := values}} state instruction = .ok (.Ok (), after) := by
  obtain ⟨answer, indexCall, rest⟩ := effect
  cases answer with
  | Err error => cases rest.1
  | Ok entry =>
    obtain ⟨answer, budget, values, pushed, rest⟩ := rest
    cases answer with
    | Err error => cases rest.1
    | Ok value =>
      cases value
      obtain ⟨constructed, makeCall, rest⟩ := rest
      cases constructed with
      | none => cases rest.1
      | some instruction => exact ⟨entry, budget, values, instruction, indexCall, pushed, makeCall, rest⟩

theorem SimdOperandEffect.success {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {state sub a bits}
    (effect : SimdOperandEffect ops before after state sub a bits (.Ok ())) :
    ∃ total consumed source,
      Usize.checked_add (alloc.vec.Vec.len before.before) (if simdStores sub then 0#usize else 1#usize) = some total ∧
      Usize.checked_sub total (alloc.vec.Vec.len state.vals) = some consumed ∧
      runtime.compiler.FunctionCompiler.operand ops before consumed = .ok (.Ok source) ∧
      SimdAllocationEffect ops before after state sub a source bits (.Ok ()) := by
  unfold SimdOperandEffect at effect
  cases added : Usize.checked_add (alloc.vec.Vec.len before.before) (if simdStores sub then 0#usize else 1#usize) with
  | none =>
    rw [added] at effect
    cases effect.1
  | some total =>
    simp only [added] at effect
    cases subtracted : Usize.checked_sub total (alloc.vec.Vec.len state.vals) with
    | none =>
      rw [subtracted] at effect
      cases effect.1
    | some consumed =>
      rw [subtracted] at effect
      obtain ⟨answer, operand, rest⟩ := effect
      cases answer with
      | Err error => cases rest.1
      | Ok source => exact ⟨total, consumed, source, rfl, subtracted, operand, rest⟩

theorem SimdLoweringEffect.at_reduced {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {state opcode a bits status reduced}
    (effect : SimdLoweringEffect ops before after state opcode a bits status)
    (number : (opcode - 512#u16 : Result U16) = .ok reduced) :
    SimdOperandEffect ops before after state (UScalar.cast .U32 reduced) a bits status := by
  obtain ⟨actual, called, rest⟩ := effect
  rw [number] at called
  have same : actual = reduced := (Result.ok_injective called).symm
  subst actual
  exact rest


end Itasca.Runtime.Compiler
