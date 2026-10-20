import Exec.Code.Local.Capacity.AuxiliaryAvailability

namespace Exec.Code
open Aeneas Aeneas.Std
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

inductive ScalarLiteralKind where
  | i32 | i64 | f32 | f64

def ScalarLiteralKind.opcode : ScalarLiteralKind → U16
  | .i32 => 65#u16 | .i64 => 66#u16 | .f32 => 67#u16 | .f64 => 68#u16

def ScalarLiteralKind.lowering {A : Type} (kind : ScalarLiteralKind) (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState) (bits : U128) :
    Result (core.result.Result Unit Itasca.error.VisitError × runtime.compiler.FunctionCompiler A) :=
  match kind with
  | .i32 | .f32 => do
    let word ← lift (UScalar.cast .U32 bits)
    runtime.compiler.lower.FunctionCompiler.finish_op ops compiler state (.Const32 compiler.height word)
  | .i64 | .f64 => do
    let word ← lift (UScalar.cast .U64 bits)
    runtime.compiler.lower.FunctionCompiler.finish_op ops compiler state (.Const64 compiler.height word)

/-- Scalar literal callbacks accept for every bit pattern under the same
independent numerical demand; no numeric execution or FP law is needed. -/
theorem compiler_literal_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (kind : ScalarLiteralKind) (bits : U128) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state kind.opcode 0#u32 0#u32 bits
      ⦃ out => out.1 = .Ok () ⦄ := by
  by_cases live : compiler.reachable = true
  · have dispatch : runtime.compiler.lower.FunctionCompiler.op ops compiler state kind.opcode 0#u32 0#u32 bits =
        kind.lowering ops compiler state bits := by
      cases kind <;> unfold ScalarLiteralKind.opcode ScalarLiteralKind.lowering runtime.compiler.lower.FunctionCompiler.op <;>
        rw [if_pos live] <;> rfl
    rw [dispatch]
    cases kind <;> simp only [ScalarLiteralKind.lowering,lift,bind_ok] <;>
      exact finish_op_available ops bound available compiler state demand _
  · unfold runtime.compiler.lower.FunctionCompiler.op
    rw [if_neg live]
    exact compiler_observe_available ops bound available compiler state demand.operands demand.slots

/-- SIMD constants accept when their independently bounded pool index and
reserve fit. The emitted literal retains its exact native bit pattern. -/
theorem compiler_vector_literal_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound)
    (poolBound : compiler.function.v128_pool.length ≤ compiler.function.code.length) (bits : U128) :
    runtime.compiler.simd.FunctionCompiler.simd_op ops compiler state 524#u16 0#u32 bits
      ⦃ out => out.1 = .Ok () ⦄ := by
  unfold runtime.compiler.simd.FunctionCompiler.simd_op
  split <;> try contradiction
  step with bounded_index_available (alloc.vec.Vec.len compiler.function.v128_pool) (by
    change compiler.function.v128_pool.length ≤ U32.max
    have bound := demand.pc
    omega) as ⟨status,index,accepted,indexEq⟩
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  step with budget_push_available ops bound available compiler.budget compiler.function.v128_pool bits
    (by change compiler.function.v128_pool.length < Usize.max; have cap := demand.codeCapacity; omega)
    (by change compiler.function.v128_pool.length+1 ≤ bound; have room := demand.codeReserve; omega)
    as ⟨status,budget,pool,accepted,same,appended⟩
  subst status budget
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  have fresh : CallbackDemand {compiler with function := {compiler.function with v128_pool := pool}} state bound := by
    exact ⟨demand.pc,demand.codeCapacity,demand.sourceCapacity,demand.codeReserve,demand.sourceReserve,
      demand.coordinate,demand.instruction,demand.operands,demand.slots⟩
  change runtime.compiler.lower.FunctionCompiler.finish_op ops
    {compiler with function := {compiler.function with v128_pool := pool}} state
    (.ConstV128 compiler.height index) ⦃ out => out.1 = .Ok () ⦄
  exact finish_op_available ops bound available _ state fresh _

end Exec.Code
