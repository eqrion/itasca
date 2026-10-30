import Itasca.Runtime.Compiler.Body.Reader.Safety.ScalarDispatchSafety
import Itasca.Runtime.Compiler.Body.Reader.Local.LocalSafety
import Itasca.Runtime.Compiler.Body.Reader.Safety.LiteralSafety
import Itasca.Runtime.Compiler.Body.Reader.Safety.ReferenceSafety
import Itasca.Wasm2.Scalar.Total

/-!
Normal return of scalar reader dispatch.

Main declarations: `compiler_reader_scalar_total`. A direct consumer is `Compiler.Body.Reader.Safety.OrdinarySafety`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem compiler_reader_scalar_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Control.Shape st) (capacity : st.vals.val.length < Usize.max)
    (opcode : U8) (ordinary : opcode.val ∉ Wasm2.controlOpcodes) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx opcode compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  by_cases high : 69 ≤ opcode.val
  · exact compiler_reader_numeric_dispatch_total ops law compiler st data env ctx ready shape capacity opcode high
  by_cases memory : 40 ≤ opcode.val ∧ opcode.val ≤ 62
  · exact compiler_reader_memory_dispatch_total ops law compiler st data env ctx ready shape capacity opcode memory.1 memory.2
  by_cases h_nop : opcode = code.OP_NOP
  · subst opcode
    exact compiler_reader_nop_total ops law compiler st data env ctx ready shape capacity
  by_cases h_unreachable : opcode = code.OP_UNREACHABLE
  · subst opcode
    exact compiler_reader_unreachable_total ops law compiler st data env ctx ready shape capacity
  by_cases h_i32_const : opcode = code.OP_I32_CONST
  · subst opcode
    exact compiler_reader_i32_const_total ops law compiler st data env ctx ready shape capacity
  by_cases h_i64_const : opcode = code.OP_I64_CONST
  · subst opcode
    exact compiler_reader_i64_const_total ops law compiler st data env ctx ready shape capacity
  by_cases h_f32_const : opcode = code.OP_F32_CONST
  · subst opcode
    exact compiler_reader_f32_const_total ops law compiler st data env ctx ready shape capacity
  by_cases h_f64_const : opcode = code.OP_F64_CONST
  · subst opcode
    exact compiler_reader_f64_const_total ops law compiler st data env ctx ready shape capacity
  by_cases h_drop : opcode = code.OP_DROP
  · subst opcode
    exact compiler_reader_drop_total ops law compiler st data env ctx ready shape capacity
  by_cases h_select : opcode = code.OP_SELECT
  · subst opcode
    exact compiler_reader_select_total ops law compiler st data env ctx ready shape capacity
  by_cases h_local_get : opcode = code.OP_LOCAL_GET
  · subst opcode
    exact compiler_reader_local_get_total ops law compiler st data env ctx ready shape capacity
  by_cases h_local_set : opcode = code.OP_LOCAL_SET
  · subst opcode
    exact compiler_reader_local_set_total ops law compiler st data env ctx ready shape capacity
  by_cases h_local_tee : opcode = code.OP_LOCAL_TEE
  · subst opcode
    exact compiler_reader_local_tee_total ops law compiler st data env ctx ready shape capacity
  by_cases h_global_get : opcode = code.OP_GLOBAL_GET
  · subst opcode
    exact compiler_reader_global_get_total ops law compiler st data env ctx ready shape capacity
  by_cases h_global_set : opcode = code.OP_GLOBAL_SET
  · subst opcode
    exact compiler_reader_global_set_total ops law compiler st data env ctx ready shape capacity
  by_cases h_memory_size : opcode = code.OP_MEMORY_SIZE
  · subst opcode
    exact compiler_reader_memory_size_total ops law compiler st data env ctx ready shape capacity
  by_cases h_memory_grow : opcode = code.OP_MEMORY_GROW
  · subst opcode
    exact compiler_reader_memory_grow_total ops law compiler st data env ctx ready shape capacity
  have reserved : (6 ≤ opcode.val ∧ opcode.val ≤ 10) ∨
      (18 ≤ opcode.val ∧ opcode.val ≤ 25) ∨
      (28 ≤ opcode.val ∧ opcode.val ≤ 31) ∨
      (37 ≤ opcode.val ∧ opcode.val ≤ 39) := by
    simp only [Wasm2.controlOpcodes, List.mem_cons, not_or] at ordinary
    simp only [global_simps] at *
    scalar_tac
  rw [code.step.reserved _ st data env ctx opcode compiler reserved]
  simp
end Itasca.Runtime.Compiler
