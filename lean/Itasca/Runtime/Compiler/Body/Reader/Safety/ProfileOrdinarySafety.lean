import Itasca.Runtime.Compiler.Body.Reader.Safety.ScalarDispatchSafety
import Itasca.Runtime.Compiler.Body.Reader.Local.LocalSafety
import Itasca.Runtime.Compiler.Body.Reader.Safety.ReferenceSafety
import Itasca.Wasm2.Scalar.Total
import Itasca.Runtime.Compiler.Body.Reader.Safety.ExtendedNumericSafety
import Itasca.Runtime.Compiler.Body.Reader.Safety.SaturatingSafety
import Itasca.Runtime.Compiler.Body.Reader.Simd.SimdSafety
import Itasca.Wasm2.Step.Total
import Itasca.Runtime.Compiler.Body.Reader.Replay.ProfileSafety
import Itasca.Runtime.Compiler.Body.Reader.Calls.Safety

/-!
Sections, each formerly its own module: ScalarSafety, OrdinarySafety, ProfileOrdinarySafety.
-/

/-! ## ScalarSafety -/

section

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

end

/-! ## OrdinarySafety -/

section

/-!
Normal return of extended and complete ordinary reader dispatch.

Main declarations: `compiler_reader_extended_total` and `compiler_reader_wasm2_total`. A direct consumer is `Compiler.Body.Reader.Safety.ProfileOrdinarySafety`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca
theorem compiler_reader_extended_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Control.Shape st) (capacity : st.vals.val.length < Usize.max)
    (opcode : U8) (ordinary : opcode.val ∉ Wasm2.controlOpcodes) :
    code.step_extended (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx opcode compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  by_cases sign : 192 ≤ opcode.val ∧ opcode.val ≤ 196
  · exact compiler_reader_sign_dispatch_total ops law compiler st data env ctx ready shape capacity opcode sign.1 sign.2
  have noSign : Wasm2.NumericExtensions.signMeaning opcode = none := by
    unfold Wasm2.NumericExtensions.signMeaning
    split <;> simp_all
  by_cases prefixed : opcode = 252#u8
  · subst opcode
    exact compiler_reader_saturating_dispatch_total ops law compiler st data env ctx ready shape capacity
  rw [code.step_extended.base _ st data env ctx opcode compiler noSign (by simpa only [code.OP_MISC_PREFIX] using prefixed)]
  exact compiler_reader_scalar_total ops law compiler st data env ctx ready shape capacity opcode ordinary

theorem compiler_reader_wasm2_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Control.Shape st) (capacity : st.vals.val.length < Usize.max)
    (opcode : U8) (ordinary : opcode.val ∉ Wasm2.controlOpcodes) :
    code.step_wasm2 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx opcode compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  by_cases h253 : opcode = 253#u8
  · subst opcode
    rw [code.step_wasm2.simd]
    exact compiler_reader_simd_total ops law compiler st data env ctx ready shape capacity
  by_cases h28 : opcode = 28#u8
  · subst opcode
    exact compiler_reader_typed_select_total ops law compiler st data env ctx ready shape capacity
  by_cases h37 : opcode = 37#u8
  · subst opcode
    exact compiler_reader_table_get_total ops law compiler st data env ctx ready shape capacity
  by_cases h38 : opcode = 38#u8
  · subst opcode
    exact compiler_reader_table_set_total ops law compiler st data env ctx ready shape capacity
  by_cases h208 : opcode = 208#u8
  · subst opcode
    exact compiler_reader_ref_null_total ops law compiler st data env ctx ready shape capacity
  by_cases h209 : opcode = 209#u8
  · subst opcode
    exact compiler_reader_ref_is_null_total ops law compiler st data env ctx ready shape capacity
  by_cases h210 : opcode = 210#u8
  · subst opcode
    exact compiler_reader_ref_func_total ops law compiler st data env ctx ready shape capacity
  by_cases h252 : opcode = 252#u8
  · rw [h252, code.step_wasm2.prefixed]
    obtain ⟨result,read,_⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data st.pos)
    simp only [Wasm2.wasm2PrefixedStep,read,bind_ok]
    cases result with
    | Err error => simp
    | Ok pair =>
      obtain ⟨subopcode,next⟩ := pair
      dsimp only at *
      split
      · exact compiler_reader_saturating_dispatch_total ops law compiler st data env ctx ready shape capacity
      · exact compiler_reader_bulk_total ops law compiler {st with pos := next} data env ctx subopcode
          ready ⟨shape.ordered,shape.bounded⟩ capacity
  rw [code.step_wasm2.base _ st data env ctx opcode compiler (by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
    have neq {a b : U8} (h : a ≠ b) : a.val ≠ b.val := fun he => h (UScalar.eq_of_val_eq he)
    exact ⟨neq h28,neq h37,neq h38,neq h208,neq h209,neq h210,neq h252,neq h253⟩)]
  exact compiler_reader_extended_total ops law compiler st data env ctx ready shape capacity opcode ordinary
end Itasca.Runtime.Compiler

end

/-! ## ProfileOrdinarySafety -/

section

/-!
Normal return of profile-filtered ordinary reader steps.

Main declarations: `compiler_reader_profile_wasm2_ordinary_total`. A direct consumer is `Compiler.Body.Reader.Replay.ReachedSafety`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem compiler_reader_profile_wasm2_ordinary_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.BodyState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (index : U32) (opcode : U8)
    (ready : OrdinaryCallbackReady compiler env ctx st.core.vals.val)
    (shape : Control.Shape st.core)
    (ordinary : opcode.val ∉ [2,3,4,5,11,12,13,14,15]) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index opcode compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.core.vals.val ⦄ := by
  by_cases call : opcode = 16#u8
  · subst opcode
    exact compiler_reader_call_wasm2_total ops law compiler st data env ctx index ready shape
  by_cases indirect : opcode = 17#u8
  · subst opcode
    exact compiler_reader_call_indirect_wasm2_total ops law compiler st data env ctx index ready shape
  have scalar : opcode.val ∉ Wasm2.controlOpcodes := by
    simp only [Wasm2.controlOpcodes,List.mem_cons,List.not_mem_nil,or_false,not_or] at ordinary ⊢
    have callNe : opcode.val ≠ 16 := fun h => call (UScalar.eq_of_val_eq h)
    have indirectNe : opcode.val ≠ 17 := fun h => indirect (UScalar.eq_of_val_eq h)
    tauto
  apply reader_profile_scalar_reached _ st data env ctx index opcode compiler
    (fun state after => ObservedStack after state.vals.val) scalar
  intro capacity
  exact compiler_reader_wasm2_total ops law compiler st.core data env ctx ready shape capacity opcode scalar
end Itasca.Runtime.Compiler

end
