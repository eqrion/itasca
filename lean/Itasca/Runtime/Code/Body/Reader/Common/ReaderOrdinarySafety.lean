import Itasca.Runtime.Code.Body.Reader.Common.ReaderScalarSafety
import Itasca.Runtime.Code.Body.Reader.Common.ReaderExtendedNumericSafety
import Itasca.Runtime.Code.Body.Reader.Common.ReaderSaturatingSafety
import Itasca.Runtime.Code.Body.Reader.Common.ReaderBulkSafety
import Itasca.Runtime.Code.Body.Reader.Simd.ReaderSimdSafety
import Itasca.Wasm2.Step.Total
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca
theorem compiler_reader_extended_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
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
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
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
end Itasca.Runtime.Code
