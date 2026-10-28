import Itasca.Runtime.Code.Body.Reader.Common.ReaderTypedSelect
import Itasca.Runtime.Code.Body.Reader.Simd.ReaderSimdTypes
import Itasca.Runtime.Code.Body.Reader.Acceptance.RecordedReaderAcceptance
import Itasca.Runtime.Code.Body.Reader.Acceptance.ReaderProfileAcceptance
import Itasca.Runtime.Code.Local.Capacity.SelectAvailability

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Explicit-select source typing supplies the full live operand layout.
The actual profile reader and callback accept with one instruction of room. -/
theorem reached_profile_typed_select_available_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (before after : List Observation) (compiler : runtime.compiler.FunctionCompiler A)
    (out : code.BodyState) (ctx : code.Context) (demand : CallbackDemand compiler out.core bound)
    (known : compiler.reachable = true → ConcreteStack st.core.vals.val)
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Sequence.stackTypes st.core.vals.val))
    (byte : data.val[p.start.val]'p.inbounds = 28#u8)
    (reference : code.step_profile recorder st data env ctx index .Wasm2 28#u8 before = .ok (.Ok (),out,after)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 28#u8 compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨capacity,raw⟩ := profile_scalar_success recorder st out data env ctx index 28#u8 before after (by decide) reference
  obtain ⟨ty,position,sourceCalled,read,controls,cursor,values,effect,post⟩ := reader_typed_select_wasm2 p
    recorder before after out ctx byte reference
  have callback : invoke (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) compiler
      (.op out.core (.select_typed ty)) ⦃ result => result.1 = .Ok () ∧
        CompilationBudgetEffect compiler.budget result.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
    change runtime.compiler.lower.FunctionCompiler.op ops compiler out.core 28#u16 0#u32 0#u32 0#u128 ⦃ _ ⦄
    by_cases live : compiler.reachable = true
    · obtain ⟨front,types,beforeTypes,_,_⟩ := reader_simd_fixed_types post effect read (known live) (monomorphic live) capacity
      simp only [Wasm2.Simd.inputTypes,Wasm2.Simd.outputTypes,List.reverse_cons,List.reverse_nil,
        List.map_append,List.map_cons,List.map_nil,List.nil_append,List.cons_append,Translate.valueType] at beforeTypes
      have layout := wholeLayout live
      rw [beforeTypes] at layout
      exact compiler_select_available ops bound allocation compiler out.core demand front (Translate.valueType ty) true
        (fun _ => layout)
    · exact compiler_select_available ops bound allocation compiler out.core demand [] .I32 true
        (fun impossible => False.elim (live impossible))
  apply profile_scalar_available_wasm2 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out.core data env
    ctx index 28#u8 compiler (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) capacity (by decide)
  rw [code.step_wasm2.typed_select] at raw ⊢
  exact recorded_reader_available (code.read_typed_select st.core data) .select_typed
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) compiler before after out.core (.select_typed ty)
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) raw sourceCalled callback

end Itasca.Runtime.Code
