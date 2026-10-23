import Exec.Code.Body.Reader.Simd.ReachedSimdScalarAcceptance

namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace
set_option maxRecDepth 4096

/-- The actual sixteen-byte vector constant reader accepts under independently
bounded pool/observer demand, including dead code. -/
theorem reached_profile_simd_constant_available_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (before after : List Observation) (compiler : runtime.compiler.FunctionCompiler A)
    (out : code.BodyState) (ctx : code.Context) (next : Usize)
    (decoded : Leb128.Decoded data st.core.pos 12#u32 next)
    (demand : CallbackDemand compiler out.core bound)
    (poolBound : compiler.function.v128_pool.length ≤ compiler.function.code.length)
    (byte : data.val[p.start.val]'p.inbounds = 253#u8)
    (reference : code.step_profile recorder st data env ctx index .Wasm2 253#u8 before = .ok (.Ok (),out,after)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 253#u8 compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨capacity,raw⟩ := simd_sub_success_of_decoded recorder st out data env ctx index before after 12#u32 next decoded reference
  obtain ⟨lo,hi,position,bits,sourceCalled,_⟩ := reader_simd_constant_wasm2 p recorder before after out ctx next decoded byte reference
  have callback := compiler_on_simd_const_available ops bound allocation compiler out.core demand lo hi poolBound
  apply simd_prefix_available (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx index
    compiler 12#u32 next (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) decoded capacity
  rw [Wasm2.Simd.subStep.constant] at raw ⊢
  exact recorded_reader_available (code.read_simd_const {st.core with pos := next} data)
    (fun actual : U64 × U64 => .simd_const actual.1 actual.2)
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) compiler before after out.core (.simd_const lo hi)
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) raw sourceCalled callback

/-- Shuffle acceptance preserves its actual packed lane bytes and derives
live operand/output layouts from the independent fixed source effect. -/
theorem reached_profile_simd_shuffle_available_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (before after : List Observation) (compiler : runtime.compiler.FunctionCompiler A)
    (out : code.BodyState) (ctx : code.Context) (C : context) (next : Usize)
    (decoded : Leb128.Decoded data st.core.pos 13#u32 next)
    (demand : CallbackDemand compiler out.core bound)
    (known : compiler.reachable = true → ConcreteStack st.core.vals.val)
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Sequence.stackTypes st.core.vals.val))
    (simdBound : compiler.function.simd.length ≤ compiler.function.code.length)
    (byte : data.val[p.start.val]'p.inbounds = 253#u8)
    (reference : code.step_profile recorder st data env ctx index .Wasm2 253#u8 before = .ok (.Ok (),out,after)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 253#u8 compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨capacity,raw⟩ := simd_sub_success_of_decoded recorder st out data env ctx index before after 13#u32 next decoded reference
  obtain ⟨lo,hi,bits,bounds,sourceCalled,read,controls,values,effect,post⟩ := reader_simd_shuffle_wasm2 p
    recorder before after out ctx next decoded byte reference
  obtain ⟨sourceContext,outer,spine,header,base,prior,ctrls,blocks,stack⟩ := p.opened
  have physicalBase : (Control.base {st.core with pos := next}).val = outer.length := by
    simp [Control.base,ctrls,base]
  have fixed := simd_shuffle_fixed {st.core with pos := next} out.core data outer p.current.vals stack physicalBase
    capacity decoded.span.2.2 lo hi read
  have retained : SimdImmediateMeaning C 13#u32 (simdImmediate 13#u32 0#u32 (initializerBits lo hi))
      (Wasm2.Simd.inputTypes [.V128,.V128]) (Wasm2.Simd.shuffle lo hi) (Wasm2.Simd.outputTypes (some .V128)) :=
    simd_shuffle_callback_meaning C lo hi
  have callback : invoke (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) compiler
      (.op out.core (.simd_shuffle lo hi)) ⦃ result => result.1 = .Ok () ∧
        CompilationBudgetEffect compiler.budget result.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
    change (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_simd_shuffle compiler out.core lo hi ⦃ _ ⦄
    rw [compiler_simd_shuffle_callback ops compiler out.core lo hi]
    exact reader_simd_nonconstant_available p ops bound allocation compiler out.core C 525#u16
      13#u32 0#u32 0#u32 (initializerBits lo hi) rfl retained post effect fixed capacity known monomorphic wholeLayout demand simdBound
  apply simd_prefix_available (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx index
    compiler 13#u32 next (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) decoded capacity
  rw [Wasm2.Simd.subStep.shuffle] at raw ⊢
  exact recorded_reader_available (code.read_simd_shuffle {st.core with pos := next} data)
    (fun actual : U64 × U64 => .simd_shuffle actual.1 actual.2)
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) compiler before after out.core (.simd_shuffle lo hi)
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) raw sourceCalled callback

end Exec.Code
