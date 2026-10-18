import Exec.Code.Body.Reader.Simd.ReaderSimdPure
import Exec.Code.Body.Reader.Simd.ReaderSimdEmissions
import Exec.Code.Local.Lowering.Simd.SimdCallbacks
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem reader_emit_simd_pure_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (sub : U32) (next : Usize) (op : Wasm2.Simd.Operation)
    (decoded : Leb128.Decoded data st.core.pos sub next)
    (meaning : Wasm2.Simd.pureMeaning sub.val = some op)
    (opcode : U16) (number : opcode.val = 512 + sub.val) (C : context)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (contextLocals : C.LOCALS = compilerLocals before)
    (layout : CompilerLayout before (Sequence.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 0xfd#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 0xfd#u8 before = .ok (.Ok (),out,after)) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧ after.next_source = out.core.pos ∧
    after.function.simd.val = before.function.simd.val ++ [simdImmediate sub 0#u32 0#u128] ∧
    after.function.v128_pool = before.function.v128_pool ∧
    ∃ front values emitted, Sequence.stackTypes st.core.vals.val = front ++ op.signature.inputs ∧
      ReaderPostWasm2 p out.core op.instruction p.current.ctrl.polymorphic_base values ∧
      TypedLowered before after out.core.vals.val emitted (front ++ op.signature.outputs) ∧
      SimdEmission after.function.simd.val after.function.v128_pool.val C
        (front ++ op.signature.inputs) op.instruction [emitted] (front ++ op.signature.outputs) := by
  have bound := Wasm2.Simd.pure_bound meaning
  have nonconstant : sub.val ≠ 12 := by
    intro equal
    have rejected : Wasm2.Simd.pureMeaning 12 = none := rfl
    rw [equal,rejected] at meaning
    cases meaning
  obtain ⟨capacity,_⟩ := simd_prefix_success (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
    st out data env ctx index before after accepted
  obtain ⟨callback,read,controls,position,values,effect,post⟩ := reader_simd_pure_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx sub next op decoded meaning byte accepted
  rw [compiler_simd_callback ops before out.core sub opcode bound number] at callback
  have retained : SimdImmediateMeaning C sub (simdImmediate sub 0#u32 0#u128)
      (Wasm2.Simd.inputTypes op.signature.popTypes) op.instruction (Wasm2.Simd.outputTypes (some op.signature.output)) := by
    simpa only [Wasm2.Simd.Signature.inputs_pop,Wasm2.Simd.Signature.outputs_pop] using
      (SimdImmediateMeaning.pure sub (simdImmediate sub 0#u32 0#u128) op meaning : SimdImmediateMeaning C _ _ _ _ _)
  obtain ⟨ordinary,sources,cursor,simd,pool,front,emitted,oldTypes,lowered,emission⟩ :=
    reader_simd_fixed_emission p ops law before after out.core C opcode sub 0#u32 0#u32 0#u128
      number bound nonconstant retained post effect read known monomorphic capacity contextLocals layout reachable
      codeFits sourceFits coordinateFits callback
  refine ⟨ordinary,sources,cursor,simd,pool,front,values,emitted,?_,post,?_,?_⟩
  · simpa only [Wasm2.Simd.Signature.inputs_pop] using oldTypes
  · simpa only [Wasm2.Simd.Signature.outputs_pop] using lowered
  · simpa only [Wasm2.Simd.Signature.inputs_pop,Wasm2.Simd.Signature.outputs_pop] using emission
end Exec.Code
