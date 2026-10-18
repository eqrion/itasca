import Exec.Code.Body.Reader.Simd.ReaderSimdMemory
import Exec.Code.Body.Reader.Memory.ReaderMemoryTypes
import Exec.Code.Body.Reader.Simd.ReaderSimdEmissions
import Exec.Code.Local.Lowering.Simd.SimdCallbacks
import Exec.Code.Body.Reader.Simd.SimdReaderMeaning
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem reader_emit_simd_memory_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (sub : U32) (next : Usize) (op : Wasm2.Simd.MemoryOperation)
    (decoded : Leb128.Decoded data st.core.pos sub next)
    (meaning : Wasm2.Simd.memoryMeaning sub.val = some op) (full : op.laneCount = 0)
    (opcode : U16) (number : opcode.val = 512 + sub.val) (C : context)
    (contextMemories : C.MEMS = env.mem_types.val.map EnvTranslation.memType)
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
    after.function.v128_pool = before.function.v128_pool ∧
    ∃ (arg : code.MemArg), ∃ front values emitted,
      after.function.simd.val = before.function.simd.val ++ [simdImmediate sub arg.offset 0#u128] ∧
      Sequence.stackTypes st.core.vals.val = front ++ op.inputs ∧
      ReaderPostWasm2 p out.core (op.instruction (MemoryMeaning.memArg arg) (.mk_uN 0)) p.current.ctrl.polymorphic_base values ∧
      TypedLowered before after out.core.vals.val emitted (front ++ op.outputs) ∧
      SimdEmission after.function.simd.val after.function.v128_pool.val C
        (front ++ op.inputs) (op.instruction (MemoryMeaning.memArg arg) (.mk_uN 0)) [emitted] (front ++ op.outputs) := by
  obtain ⟨capacity,_⟩ := simd_prefix_success (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
    st out data env ctx index before after accepted
  obtain ⟨arg,middle,position,alignment,offset,checked,callback,read,controls,cursor,values,effect,post⟩ := reader_simd_memory_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx sub next op decoded meaning full byte accepted
  obtain ⟨memory,available⟩ := memory_reader_available env arg _ C contextMemories checked
  have retained := simd_memory_callback_meaning C sub op arg memory meaning full available
  have bound := retained.opcode_bound
  have nonconstant := retained.not_constant
  rw [compiler_simd_memory_callback ops before out.core sub opcode bound number arg] at callback
  have normalized : SimdImmediateMeaning C sub (simdImmediate sub arg.offset 0#u128)
      (Wasm2.Simd.inputTypes (Wasm2.Simd.fullMemoryInputs op.store)) (op.instruction (MemoryMeaning.memArg arg) (.mk_uN 0))
      (Wasm2.Simd.outputTypes (Wasm2.Simd.memoryOutput op.store)) := by
    simpa only [op.inputs_full full,Wasm2.Simd.MemoryOperation.outputs_pop] using retained
  obtain ⟨ordinary,sources,cursor,simd,pool,front,emitted,oldTypes,lowered,emission⟩ :=
    reader_simd_fixed_emission p ops law before after out.core C opcode sub arg.offset arg.align 0#u128
      number bound nonconstant normalized post effect read known monomorphic capacity contextLocals layout reachable
      codeFits sourceFits coordinateFits callback
  refine ⟨ordinary,sources,cursor,pool,arg,front,values,emitted,simd,?_,post,?_,?_⟩
  · simpa only [op.inputs_full full] using oldTypes
  · simpa only [Wasm2.Simd.MemoryOperation.outputs_pop] using lowered
  · simpa only [op.inputs_full full,Wasm2.Simd.MemoryOperation.outputs_pop] using emission
end Exec.Code
