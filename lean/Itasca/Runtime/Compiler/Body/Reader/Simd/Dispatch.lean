import Itasca.Runtime.Compiler.Body.Reader.Simd.SimdEvent
import Itasca.Runtime.Compiler.Body.Reader.Simd.SimdLane
import Itasca.Runtime.Compiler.Body.Reader.Simd.SimdEmissions
import Itasca.Runtime.Compiler.Local.Lowering.Simd.SimdCallbacks
import Itasca.Runtime.Compiler.Body.Reader.Simd.SimdMeaning
import Itasca.Runtime.Compiler.Body.Reader.Simd.Memory
import Itasca.Runtime.Compiler.Body.Reader.Memory.MemoryTypes
import Itasca.Runtime.Compiler.Body.Reader.Simd.SimdConstant
import Itasca.Runtime.Compiler.Local.Lowering.Simd.SimdBitsCallbacks
import Itasca.Runtime.Compiler.Local.Lowering.Simd.SimdBits
import Itasca.Runtime.Compiler.Body.Reader.Simd.Shuffle

/-!
Complete SIMD event cases and their dispatch lift, composing the operation-family reader facts.
-/

/-! ## Reader Simd Events -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

def simdCompilerOpcode (sub : U32) : U16 := ⟨BitVec.ofNat 16 (512 + sub.val)⟩
theorem simdCompilerOpcode_val (sub : U32) (bound : sub.val < 256) :
    (simdCompilerOpcode sub).val = 512 + sub.val := by
  change (512 + sub.val) % 2 ^ 16 = 512 + sub.val
  apply Nat.mod_eq_of_lt
  omega

section
variable {data env locals index st} (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
  (ops : runtime.platform.Alloc A) (before after : runtime.compiler.FunctionCompiler A)
  (out : code.BodyState) (ctx : code.Context) (C : context)
  (sub : U32) (next : Usize) (decoded : Leb128.Decoded data st.core.pos sub next)
  (byte : data.val[p.start.val]'p.inbounds = 0xfd#u8)
  (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
    st data env ctx index .Wasm2 0xfd#u8 before = .ok (.Ok (),out,after))
include decoded byte accepted

theorem simd_reader_event_pure (op : Wasm2.Simd.Operation)
    (meaning : Wasm2.Simd.pureMeaning sub.val = some op) :
    Nonempty (SimdReaderEvent ops p before after out.core C) := by
  obtain ⟨capacity,_⟩ := simd_prefix_success (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
    st out data env ctx index before after accepted
  obtain ⟨callback,read,controls,position,values,effect,post⟩ := reader_simd_pure_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx sub next op decoded meaning byte accepted
  have bound := Wasm2.Simd.pure_bound meaning
  rw [compiler_simd_callback ops before out.core sub (simdCompilerOpcode sub) bound (simdCompilerOpcode_val sub bound)] at callback
  have retained : SimdImmediateMeaning C sub (simdImmediate sub 0#u32 0#u128)
      (Wasm2.Simd.inputTypes op.signature.popTypes) op.instruction (Wasm2.Simd.outputTypes (some op.signature.output)) := by
    simpa only [Wasm2.Simd.Signature.inputs_pop,Wasm2.Simd.Signature.outputs_pop] using
      (SimdImmediateMeaning.pure sub (simdImmediate sub 0#u32 0#u128) op meaning : SimdImmediateMeaning C _ _ _ _ _)
  exact ⟨{
    source:=op.instruction,inputs:=op.signature.popTypes,output:=some op.signature.output,
    sub:=sub,a:=0#u32,b:=0#u32,bits:=0#u128,opcode:=simdCompilerOpcode sub,
    number:=simdCompilerOpcode_val sub bound,meaning:=.instruction retained,
    values:=values,position:=next,post:=post,effect:=effect,read:=read,callback:=callback,capacity:=capacity}⟩

theorem simd_reader_event_lane (op : Wasm2.Simd.LaneOperation)
    (meaning : Wasm2.Simd.laneMeaning sub.val = some op) :
    Nonempty (SimdReaderEvent ops p before after out.core C) := by
  obtain ⟨capacity,_⟩ := simd_prefix_success (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
    st out data env ctx index before after accepted
  obtain ⟨lane,position,laneBound,span,callback,read,controls,cursor,values,effect,post⟩ := reader_simd_lane_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx sub next op decoded meaning byte accepted
  have retained := simd_lane_callback_meaning C sub op lane meaning
  have bound := retained.opcode_bound
  rw [compiler_simd_lane_callback ops before out.core sub (simdCompilerOpcode sub) bound (simdCompilerOpcode_val sub bound) lane] at callback
  have normalized : SimdImmediateMeaning C sub (simdImmediate sub (UScalar.cast .U32 lane) 0#u128)
      (Wasm2.Simd.inputTypes (Wasm2.Simd.laneInputs op.runtime.1 op.replace)) (op.instruction (.mk_uN lane.val))
      (Wasm2.Simd.outputTypes (Wasm2.Simd.laneOutput op.runtime.1 op.replace)) := by
    simpa only [Wasm2.Simd.LaneOperation.inputs_pop,Wasm2.Simd.LaneOperation.outputs_pop] using retained
  exact ⟨{
    source:=_,inputs:=_,output:=_,sub:=sub,a:=UScalar.cast .U32 lane,b:=0#u32,bits:=0#u128,
    opcode:=simdCompilerOpcode sub,number:=simdCompilerOpcode_val sub bound,meaning:=.instruction normalized,
    values:=values,position:=position,post:=post,effect:=effect,read:=read,callback:=callback,capacity:=capacity}⟩

theorem simd_reader_event_memory (op : Wasm2.Simd.MemoryOperation)
    (meaning : Wasm2.Simd.memoryMeaning sub.val = some op)
    (full : op.laneCount = 0)
    (contextMemories : C.MEMS = env.mem_types.val.map EnvTranslation.memType) :
    Nonempty (SimdReaderEvent ops p before after out.core C) := by
  obtain ⟨capacity,_⟩ := simd_prefix_success (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
    st out data env ctx index before after accepted
  obtain ⟨arg,middle,position,alignment,offset,checked,callback,read,controls,cursor,values,effect,post⟩ := reader_simd_memory_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx sub next op decoded meaning full byte accepted
  obtain ⟨memory,available⟩ := memory_reader_available env arg _ C contextMemories checked
  have retained := simd_memory_callback_meaning C sub op arg memory meaning full available
  have bound := retained.opcode_bound
  let opcode := simdCompilerOpcode sub
  have number := simdCompilerOpcode_val sub bound
  have nonconstant := retained.not_constant
  rw [compiler_simd_memory_callback ops before out.core sub opcode bound number arg] at callback
  have normalized : SimdImmediateMeaning C sub (simdImmediate sub arg.offset 0#u128)
      (Wasm2.Simd.inputTypes (Wasm2.Simd.fullMemoryInputs op.store)) (op.instruction (MemoryMeaning.memArg arg) (.mk_uN 0))
      (Wasm2.Simd.outputTypes (Wasm2.Simd.memoryOutput op.store)) := by
    simpa only [op.inputs_full full,Wasm2.Simd.MemoryOperation.outputs_pop] using retained
  exact ⟨{
    source:=_,inputs:=_,output:=_,sub:=sub,a:=arg.offset,b:=arg.align,bits:=0#u128,
    opcode:=opcode,number:=number,meaning:=.instruction normalized,
    values:=values,position:=position,post:=post,effect:=effect,read:=read,callback:=callback,capacity:=capacity}⟩

theorem simd_reader_event_memory_lane (op : Wasm2.Simd.MemoryOperation)
    (meaning : Wasm2.Simd.memoryMeaning sub.val = some op)
    (laned : op.laneCount ≠ 0)
    (contextMemories : C.MEMS = env.mem_types.val.map EnvTranslation.memType) :
    Nonempty (SimdReaderEvent ops p before after out.core C) := by
  obtain ⟨capacity,_⟩ := simd_prefix_success (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
    st out data env ctx index before after accepted
  obtain ⟨arg,middle,ending,lane,position,alignment,offset,span,laneBound,checked,callback,read,controls,cursor,values,effect,post⟩ := reader_simd_memory_lane_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx sub next op decoded meaning laned byte accepted
  obtain ⟨memory,available⟩ := memory_reader_available env arg _ C contextMemories checked
  have retained := simd_memory_lane_callback_meaning C sub op arg lane memory meaning laned available
  have bound := retained.opcode_bound
  let opcode := simdCompilerOpcode sub
  have number := simdCompilerOpcode_val sub bound
  have nonconstant := retained.not_constant
  rw [compiler_simd_memory_lane_callback ops before out.core sub opcode bound number arg lane] at callback
  have normalized : SimdImmediateMeaning C sub (simdImmediate sub arg.offset (UScalar.cast .U128 lane))
      (Wasm2.Simd.inputTypes ([.V128,.I32])) (op.instruction (MemoryMeaning.memArg arg) (.mk_uN lane.val))
      (Wasm2.Simd.outputTypes (Wasm2.Simd.memoryOutput op.store)) := by
    simpa only [op.inputs_lane laned,Wasm2.Simd.MemoryOperation.outputs_pop] using retained
  exact ⟨{
    source:=_,inputs:=_,output:=_,sub:=sub,a:=arg.offset,b:=arg.align,bits:=UScalar.cast .U128 lane,
    opcode:=opcode,number:=number,meaning:=.instruction normalized,
    values:=values,position:=position,post:=post,effect:=effect,read:=read,callback:=callback,capacity:=capacity}⟩

theorem simd_reader_event_constant (constant : sub = 12#u32) :
    Nonempty (SimdReaderEvent ops p before after out.core C) := by
  subst sub
  obtain ⟨capacity,_⟩ := simd_prefix_success (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
    st out data env ctx index before after accepted
  obtain ⟨low,high,position,bits,callback,read,controls,cursor,values,effect,post⟩ := reader_simd_constant_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx next decoded byte accepted
  rw [compiler_simd_constant_callback ops before out.core low high] at callback
  have normalized : ReaderPostWasm2 p out.core (.VCONST .V128 (.mk_uN (initializerBits low high).val))
      p.current.ctrl.polymorphic_base values := by
    simpa only [initializerBits_val,Wasm2.Simd.vectorConstant] using post
  exact ⟨{
    source:=_,inputs:=[],output:=some .V128,sub:=12#u32,a:=0#u32,b:=0#u32,bits:=initializerBits low high,
    opcode:=524#u16,number:=rfl,meaning:=.constant _ _,values:=values,position:=position,
    post:=normalized,effect:=effect,read:=read,callback:=callback,capacity:=capacity}⟩

theorem simd_reader_event_shuffle (shuffle : sub = 13#u32) :
    Nonempty (SimdReaderEvent ops p before after out.core C) := by
  subst sub
  obtain ⟨capacity,_⟩ := simd_prefix_success (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
    st out data env ctx index before after accepted
  obtain ⟨low,high,bits,bounds,callback,read,controls,values,effect,post⟩ := reader_simd_shuffle_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx next decoded byte accepted
  rw [compiler_simd_shuffle_callback ops before out.core low high] at callback
  obtain ⟨sourceContext,outer,spine,header,base,prior,ctrls,blocks,stack⟩ := p.opened
  have physicalBase : (Control.base {st.core with pos := next}).val = outer.length := by
    simp [Control.base,ctrls,base]
  obtain ⟨prefixBytes,first,last,within,leb⟩ := decoded
  have fixed := simd_shuffle_fixed {st.core with pos := next} out.core data outer p.current.vals stack physicalBase capacity within low high read
  have retained : SimdImmediateMeaning C 13#u32 (simdImmediate 13#u32 0#u32 (initializerBits low high))
      (Wasm2.Simd.inputTypes [.V128,.V128]) (Wasm2.Simd.shuffle low high) (Wasm2.Simd.outputTypes (some .V128)) :=
    simd_shuffle_callback_meaning C low high
  exact ⟨{
    source:=_,inputs:=[.V128,.V128],output:=some .V128,sub:=13#u32,a:=0#u32,b:=0#u32,
    bits:=initializerBits low high,opcode:=525#u16,number:=rfl,meaning:=.instruction retained,
    values:=values,position:=out.core.pos,post:=post,effect:=effect,read:=fixed,callback:=callback,capacity:=capacity}⟩
end
end Itasca.Runtime.Code

end

/-! ## Reader Simd Event Dispatch -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Every accepted SIMD-prefixed reader is one of the independently classified
families and retains a complete canonical reader/callback witness. -/
theorem reader_simd_event_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (before after : runtime.compiler.FunctionCompiler A)
    (out : code.BodyState) (ctx : code.Context) (C : context)
    (contextMemories : C.MEMS = env.mem_types.val.map EnvTranslation.memType)
    (byte : data.val[p.start.val]'p.inbounds = 0xfd#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 0xfd#u8 before = .ok (.Ok (),out,after)) :
    Nonempty (SimdReaderEvent ops p before after out.core C) := by
  obtain ⟨capacity,sub,next,decoded,called⟩ := simd_prefix_success
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx index before after accepted
  cases pure : Wasm2.Simd.pureMeaning sub.val with
  | some op => exact simd_reader_event_pure p ops before after out ctx C sub next decoded byte accepted op pure
  | none =>
    cases lane : Wasm2.Simd.laneMeaning sub.val with
    | some op => exact simd_reader_event_lane p ops before after out ctx C sub next decoded byte accepted op lane
    | none =>
      cases memory : Wasm2.Simd.memoryMeaning sub.val with
      | some op =>
        by_cases full : op.laneCount = 0
        · exact simd_reader_event_memory p ops before after out ctx C sub next decoded byte accepted op memory full contextMemories
        · exact simd_reader_event_memory_lane p ops before after out ctx C sub next decoded byte accepted op memory full contextMemories
      | none =>
        simp only [Wasm2.Simd.subStep,Wasm2.Simd.pure_table,pure,Wasm2.Simd.lane_table,lane,
          Wasm2.Simd.memory_table,memory,Option.map_none,bind_ok] at called
        split at called
        · exact simd_reader_event_constant p ops before after out ctx C 12#u32 next decoded byte accepted rfl
        · exact simd_reader_event_shuffle p ops before after out ctx C 13#u32 next decoded byte accepted rfl
        · simp at called
end Itasca.Runtime.Code

end
