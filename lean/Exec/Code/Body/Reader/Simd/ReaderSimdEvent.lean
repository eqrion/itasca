import Exec.Code.Body.Reader.Simd.ReaderPrefixSimdCallback
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- All information retained from one actually accepted SIMD reader and
callback. The source meaning is supplied by the independent opcode tables. -/
structure SimdReaderEvent {A : Type} (ops : runtime.platform.Alloc A)
    {data env locals index st} (p : Wasm2.Pending data env locals index st)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState) (C : context) where
  source : instr
  inputs : List types.ValueType
  output : Option types.ValueType
  sub : U32
  a : U32
  b : U32
  bits : U128
  opcode : U16
  number : opcode.val = 512 + sub.val
  meaning : SimdCallbackMeaning C sub a bits inputs source output
  values : List code.StackType
  position : Usize
  post : ReaderPostWasm2 p out source p.current.ctrl.polymorphic_base values
  effect : Wasm2.Simd.FixedEffect p.current.ctrl.polymorphic_base p.current.vals inputs output values
  read : Wasm2.Simd.readFixed {st.core with pos := position} inputs output = .ok (.Ok (),out)
  callback : runtime.compiler.lower.FunctionCompiler.op ops before out opcode a b bits = .ok (.Ok (),after)
  capacity : st.core.vals.val.length < Usize.max

theorem SimdReaderEvent.capacity_step {A : Type} {ops : runtime.platform.Alloc A}
    {data env locals index st p before after out C}
    (event : @SimdReaderEvent A ops data env locals index st p before after out C)
    (law : Platform.AllocCorrect ops) : CapacityStep before after out := by
  have bound := event.meaning.opcode_bound
  exact (compiler_lower_simd_effects ops law before after out event.opcode event.a event.b event.bits
    (by have number := event.number; omega) (by have number := event.number; omega) event.callback).2.2.2

theorem SimdReaderEvent.prefix {A : Type} {ops : runtime.platform.Alloc A}
    {data env sourceLocals index st p initial before after out C}
    (event : @SimdReaderEvent A ops data env sourceLocals index st p before after out C)
    (law : Platform.AllocCorrect ops)
    {emit} [SimdEmbedding after.function.simd.val after.function.v128_pool.val C emit]
    {types functions returns locals parents current}
    (contextLocals : C.LOCALS = locals)
    (invariant : StructuredCompilerPrefix emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max) :
    ∃ extra, CompilerTables.ofFunction after.function = (CompilerTables.ofFunction before.function).append extra ∧
      StructuredCompilerPrefix emit initial after types functions returns locals parents (current.advance event.source)
        out.vals.val out.pos.val ∧ (after.reachable = true → p.current.ctrl.polymorphic_base = false) :=
  event.post.simd_callback_prefix ops law C event.effect event.read event.capacity contextLocals invariant monomorphic
    event.opcode event.sub event.a event.b event.bits event.number event.meaning sourceBound bodyBound event.callback
end Exec.Code
