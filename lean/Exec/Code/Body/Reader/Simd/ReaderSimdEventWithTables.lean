import Exec.Code.Body.Control.Table.CumulativeTableExclusion
import Exec.Code.Body.Reader.Simd.ReaderSimdEvent
import Exec.Code.Body.Reader.Simd.ReaderPrefixSimdCallbackWithTables
namespace Exec.Code
open Aeneas Aeneas.Std Itasca
theorem SimdReaderEvent.prefix_with_tables {jumpTables : List U32} {A : Type} {ops : runtime.platform.Alloc A}
    {data env sourceLocals index st p initial before after out C}
    (event : @SimdReaderEvent A ops data env sourceLocals index st p before after out C)
    (law : Platform.AllocCorrect ops)
    {emit} [SimdEmbedding after.function.simd.val after.function.v128_pool.val C emit]
    {types functions returns locals parents current}
    (contextLocals : C.LOCALS = locals)
    (invariant : StructuredCompilerPrefixWithTables (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max) :
    ∃ extra, CompilerTables.ofFunction after.function = (CompilerTables.ofFunction before.function).append extra ∧
      StructuredCompilerPrefixWithTables (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance event.source)
        out.vals.val out.pos.val ∧ (after.reachable = true → p.current.ctrl.polymorphic_base = false) :=
  event.post.simd_callback_prefix_with_tables ops law C event.effect event.read event.capacity contextLocals invariant monomorphic
    event.opcode event.sub event.a event.b event.bits event.number event.meaning sourceBound bodyBound event.callback
end Exec.Code
