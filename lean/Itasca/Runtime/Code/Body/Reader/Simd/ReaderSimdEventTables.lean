import Itasca.Runtime.Code.Body.Reader.Simd.ReaderSimdEventPrefix
import Itasca.Runtime.Code.Body.Control.Table.CumulativeTableExclusion
import Itasca.Runtime.Code.Body.Reader.Simd.ReaderSimdEvent
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

theorem SimdReaderEvent.tables {jumpTables : List U32} {A : Type} {ops : runtime.platform.Alloc A}
    {data env sourceLocals index st p initial before after out C}
    (event : @SimdReaderEvent A ops data env sourceLocals index st p before after out C)
    (law : Platform.AllocCorrect ops)
    {emit types functions returns locals parents current}
    (contextLocals : C.LOCALS = locals)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max) :
    ∃ extra, CompilerTables.ofFunction after.function = (CompilerTables.ofFunction before.function).append extra := by
  cases reachable : before.reachable with
  | false =>
    have bound := event.meaning.opcode_bound
    have number := event.number
    obtain ⟨prefixProof,dead,tables⟩ := event.post.simd_dead_prefix ops law invariant reachable event.opcode event.a event.b event.bits
      (by omega) (by omega) event.callback
    exact ⟨CompilerTables.empty,by simpa only [CompilerTables.append_empty] using tables⟩
  | true =>
    obtain ⟨entered,retained⟩ := invariant.live reachable
    have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
    obtain ⟨codeFits,sourceFits,_,_⟩ := invariant.capacities bound
    have coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max := by
      have cursor := invariant.cursor
      have position := p.inbounds
      omega
    obtain ⟨ordinary,sources,cursor,extra,front,emitted,tables,oldTypes,lowered,emission⟩ :=
      reader_simd_callback_emission p ops law before after out C event.opcode event.sub event.a event.b event.bits event.number
        event.meaning event.post event.effect event.read (invariant.known reachable) (monomorphic reachable) event.capacity
        (contextLocals.trans retained.localsEq.symm) retained.layout reachable codeFits sourceFits coordinateFits event.callback
    exact ⟨extra,tables⟩
end Itasca.Runtime.Code
