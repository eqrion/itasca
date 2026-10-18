import Exec.Code.Body.Control.Common.CumulativeCompilerPrefix
import Exec.Code.Body.Reader.Common.StatefulReaderEmission
import Exec.Code.Body.Reader.Common.ReaderSpan
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Canonical source reading and its actual callback advance a live cumulative
prefix, including the newly allocated indirect-index pair when required. -/
theorem StatefulReaderPost.cumulative_live {data env sourceLocals index st}
    {p : Wasm2.Pending data env sourceLocals index st} {out : code.OpIterState} {op : Abs.Stateful.Instruction}
    (post : StatefulReaderPost p out op) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (C : context)
    {types functions returns locals parents current}
    (invariant : CumulativeCompilerPrefix C initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (reachable : before.reachable = true) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (matched : EnvTranslation.Matches env ⟨sourceLocals,p.ft.results⟩ C)
    (contextLocals : C.LOCALS = locals)
    (a b : U32) (arguments : StatefulArguments op a b)
    (callback : runtime.compiler.lower.FunctionCompiler.op ops before out (statefulOpcode op) a b 0#u128 = .ok (.Ok (),after))
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max) :
    ∃ values, ReaderPostWasm2 p out op.source p.current.ctrl.polymorphic_base values ∧
      CumulativeCompilerPrefix C initial after types functions returns locals parents (current.advance op.source)
        out.vals.val out.pos.val ∧ after.reachable = true := by
  have currentPrefix := invariant.current
  obtain ⟨entered,retained⟩ := currentPrefix.live reachable
  have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
  obtain ⟨codeFits,sourceFits,_,_⟩ := currentPrefix.capacities bound
  have coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max := by
    have cursor := currentPrefix.cursor
    have position := p.inbounds
    omega
  obtain ⟨ordinary,sources,cursor,⟨extra,pairs⟩,values,emitted,output,reader,lowered,emission⟩ :=
    post.emission ops law before after C a b arguments callback matched
      (contextLocals.trans retained.localsEq.symm) (currentPrefix.known reachable) monomorphic retained.layout
      reachable codeFits sourceFits coordinateFits
  have consumed : p.start.val < out.pos.val := by have position := p.pos; have span := reader.span; omega
  exact ⟨values,reader,invariant.ordinary reachable ordinary lowered emission extra pairs sources consumed (by rw [cursor]),
    lowered.1.2.2.2.1.trans reachable⟩

/-- Dead stateful readers retain exact source syntax without requiring concrete
polymorphic operands, and cannot allocate a pair-table entry. -/
theorem StatefulReaderPost.cumulative_dead {data env sourceLocals index st}
    {p : Wasm2.Pending data env sourceLocals index st} {out : code.OpIterState} {op : Abs.Stateful.Instruction}
    (post : StatefulReaderPost p out op) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (C : context)
    {types functions returns locals parents current}
    (invariant : CumulativeCompilerPrefix C initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (dead : before.reachable = false) (a b : U32)
    (callback : runtime.compiler.lower.FunctionCompiler.op ops before out (statefulOpcode op) a b 0#u128 = .ok (.Ok (),after)) :
    ∃ values, ReaderPostWasm2 p out op.source p.current.ctrl.polymorphic_base values ∧
      CumulativeCompilerPrefix C initial after types functions returns locals parents (current.advance op.source)
        out.vals.val out.pos.val ∧ after.reachable = false := by
  obtain ⟨values,reader,_⟩ := post
  have effect := compiler_dead_op_fields ops law before out (statefulOpcode op) a b 0#u128 dead
  rw [callback,WP.spec_ok] at effect
  have frame := compiler_dead_op_frame ops law before out (statefulOpcode op) a b 0#u128 dead
  rw [callback,WP.spec_ok] at frame
  dsimp only at frame
  have pairs : after.function.indirect = before.function.indirect := by rw [frame]
  have consumed : p.start.val < out.pos.val := by have position := p.pos; have span := reader.span; omega
  have cursor := compiler_stateful_cursor ops law before after out op a b callback
  refine ⟨values,reader,invariant.skip op.source dead effect.2.2.2
    (compiler_stateful_ordinary_result ops law before after out op a b (.Ok ()) callback)
    effect.1 pairs (compiler_stateful_sources ops law before after out op a b callback)
    consumed (by rw [cursor]),effect.2.2.2⟩

end Exec.Code
