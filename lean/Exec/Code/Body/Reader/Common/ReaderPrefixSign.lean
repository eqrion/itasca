import Exec.Code.Body.Callbacks.Common.CompilerPrefix
import Exec.Code.Body.Reader.Common.ReaderSignEmissions
import Exec.Code.Body.Reader.Common.ReaderSpan
import Exec.Code.Body.Reader.Common.ReaderDead
import Exec.Code.Local.Relations.Common.KnownNumericStack
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem reader_prefix_sign_wasm2 {data env sourceLocals index st}
    (p : Wasm2.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {types functions returns locals parents current}
    (invariant : CompilerPrefix initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (reachable : before.reachable = true) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (op : Abs.Numeric.Instruction) (extension : 192 ≤ (integerOpcode op).val)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (integerOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (UScalar.cast .U8 (integerOpcode op)) before = .ok (.Ok (), out, after)) :
    ∃ values,
      ReaderPostWasm2 p out.core op.source p.current.ctrl.polymorphic_base values ∧
      CompilerPrefix initial after types functions returns locals parents (current.advance op.source)
        out.core.vals.val out.core.pos.val := by
  obtain ⟨entered, retained⟩ := invariant.live reachable
  have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
  obtain ⟨codeFits, sourceFits, _, _⟩ := invariant.capacities bound
  have coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max := by
    have cursor := invariant.cursor
    have position := p.inbounds
    omega
  obtain ⟨ordinary, sources, cursor, front, values, inputTypes, post, emitted, lower, emission⟩ :=
    reader_emit_sign_wasm2 p ops law before after out ctx contextLocals op extension invariant.known monomorphic retained.layout reachable
      codeFits sourceFits coordinateFits byte accepted
  have consumed : p.start.val < out.core.pos.val := by have pos := p.pos; have span := post.span; omega
  refine ⟨values, post, invariant.ordinary reachable ordinary lower ?_ sources consumed ?_⟩
  · simpa only [retained.localsEq, inputTypes] using emission
  · rw [cursor]

theorem reader_prefix_dead_sign_wasm2 {data env sourceLocals index st}
    (p : Wasm2.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {types functions returns locals parents current}
    (invariant : CompilerPrefix initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (dead : before.reachable = false)
    (op : Abs.Numeric.Instruction) (extension : 192 ≤ (integerOpcode op).val)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (integerOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (UScalar.cast .U8 (integerOpcode op)) before = .ok (.Ok (), out, after)) :
    ∃ values,
      ReaderPostWasm2 p out.core op.source p.current.ctrl.polymorphic_base values ∧
      CompilerPrefix initial after types functions returns locals parents (current.advance op.source)
        out.core.vals.val out.core.pos.val ∧ after.reachable = false := by
  obtain ⟨operation, instruction, inputs, output, callback, read, converted,
    ctrlsEq, position, values, effect, post⟩ :=
    reader_integer_sign_wasm2 p ops before after out ctx op extension byte accepted
  obtain ⟨_, _, _, _, _, _, _, _, ordinary, _⟩ := integer_sign_reader_facts ops before out.core op extension
  have capacity := (profile_scalar_success
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx index _ before after ordinary accepted).1
  obtain ⟨_, outer, _, _, base, _, controls, _, vals⟩ := p.opened
  have physicalBase : (Control.base st.core).val = outer.length := by
    simpa [Control.base, controls] using base
  have known := numeric_read_known operation st.core out.core outer p.current.vals vals physicalBase capacity invariant.known read
  exact ⟨values, post, post.dead_op ops law invariant dead known (integerOpcode op) 0#u32 0#u32 0#u128 callback⟩

end Exec.Code
