import Itasca.Runtime.Compiler.Body.Reader.Replay.DormantOperation
import Itasca.Runtime.Compiler.Body.Reader.Scalar.Empty

/-!
Dormant source prefixes for constants, nop and drop.

Main declarations: `structured_reader_prefix_dead_const32_wasm2` and `structured_reader_prefix_dead_drop_wasm2`. A direct consumer is `Compiler.Body.Reader.Scalar.ConstantCompilation`.
-/

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

theorem structured_reader_prefix_dead_const32_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (dead : before.reachable = false)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_I32_CONST)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 code.OP_I32_CONST before = .ok (.Ok (), out, after)) :
    ∃ value,
      ReaderPostWasm2 p out.core (Spec.i32Const value) p.current.ctrl.polymorphic_base (p.current.vals ++ [.Val .I32]) ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (Spec.i32Const value))
        out.core.vals.val out.core.pos.val ∧ after.reachable = false := by
  obtain ⟨capacity, run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨sourceLocals, p.ft.results⟩ index code.OP_I32_CONST before after
    (by simp only [global_simps]; decide) (by simp only [global_simps]; decide)
    (by simp only [global_simps]; rfl) (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨value, callback, read, values, post⟩ := reader_i32_const_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core capacity byte run
  refine ⟨value, post, ?_⟩
  apply post.structured_dead_op ops law invariant dead 65#u16 0#u32 0#u32 (UScalar.cast .U128 (IScalar.hcast .U32 value))
  change runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i32_const ops before out.core value = _ at callback
  simpa only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i32_const, lift, bind_ok] using callback

theorem structured_reader_prefix_dead_const64_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (dead : before.reachable = false)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_I64_CONST)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 code.OP_I64_CONST before = .ok (.Ok (), out, after)) :
    ∃ value,
      ReaderPostWasm2 p out.core (ScalarConst.i64 value) p.current.ctrl.polymorphic_base (p.current.vals ++ [.Val .I64]) ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (ScalarConst.i64 value))
        out.core.vals.val out.core.pos.val ∧ after.reachable = false := by
  obtain ⟨capacity, run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨sourceLocals, p.ft.results⟩ index code.OP_I64_CONST before after
    (by simp only [global_simps]; decide) (by simp only [global_simps]; decide)
    (by simp only [global_simps]; rfl) (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨value, callback, read, values, post⟩ := reader_i64_const_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core capacity byte run
  refine ⟨value, post, ?_⟩
  apply post.structured_dead_op ops law invariant dead 66#u16 0#u32 0#u32 (UScalar.cast .U128 (IScalar.hcast .U64 value))
  change runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i64_const ops before out.core value = _ at callback
  simpa only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i64_const, lift, bind_ok] using callback

theorem structured_reader_prefix_dead_nop_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (dead : before.reachable = false)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_NOP)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 code.OP_NOP before = .ok (.Ok (), out, after)) :
    ReaderPostWasm2 p out.core .NOP p.current.ctrl.polymorphic_base p.current.vals ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance .NOP)
        out.core.vals.val out.core.pos.val ∧ after.reachable = false := by
  obtain ⟨capacity, run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨sourceLocals, p.ft.results⟩ index code.OP_NOP before after
    (by simp only [global_simps]; decide) (by simp only [global_simps]; decide)
    (by simp only [global_simps]; rfl) (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨callback, post⟩ := reader_nop_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core byte run
  have same : out.core.vals.val = st.core.vals.val := post.values.2.trans post.values.1.symm
  refine ⟨post, ?_⟩
  apply post.structured_dead_op ops law invariant dead 1#u16 0#u32 0#u32 0#u128
  exact callback

theorem structured_reader_prefix_dead_drop_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (dead : before.reachable = false)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_DROP)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 code.OP_DROP before = .ok (.Ok (), out, after)) :
    ∃ values,
      ReaderPostWasm2 p out.core .DROP p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance .DROP)
        out.core.vals.val out.core.pos.val ∧ after.reachable = false := by
  obtain ⟨capacity, run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨sourceLocals, p.ft.results⟩ index code.OP_DROP before after
    (by simp only [global_simps]; decide) (by simp only [global_simps]; decide)
    (by simp only [global_simps]; rfl) (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨value, values, callback, read, popped, post⟩ := reader_drop_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core byte run
  obtain ⟨old, new⟩ := post.values
  refine ⟨values, post, ?_⟩
  apply post.structured_dead_op ops law invariant dead 26#u16 0#u32 0#u32 0#u128
  exact callback

end Itasca.Runtime.Code
