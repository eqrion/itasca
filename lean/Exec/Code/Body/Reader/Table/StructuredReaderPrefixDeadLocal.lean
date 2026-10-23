import Exec.Code.Body.Reader.Table.StructuredReaderDead
import Exec.Code.Local.Relations.Common.KnownNumericStack
import Exec.Code.Body.Reader.Local.ReaderLocalEffects
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem structured_reader_prefix_dead_local_get_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (dead : before.reachable = false)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_LOCAL_GET)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 code.OP_LOCAL_GET before = .ok (.Ok (), out, after)) :
    ∃ (idx : U32) (values : List code.StackType),
      ReaderPostWasm2 p out.core (.LOCAL_GET (.mk_uN idx.val)) p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (.LOCAL_GET (.mk_uN idx.val)))
        out.core.vals.val out.core.pos.val ∧ after.reachable = false := by
  obtain ⟨capacity, run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨sourceLocals, p.ft.results⟩ index code.OP_LOCAL_GET before after
    (by simp only [global_simps]; decide) (by simp only [global_simps]; decide)
    (by simp only [global_simps]; rfl) (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨idx, values, callback, read, post⟩ := reader_local_get_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core capacity (by simpa only [global_simps] using byte) run
  obtain ⟨ty, _, vals⟩ := reader_local_get_effect st.core out.core data ⟨sourceLocals, p.ft.results⟩ idx capacity read
  refine ⟨idx, values, post, ?_⟩
  change runtime.compiler.lower.FunctionCompiler.op ops before out.core 32#u16 idx 0#u32 0#u128 = _ at callback
  exact post.structured_dead_op ops law invariant dead 32#u16 idx 0#u32 0#u128 callback

theorem structured_reader_prefix_dead_local_set_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (dead : before.reachable = false)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_LOCAL_SET)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 code.OP_LOCAL_SET before = .ok (.Ok (), out, after)) :
    ∃ (idx : U32) (values : List code.StackType),
      ReaderPostWasm2 p out.core (.LOCAL_SET (.mk_uN idx.val)) p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (.LOCAL_SET (.mk_uN idx.val)))
        out.core.vals.val out.core.pos.val ∧ after.reachable = false := by
  obtain ⟨capacity, run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨sourceLocals, p.ft.results⟩ index code.OP_LOCAL_SET before after
    (by simp only [global_simps]; decide) (by simp only [global_simps]; decide)
    (by simp only [global_simps]; rfl) (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨idx, values, callback, read, post⟩ := reader_local_set_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core (by simpa only [global_simps] using byte) run
  obtain ⟨_, outer, _, _, base, _, controls, _, vals⟩ := p.opened
  refine ⟨idx, values, post, ?_⟩
  change runtime.compiler.lower.FunctionCompiler.op ops before out.core 33#u16 idx 0#u32 0#u128 = _ at callback
  exact post.structured_dead_op ops law invariant dead 33#u16 idx 0#u32 0#u128 callback

theorem structured_reader_prefix_dead_local_tee_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (dead : before.reachable = false)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_LOCAL_TEE)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 code.OP_LOCAL_TEE before = .ok (.Ok (), out, after)) :
    ∃ (idx : U32) (values : List code.StackType),
      ReaderPostWasm2 p out.core (.LOCAL_TEE (.mk_uN idx.val)) p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (.LOCAL_TEE (.mk_uN idx.val)))
        out.core.vals.val out.core.pos.val ∧ after.reachable = false := by
  obtain ⟨capacity, run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨sourceLocals, p.ft.results⟩ index code.OP_LOCAL_TEE before after
    (by simp only [global_simps]; decide) (by simp only [global_simps]; decide)
    (by simp only [global_simps]; rfl) (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨idx, values, callback, read, post⟩ := reader_local_tee_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core capacity (by simpa only [global_simps] using byte) run
  obtain ⟨_, outer, _, _, base, _, controls, _, vals⟩ := p.opened
  refine ⟨idx, values, post, ?_⟩
  change runtime.compiler.lower.FunctionCompiler.op ops before out.core 34#u16 idx 0#u32 0#u128 = _ at callback
  exact post.structured_dead_op ops law invariant dead 34#u16 idx 0#u32 0#u128 callback

end Exec.Code
