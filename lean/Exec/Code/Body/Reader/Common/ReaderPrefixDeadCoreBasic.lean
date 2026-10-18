import Exec.Code.Body.Reader.Common.ReaderStructuredDead
import Exec.Code.Body.Reader.Global.ReaderGlobalEmissions
import Exec.Code.Body.Reader.Common.ReaderSelectEmissions
namespace Exec.Code
open Aeneas Aeneas.Std Itasca
theorem reader_prefix_dead_global_get_wasm1 {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix emit initial before types functions returns locals parents current st.vals.val p.start.val)
    (dead : before.reachable = false)
    (byte : data.val[p.start.val]'p.inbounds = 35#u8)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_GLOBAL_GET before = .ok (.Ok (), out, after)) :
    ∃ (idx : U32) (values : List code.StackType),
      ReaderPostWasm1 p out (.GLOBAL_GET (.mk_uN idx.val)) p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix emit initial after types functions returns locals parents (current.advance (.GLOBAL_GET (.mk_uN idx.val)))
        out.vals.val out.pos.val ∧ after.reachable = false := by
  have capacity : st.vals.val.length < Usize.max := by have := p.val_capacity; omega
  obtain ⟨idx, values, callback, read, post⟩ := reader_global_get_wasm1 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out capacity byte accepted
  change runtime.compiler.lower.FunctionCompiler.op ops before out 35#u16 idx 0#u32 0#u128 = _ at callback
  have ordinary := compiler_core_ordinary_result ops law before after out (.globalGet idx) (.Ok ()) callback
  have sources := compiler_core_sources ops law before after out (.globalGet idx) callback
  have cursor := compiler_core_cursor ops law before after out (.globalGet idx) callback
  exact ⟨idx, values, post, post.structured_skip ops law invariant dead ordinary sources cursor
    35#u16 idx 0#u32 0#u128 callback⟩

theorem reader_prefix_dead_global_set_wasm1 {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix emit initial before types functions returns locals parents current st.vals.val p.start.val)
    (dead : before.reachable = false)
    (byte : data.val[p.start.val]'p.inbounds = 36#u8)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_GLOBAL_SET before = .ok (.Ok (), out, after)) :
    ∃ (idx : U32) (values : List code.StackType),
      ReaderPostWasm1 p out (.GLOBAL_SET (.mk_uN idx.val)) p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix emit initial after types functions returns locals parents (current.advance (.GLOBAL_SET (.mk_uN idx.val)))
        out.vals.val out.pos.val ∧ after.reachable = false := by
  obtain ⟨idx, values, callback, read, post⟩ := reader_global_set_wasm1 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out byte accepted
  change runtime.compiler.lower.FunctionCompiler.op ops before out 36#u16 idx 0#u32 0#u128 = _ at callback
  have ordinary := compiler_core_ordinary_result ops law before after out (.globalSet idx) (.Ok ()) callback
  have sources := compiler_core_sources ops law before after out (.globalSet idx) callback
  have cursor := compiler_core_cursor ops law before after out (.globalSet idx) callback
  exact ⟨idx, values, post, post.structured_skip ops law invariant dead ordinary sources cursor
    36#u16 idx 0#u32 0#u128 callback⟩

theorem reader_prefix_dead_select_wasm1 {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix emit initial before types functions returns locals parents current st.vals.val p.start.val)
    (dead : before.reachable = false)
    (byte : data.val[p.start.val]'p.inbounds = 27#u8)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_SELECT before = .ok (.Ok (), out, after)) :
    ∃ values,
      ReaderPostWasm1 p out (.SELECT none) p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix emit initial after types functions returns locals parents (current.advance (.SELECT none))
        out.vals.val out.pos.val ∧ after.reachable = false := by
  have capacity : st.vals.val.length < Usize.max := by have := p.val_capacity; omega
  obtain ⟨selected, values, callback, read, effect, post⟩ := reader_select_wasm1 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out capacity byte accepted
  change runtime.compiler.lower.FunctionCompiler.op ops before out 27#u16 0#u32 0#u32 0#u128 = _ at callback
  have ordinary := compiler_core_ordinary_result ops law before after out (.select false) (.Ok ()) callback
  have sources := compiler_core_sources ops law before after out (.select false) callback
  have cursor := compiler_core_cursor ops law before after out (.select false) callback
  exact ⟨values, post, post.structured_skip ops law invariant dead ordinary sources cursor
    27#u16 0#u32 0#u32 0#u128 callback⟩

theorem reader_prefix_dead_global_get_wasm2 {data env sourceLocals index st}
    (p : Wasm2.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (dead : before.reachable = false)
    (byte : data.val[p.start.val]'p.inbounds = 35#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 code.OP_GLOBAL_GET before = .ok (.Ok (), out, after)) :
    ∃ (idx : U32) (values : List code.StackType),
      ReaderPostWasm2 p out.core (.GLOBAL_GET (.mk_uN idx.val)) p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix emit initial after types functions returns locals parents (current.advance (.GLOBAL_GET (.mk_uN idx.val)))
        out.core.vals.val out.core.pos.val ∧ after.reachable = false := by
  obtain ⟨capacity, run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨sourceLocals, p.ft.results⟩ index code.OP_GLOBAL_GET before after (by simp only [global_simps]; decide)
    (by simp only [global_simps]; decide) (by simp only [global_simps]; rfl)
    (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨idx, values, callback, read, post⟩ := reader_global_get_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core capacity byte run
  change runtime.compiler.lower.FunctionCompiler.op ops before out.core 35#u16 idx 0#u32 0#u128 = _ at callback
  have ordinary := compiler_core_ordinary_result ops law before after out.core (.globalGet idx) (.Ok ()) callback
  have sources := compiler_core_sources ops law before after out.core (.globalGet idx) callback
  have cursor := compiler_core_cursor ops law before after out.core (.globalGet idx) callback
  exact ⟨idx, values, post, post.structured_skip ops law invariant dead ordinary sources cursor
    35#u16 idx 0#u32 0#u128 callback⟩

theorem reader_prefix_dead_global_set_wasm2 {data env sourceLocals index st}
    (p : Wasm2.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (dead : before.reachable = false)
    (byte : data.val[p.start.val]'p.inbounds = 36#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 code.OP_GLOBAL_SET before = .ok (.Ok (), out, after)) :
    ∃ (idx : U32) (values : List code.StackType),
      ReaderPostWasm2 p out.core (.GLOBAL_SET (.mk_uN idx.val)) p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix emit initial after types functions returns locals parents (current.advance (.GLOBAL_SET (.mk_uN idx.val)))
        out.core.vals.val out.core.pos.val ∧ after.reachable = false := by
  obtain ⟨capacity, run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨sourceLocals, p.ft.results⟩ index code.OP_GLOBAL_SET before after (by simp only [global_simps]; decide)
    (by simp only [global_simps]; decide) (by simp only [global_simps]; rfl)
    (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨idx, values, callback, read, post⟩ := reader_global_set_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core byte run
  change runtime.compiler.lower.FunctionCompiler.op ops before out.core 36#u16 idx 0#u32 0#u128 = _ at callback
  have ordinary := compiler_core_ordinary_result ops law before after out.core (.globalSet idx) (.Ok ()) callback
  have sources := compiler_core_sources ops law before after out.core (.globalSet idx) callback
  have cursor := compiler_core_cursor ops law before after out.core (.globalSet idx) callback
  exact ⟨idx, values, post, post.structured_skip ops law invariant dead ordinary sources cursor
    36#u16 idx 0#u32 0#u128 callback⟩

theorem reader_prefix_dead_select_wasm2 {data env sourceLocals index st}
    (p : Wasm2.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (dead : before.reachable = false)
    (byte : data.val[p.start.val]'p.inbounds = 27#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 code.OP_SELECT before = .ok (.Ok (), out, after)) :
    ∃ values,
      ReaderPostWasm2 p out.core (.SELECT none) p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix emit initial after types functions returns locals parents (current.advance (.SELECT none))
        out.core.vals.val out.core.pos.val ∧ after.reachable = false := by
  obtain ⟨capacity, run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨sourceLocals, p.ft.results⟩ index code.OP_SELECT before after (by simp only [global_simps]; decide)
    (by simp only [global_simps]; decide) (by simp only [global_simps]; rfl)
    (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨selected, values, callback, read, effect, post⟩ := reader_select_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core capacity byte run
  change runtime.compiler.lower.FunctionCompiler.op ops before out.core 27#u16 0#u32 0#u32 0#u128 = _ at callback
  have ordinary := compiler_core_ordinary_result ops law before after out.core (.select false) (.Ok ()) callback
  have sources := compiler_core_sources ops law before after out.core (.select false) callback
  have cursor := compiler_core_cursor ops law before after out.core (.select false) callback
  exact ⟨values, post, post.structured_skip ops law invariant dead ordinary sources cursor
    27#u16 0#u32 0#u32 0#u128 callback⟩
end Exec.Code
