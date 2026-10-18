import Exec.Code.Body.Reader.Table.StructuredReaderDeadWithTables
import Exec.Code.Body.Relations.Calls.KnownCallStack
import Exec.Code.Body.Reader.Calls.ReaderCallLowering
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem structured_reader_prefix_dead_call_wasm2_with_tables {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefixWithTables (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (dead : before.reachable = false)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_CALL)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 code.OP_CALL before = .ok (.Ok (), out, after)) :
    ∃ (callee : U32) (values : List code.StackType),
      ReaderPostWasm2 p out.core (.CALL (.mk_uN callee.val)) p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefixWithTables (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (.CALL (.mk_uN callee.val)))
        out.core.vals.val out.core.pos.val ∧ after.reachable = false := by
  obtain ⟨callee, values, callback, read, post⟩ := reader_call_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx 
    (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
  obtain ⟨_, outer, _, _, base, _, controls, _, vals⟩ := p.opened
  change runtime.compiler.lower.FunctionCompiler.op ops before out.core 16#u16 callee 0#u32 0#u128 = _ at callback
  exact ⟨callee, values, post, post.structured_dead_op_with_tables ops law invariant dead 16#u16 callee 0#u32 0#u128 callback⟩

theorem structured_reader_prefix_dead_call_wasm1_with_tables {jumpTables : List U32} {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefixWithTables (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.vals.val p.start.val)
    (dead : before.reachable = false)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_CALL)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_CALL before = .ok (.Ok (), out, after)) :
    ∃ (callee : U32) (values : List code.StackType),
      ReaderPostWasm1 p out (.CALL (.mk_uN callee.val)) p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefixWithTables (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (.CALL (.mk_uN callee.val)))
        out.vals.val out.pos.val ∧ after.reachable = false := by
  have capacity : st.vals.val.length < Usize.max := by have bound := p.val_capacity; omega
  obtain ⟨callee, values, callback, read, post⟩ := reader_call_wasm1 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out capacity 
    (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
  obtain ⟨_, outer, _, _, base, _, controls, vals⟩ := p.opened
  change runtime.compiler.lower.FunctionCompiler.op ops before out 16#u16 callee 0#u32 0#u128 = _ at callback
  exact ⟨callee, values, post, post.structured_dead_op_with_tables ops law invariant dead 16#u16 callee 0#u32 0#u128 callback⟩

end Exec.Code
