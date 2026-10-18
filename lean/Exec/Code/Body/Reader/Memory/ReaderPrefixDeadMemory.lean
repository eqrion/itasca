import Exec.Code.Body.Reader.Common.ReaderStructuredDead
import Exec.Code.Body.Reader.Memory.MemoryReaderFacts
import Exec.Code.Local.Relations.Common.CoreLoweringEffects
import Exec.Code.Body.Reader.Integer.ReaderInteger
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem reader_prefix_dead_memory_load_wasm1 {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix emit initial before types functions returns locals parents current st.vals.val p.start.val)
    (dead : before.reachable = false) (op : Abs.Memory.Load)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (memoryLoadOpcode op))
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx (UScalar.cast .U8 (memoryLoadOpcode op)) before = .ok (.Ok (),out,after)) :
    ∃ arg values,
      ReaderPostWasm1 p out (op.source (MemoryMeaning.memArg arg)) p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix emit initial after types functions returns locals parents
        (current.advance (op.source (MemoryMeaning.memArg arg))) out.vals.val out.pos.val ∧ after.reachable = false := by
  obtain ⟨meaning,_,_,_,_,ordinary,base,sign,misc⟩ := memory_load_reader_facts ops before out op ⟨0#u32,0#u32⟩
  obtain ⟨arg,values,callback,read,post⟩ := reader_memory_wasm1 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out _ (memoryLoadMeaning op)
    byte meaning accepted
  obtain ⟨_,_,_,source,callbackEq,_⟩ := memory_load_reader_facts ops before out op arg
  rw [callbackEq] at callback
  rw [source] at post
  have ordinary := compiler_core_ordinary_result ops law before after out (.load op arg.offset arg.align) (.Ok ()) callback
  have sources := compiler_core_sources ops law before after out (.load op arg.offset arg.align) callback
  have cursor := compiler_core_cursor ops law before after out (.load op arg.offset arg.align) callback
  exact ⟨arg,values,post,post.structured_skip ops law invariant dead ordinary sources cursor
    (memoryLoadOpcode op) arg.offset arg.align 0#u128 callback⟩

theorem reader_prefix_dead_memory_load_wasm2 {data env sourceLocals index st}
    (p : Wasm2.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (dead : before.reachable = false) (op : Abs.Memory.Load)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (memoryLoadOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (UScalar.cast .U8 (memoryLoadOpcode op)) before = .ok (.Ok (),out,after)) :
    ∃ arg values,
      ReaderPostWasm2 p out.core (op.source (MemoryMeaning.memArg arg)) p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix emit initial after types functions returns locals parents
        (current.advance (op.source (MemoryMeaning.memArg arg))) out.core.vals.val out.core.pos.val ∧ after.reachable = false := by
  obtain ⟨meaning,_,_,_,_,ordinary,base,sign,misc⟩ := memory_load_reader_facts ops before out.core op ⟨0#u32,0#u32⟩
  obtain ⟨capacity,run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨sourceLocals,p.ft.results⟩ index _ before after ordinary base sign misc contextLocals accepted
  obtain ⟨arg,values,callback,read,post⟩ := reader_memory_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core _ (memoryLoadMeaning op)
    capacity byte meaning run
  obtain ⟨_,_,_,source,callbackEq,_⟩ := memory_load_reader_facts ops before out.core op arg
  rw [callbackEq] at callback
  rw [source] at post
  have ordinary := compiler_core_ordinary_result ops law before after out.core (.load op arg.offset arg.align) (.Ok ()) callback
  have sources := compiler_core_sources ops law before after out.core (.load op arg.offset arg.align) callback
  have cursor := compiler_core_cursor ops law before after out.core (.load op arg.offset arg.align) callback
  exact ⟨arg,values,post,post.structured_skip ops law invariant dead ordinary sources cursor
    (memoryLoadOpcode op) arg.offset arg.align 0#u128 callback⟩

theorem reader_prefix_dead_memory_store_wasm1 {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix emit initial before types functions returns locals parents current st.vals.val p.start.val)
    (dead : before.reachable = false) (op : Abs.Memory.Store)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (memoryStoreOpcode op))
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx (UScalar.cast .U8 (memoryStoreOpcode op)) before = .ok (.Ok (),out,after)) :
    ∃ arg values,
      ReaderPostWasm1 p out (op.source (MemoryMeaning.memArg arg)) p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix emit initial after types functions returns locals parents
        (current.advance (op.source (MemoryMeaning.memArg arg))) out.vals.val out.pos.val ∧ after.reachable = false := by
  obtain ⟨meaning,_,_,_,_,ordinary,base,sign,misc⟩ := memory_store_reader_facts ops before out op ⟨0#u32,0#u32⟩
  obtain ⟨arg,values,callback,read,post⟩ := reader_memory_wasm1 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out _ (memoryStoreMeaning op)
    byte meaning accepted
  obtain ⟨_,_,_,source,callbackEq,_⟩ := memory_store_reader_facts ops before out op arg
  rw [callbackEq] at callback
  rw [source] at post
  have ordinary := compiler_core_ordinary_result ops law before after out (.store op arg.offset arg.align) (.Ok ()) callback
  have sources := compiler_core_sources ops law before after out (.store op arg.offset arg.align) callback
  have cursor := compiler_core_cursor ops law before after out (.store op arg.offset arg.align) callback
  exact ⟨arg,values,post,post.structured_skip ops law invariant dead ordinary sources cursor
    (memoryStoreOpcode op) arg.offset arg.align 0#u128 callback⟩

theorem reader_prefix_dead_memory_store_wasm2 {data env sourceLocals index st}
    (p : Wasm2.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (dead : before.reachable = false) (op : Abs.Memory.Store)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (memoryStoreOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (UScalar.cast .U8 (memoryStoreOpcode op)) before = .ok (.Ok (),out,after)) :
    ∃ arg values,
      ReaderPostWasm2 p out.core (op.source (MemoryMeaning.memArg arg)) p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix emit initial after types functions returns locals parents
        (current.advance (op.source (MemoryMeaning.memArg arg))) out.core.vals.val out.core.pos.val ∧ after.reachable = false := by
  obtain ⟨meaning,_,_,_,_,ordinary,base,sign,misc⟩ := memory_store_reader_facts ops before out.core op ⟨0#u32,0#u32⟩
  obtain ⟨capacity,run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨sourceLocals,p.ft.results⟩ index _ before after ordinary base sign misc contextLocals accepted
  obtain ⟨arg,values,callback,read,post⟩ := reader_memory_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core _ (memoryStoreMeaning op)
    capacity byte meaning run
  obtain ⟨_,_,_,source,callbackEq,_⟩ := memory_store_reader_facts ops before out.core op arg
  rw [callbackEq] at callback
  rw [source] at post
  have ordinary := compiler_core_ordinary_result ops law before after out.core (.store op arg.offset arg.align) (.Ok ()) callback
  have sources := compiler_core_sources ops law before after out.core (.store op arg.offset arg.align) callback
  have cursor := compiler_core_cursor ops law before after out.core (.store op arg.offset arg.align) callback
  exact ⟨arg,values,post,post.structured_skip ops law invariant dead ordinary sources cursor
    (memoryStoreOpcode op) arg.offset arg.align 0#u128 callback⟩
end Exec.Code
