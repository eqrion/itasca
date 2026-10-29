import Itasca.Runtime.Compiler.Body.Reader.Replay.SkippedOperation
import Itasca.Runtime.Compiler.Body.Reader.Memory.Instructions
import Itasca.Runtime.Compiler.Local.Relations.Emission.CoreLoweringEffects
import Itasca.Runtime.Compiler.Body.Reader.Stacks.Values
import Itasca.Runtime.Compiler.Body.Reader.Replay.ProfileAgreement
import Itasca.Runtime.Compiler.Local.Lowering.Integer.LoweringArithmetic
import Itasca.Runtime.Compiler.Local.Relations.Prefix.Prefix
import Itasca.Runtime.Compiler.Local.Relations.Prefix.ResolvedPrefix
import Itasca.Runtime.Compiler.Local.Control.Table.StructuredCodeTableExclusion
import Itasca.Runtime.Compiler.Body.Control.Embedding.StructuredScalarEmbedding
import Itasca.Runtime.Compiler.Body.Control.Table.StructuredCompilerPrefix
import Itasca.Runtime.Compiler.Body.Reader.Memory.MemoryEmissions
import Itasca.Runtime.Compiler.Body.Reader.Replay.Span
import Itasca.Runtime.Compiler.Body.Reader.Replay.StructuredPoint

/-!
Live and dormant scalar-memory reader prefixes, composed into compiler-state preservation.
-/

/-! ## Reader Prefix Dead Memory -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

theorem reader_prefix_dead_memory_load_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (dead : before.reachable = false) (op : Abs.Memory.Load)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (memoryLoadOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (UScalar.cast .U8 (memoryLoadOpcode op)) before = .ok (.Ok (),out,after)) :
    ∃ arg values,
      ReaderPostWasm2 p out.core (op.source (MemoryMeaning.memArg arg)) p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents
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

theorem reader_prefix_dead_memory_store_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (dead : before.reachable = false) (op : Abs.Memory.Store)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (memoryStoreOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (UScalar.cast .U8 (memoryStoreOpcode op)) before = .ok (.Ok (),out,after)) :
    ∃ arg values,
      ReaderPostWasm2 p out.core (op.source (MemoryMeaning.memArg arg)) p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents
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
end Itasca.Runtime.Code

end

/-! ## Reader Prefix Memory -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

theorem reader_prefix_memory_load_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    (C : context) {emit} [ScalarEmbedding C emit] {types functions returns locals parents current}
    (contextCodeLocals : C.LOCALS = locals)
    (contextMemories : C.MEMS = env.mem_types.val.map EnvTranslation.memType)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (reachable : before.reachable = true) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (op : Abs.Memory.Load)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (memoryLoadOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (UScalar.cast .U8 (memoryLoadOpcode op)) before = .ok (.Ok (), out, after)) :
    ∃ arg values,
      ReaderPostWasm2 p out.core (op.source (MemoryMeaning.memArg arg)) p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (op.source (MemoryMeaning.memArg arg)))
        out.core.vals.val out.core.pos.val := by
  obtain ⟨entered, retained⟩ := invariant.live reachable
  have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
  obtain ⟨codeFits, sourceFits, _, _⟩ := invariant.capacities bound
  have coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max := by
    have cursor := invariant.cursor
    have position := p.inbounds
    omega
  obtain ⟨ordinary, sources, cursor, arg, front, values, inputTypes, post, emitted, lower, emission⟩ :=
    reader_emit_memory_load_wasm2 p ops law before after out ctx contextLocals op C (contextCodeLocals.trans retained.localsEq.symm) contextMemories (invariant.known reachable) monomorphic retained.layout reachable
      codeFits sourceFits coordinateFits byte accepted
  have consumed : p.start.val < out.core.pos.val := by have pos := p.pos; have span := post.span; omega
  refine ⟨arg, values, post, invariant.ordinary reachable ordinary lower ?_ sources consumed ?_ emission.not_branchTable⟩
  · simpa only [inputTypes] using (ScalarEmbedding.lift (emit := emit) emission)
  · rw [cursor]

theorem reader_prefix_memory_store_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    (C : context) {emit} [ScalarEmbedding C emit] {types functions returns locals parents current}
    (contextCodeLocals : C.LOCALS = locals)
    (contextMemories : C.MEMS = env.mem_types.val.map EnvTranslation.memType)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (reachable : before.reachable = true) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (op : Abs.Memory.Store)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = UScalar.cast .U8 (memoryStoreOpcode op))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 (UScalar.cast .U8 (memoryStoreOpcode op)) before = .ok (.Ok (), out, after)) :
    ∃ arg values,
      ReaderPostWasm2 p out.core (op.source (MemoryMeaning.memArg arg)) p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (op.source (MemoryMeaning.memArg arg)))
        out.core.vals.val out.core.pos.val := by
  obtain ⟨entered, retained⟩ := invariant.live reachable
  have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
  obtain ⟨codeFits, sourceFits, _, _⟩ := invariant.capacities bound
  have coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max := by
    have cursor := invariant.cursor
    have position := p.inbounds
    omega
  obtain ⟨ordinary, sources, cursor, arg, front, values, inputTypes, post, emitted, lower, emission⟩ :=
    reader_emit_memory_store_wasm2 p ops law before after out ctx contextLocals op C (contextCodeLocals.trans retained.localsEq.symm) contextMemories (invariant.known reachable) monomorphic retained.layout reachable
      codeFits sourceFits coordinateFits byte accepted
  have consumed : p.start.val < out.core.pos.val := by have pos := p.pos; have span := post.span; omega
  refine ⟨arg, values, post, invariant.ordinary reachable ordinary lower ?_ sources consumed ?_ emission.not_branchTable⟩
  · simpa only [inputTypes] using (ScalarEmbedding.lift (emit := emit) emission)
  · rw [cursor]

end Itasca.Runtime.Code

end

/-! ## Structured Reader Compiler Memory -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

theorem StructuredReaderCompilerStateWasm2.memory_load {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (C : context) {emit} [ScalarEmbedding C emit]
    (state : StructuredReaderCompilerStateWasm2 jumpTables emit initial before types functions returns locals data env ctx.locals index ft st parents current savedParents savedCurrent)
    (contextLocals : C.LOCALS = locals)
    (contextMemories : C.MEMS = env.mem_types.val.map EnvTranslation.memType)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (op : Abs.Memory.Load)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = (UScalar.cast .U8 (memoryLoadOpcode op)))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 (UScalar.cast .U8 (memoryLoadOpcode op)) before = .ok (.Ok (),out,after)) :
    StructuredReaderCompilerPointWasm2 jumpTables emit initial after types functions returns locals data env ctx.locals index ft out := by
  let p := state.boundary.pending next advance inbounds
  cases live : before.reachable with
  | true =>
    obtain ⟨arg,values,post,compiled⟩ := reader_prefix_memory_load_wasm2 p ops law initial before after out ctx rfl C
      contextLocals contextMemories state.compiled live (state.reach.current live) op sourceBound bodyBound byte accepted
    exact (state.advance next advance inbounds post (by cases op <;> simp [Abs.Memory.Load.source, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (fun _ => state.reach.current live)).point
  | false =>
    obtain ⟨arg,values,post,compiled,dead⟩ := reader_prefix_dead_memory_load_wasm2 p ops law initial before after out ctx rfl
      state.compiled live op byte accepted
    exact (state.advance next advance inbounds post (by cases op <;> simp [Abs.Memory.Load.source, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (by simp [dead])).point

theorem StructuredReaderCompilerStateWasm2.memory_store {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (C : context) {emit} [ScalarEmbedding C emit]
    (state : StructuredReaderCompilerStateWasm2 jumpTables emit initial before types functions returns locals data env ctx.locals index ft st parents current savedParents savedCurrent)
    (contextLocals : C.LOCALS = locals)
    (contextMemories : C.MEMS = env.mem_types.val.map EnvTranslation.memType)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (op : Abs.Memory.Store)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = (UScalar.cast .U8 (memoryStoreOpcode op)))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 (UScalar.cast .U8 (memoryStoreOpcode op)) before = .ok (.Ok (),out,after)) :
    StructuredReaderCompilerPointWasm2 jumpTables emit initial after types functions returns locals data env ctx.locals index ft out := by
  let p := state.boundary.pending next advance inbounds
  cases live : before.reachable with
  | true =>
    obtain ⟨arg,values,post,compiled⟩ := reader_prefix_memory_store_wasm2 p ops law initial before after out ctx rfl C
      contextLocals contextMemories state.compiled live (state.reach.current live) op sourceBound bodyBound byte accepted
    exact (state.advance next advance inbounds post (by cases op <;> simp [Abs.Memory.Store.source, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (fun _ => state.reach.current live)).point
  | false =>
    obtain ⟨arg,values,post,compiled,dead⟩ := reader_prefix_dead_memory_store_wasm2 p ops law initial before after out ctx rfl
      state.compiled live op byte accepted
    exact (state.advance next advance inbounds post (by cases op <;> simp [Abs.Memory.Store.source, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (by simp [dead])).point

end Itasca.Runtime.Code

end
