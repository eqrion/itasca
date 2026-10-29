import Itasca.Runtime.Compiler.Body.Control.Table.StructuredCompilerPrefixAdvance
import Itasca.Runtime.Compiler.Body.Reader.Calls.CallLowering
import Itasca.Runtime.Compiler.Body.Reader.Replay.Span
import Itasca.Runtime.Compiler.Body.Control.Table.StructuredLinearEmbedding
import Itasca.Runtime.Compiler.Body.Reader.Replay.DormantOperation
import Itasca.Runtime.Compiler.Local.Relations.Stacks.KnownNumericStack
import Itasca.Runtime.Compiler.Body.Reader.Calls.CallEffects
import Itasca.Runtime.Compiler.Body.Reader.Replay.StructuredState

/-!
Live and dormant direct-call source prefixes and their structured compiler-state composition.
-/

/-! ## Structured Reader Prefix Call -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem structured_reader_prefix_call_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context)
    {emit types returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types (env.func_types.val.map EnvTranslation.funcType) returns locals parents current st.core.vals.val p.start.val)
    (reachable : before.reachable = true) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (metadata : FunctionParameterSlots initial env)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_CALL)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 code.OP_CALL before = .ok (.Ok (), out, after)) :
    ∃ (callee : U32) (ft : Itasca.types.FuncType) (values : List code.StackType),
      env.func_types.val[callee.val]? = some ft ∧
      Wasm2.ReaderPost p out.core (.CALL (.mk_uN callee.val)) p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types (env.func_types.val.map EnvTranslation.funcType) returns locals parents (current.advance (.CALL (.mk_uN callee.val)))
        out.core.vals.val out.core.pos.val := by
  have metadataBefore : FunctionParameterSlots before env := by
    simpa only [FunctionParameterSlots, invariant.metadata.fields.2.1] using metadata
  obtain ⟨entered, retained⟩ := invariant.live reachable
  have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
  obtain ⟨codeFits, sourceFits, _, _⟩ := invariant.capacities bound
  have coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max := by
    have cursor := invariant.cursor
    have position := p.inbounds
    omega
  obtain ⟨ordinary, sources, cursor, callee, ft, values, front, base, found, inputTypes, post, arguments, lower⟩ :=
    reader_emit_call_wasm2 p ops law before after out ctx (invariant.known reachable) monomorphic metadataBefore retained.layout reachable
      codeFits sourceFits coordinateFits (by simpa only [global_simps] using byte)
      (by simpa only [global_simps] using accepted)
  have consumed : p.start.val < out.core.pos.val := by have pos := p.pos; have span := post.span; omega
  refine ⟨callee, ft, values, found, post, invariant.call reachable ordinary lower inputTypes ?_ ?_ sources consumed ?_⟩
  · simp only [List.getElem?_map, found, Option.map_some, EnvTranslation.funcType]
  · simpa only [retained.localsEq] using arguments
  · rw [cursor]

end Itasca.Runtime.Compiler

end

/-! ## Structured Reader Prefix Dead Call -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem structured_reader_prefix_dead_call_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (dead : before.reachable = false)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_CALL)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 code.OP_CALL before = .ok (.Ok (), out, after)) :
    ∃ (callee : U32) (values : List code.StackType),
      Wasm2.ReaderPost p out.core (.CALL (.mk_uN callee.val)) p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (.CALL (.mk_uN callee.val)))
        out.core.vals.val out.core.pos.val ∧ after.reachable = false := by
  obtain ⟨callee, values, callback, read, post⟩ := reader_call_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx
    (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
  obtain ⟨_, outer, _, _, base, _, controls, _, vals⟩ := p.opened
  change runtime.compiler.lower.FunctionCompiler.op ops before out.core 16#u16 callee 0#u32 0#u128 = _ at callback
  exact ⟨callee, values, post, post.structured_dead_op ops law invariant dead 16#u16 callee 0#u32 0#u128 callback⟩

end Itasca.Runtime.Compiler

end

/-! ## Structured Reader Compiler Call -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem StructuredReaderCompilerStateWasm2.call {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerStateWasm2 jumpTables emit initial before types (env.func_types.val.map EnvTranslation.funcType) returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (metadata : FunctionParameterSlots initial env)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = code.OP_CALL)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 code.OP_CALL before = .ok (.Ok (), out, after)) :
    ∃ (callee : U32) (values : List code.StackType), StructuredReaderCompilerStateWasm2 jumpTables emit initial after types (env.func_types.val.map EnvTranslation.funcType) returns locals data env ctx.locals index ft out
      parents (current.advance (.CALL (.mk_uN callee.val))) savedParents
      (savedCurrent.advance (.plain (.CALL (.mk_uN callee.val))) (.CALL (.mk_uN callee.val))
        savedCurrent.ctrl.polymorphic_base values) := by
  let p := state.boundary.pending next advance inbounds
  cases reach : before.reachable with
  | true =>
    obtain ⟨callee, ft, values, found, post, compiled⟩ := structured_reader_prefix_call_wasm2 p ops law initial before after out ctx
      state.compiled reach (state.reach.current reach) metadata sourceBound bodyBound byte accepted
    exact ⟨callee, values, state.advance next advance inbounds post (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (fun _ => state.reach.current reach)⟩
  | false =>
    obtain ⟨callee, values, post, compiled, dead⟩ := structured_reader_prefix_dead_call_wasm2 p ops law initial before after out ctx
      state.compiled reach byte accepted
    exact ⟨callee, values, state.advance next advance inbounds post (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (by simp [dead])⟩

end Itasca.Runtime.Compiler

end
