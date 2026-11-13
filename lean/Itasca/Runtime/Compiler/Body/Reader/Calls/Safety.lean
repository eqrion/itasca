import Itasca.Runtime.Compiler.Body.Control.Table.StructuredCompilerPrefixFinish
import Itasca.Runtime.Compiler.Body.Reader.Calls.Acceptance
import Itasca.Runtime.Compiler.Body.Reader.Replay.MetadataTypes
import Itasca.Runtime.Compiler.Body.Control.Table.StructuredCompiledBody
import Itasca.Runtime.Compiler.Body.Reader.Replay.IndexedPreserved
import Itasca.Runtime.Compiler.Local.Relations.Stacks.KnownNumericStack
import Itasca.Runtime.Compiler.Body.Reader.Calls.CallEffects
import Itasca.Runtime.Compiler.Body.Reader.Stateful.ExtendedFullCapacity
import Itasca.Runtime.Compiler.Body.Reader.Replay.SkippedOperation
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulLowered
import Itasca.Runtime.Compiler.Body.Reader.Safety.Run
import Itasca.Runtime.Compiler.Body.Reader.Calls.Instructions
import Itasca.Wasm2.Control.Total
import Itasca.Wasm2.Scalar.ReadersTotal
import Itasca.Runtime.Compiler.Body.Reader.Replay.ProfileSafety
import Itasca.Runtime.Compiler.Body.Relations.Calls.OrdinaryCallbackReady
import Itasca.Runtime.Compiler.Local.Relations.Calls.IndirectCallExclusions

/-!
Sections, each formerly its own module: Compilation, IndirectPrefix, Safety.
-/

/-! ## Compilation -/

section

/-!
Live and dormant direct-call source prefixes and their structured compiler-state composition.
-/

/-! ## Structured Reader Prefix Call -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem structured_reader_prefix_call_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env sourceLocals index st) {A : Type}
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
      st data env ctx index code.OP_CALL before = .ok (.Ok (), out, after)) :
    ∃ (callee : U32) (ft : Itasca.wasm_types.FuncType) (values : List code.StackType),
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
    (p : Wasm2.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (dead : before.reachable = false)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_CALL)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index code.OP_CALL before = .ok (.Ok (), out, after)) :
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
      {core := {st.core with pos := next}} data env ctx index code.OP_CALL before = .ok (.Ok (), out, after)) :
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

end

/-! ## IndirectPrefix -/

section

/-!
A successful callback only appends pair metadata. Live reader typing supplies its operand layout; a dead callback only observes the validator state.

Main declarations: `StatefulReaderPost.indirect_prefix`. A direct consumer is `Compiler.Body.Reader.Replay.StatefulFuturePrefix`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- A successful callback only appends pair metadata. Live reader typing supplies
its operand layout; a dead callback only observes the validator state. -/
theorem StatefulReaderPost.indirect_prefix {jumpTables : List U32} {data env sourceLocals index st}
    {p : Wasm2.Pending data env sourceLocals index st} {out : code.OpIterState} {op : SourceMachine.Stateful.Instruction}
    (post : StatefulReaderPost p out op) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (C : context)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (matched : EnvTranslation.Matches env ⟨sourceLocals,p.ft.results⟩ C)
    (contextLocals : C.LOCALS = locals)
    (a b : U32) (arguments : StatefulArguments op a b)
    (callback : runtime.compiler.lower.FunctionCompiler.op ops before out (statefulOpcode op) a b 0#u128 = .ok (.Ok (),after))
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max) :
    ∃ extra, after.function.indirect.val = before.function.indirect.val ++ extra := by
  by_cases reachable : before.reachable = true
  · obtain ⟨entered,retained⟩ := invariant.live reachable
    have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
    obtain ⟨codeFits,sourceFits,_,_⟩ := invariant.capacities bound
    have coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max := by
      have cursor := invariant.cursor
      have position := p.inbounds
      omega
    exact (post.emission ops law before after C a b arguments callback matched
      (contextLocals.trans retained.localsEq.symm) (invariant.known reachable) (monomorphic reachable)
      retained.layout reachable codeFits sourceFits coordinateFits).2.2.2.1
  · have dead : before.reachable = false := Bool.eq_false_iff.mpr reachable
    have frame := compiler_dead_op_frame ops law before out (statefulOpcode op) a b 0#u128 dead
    rw [callback,WP.spec_ok] at frame
    dsimp only at frame
    refine ⟨[],?_⟩
    rw [frame]
    simp

end Itasca.Runtime.Compiler

end

/-! ## Safety -/

section

/-!
Direct-call reader bounds and callback safety, composing accepted reader steps with compiler resource obligations.
-/

/-! ## Reader Call Bounds -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca
set_option maxHeartbeats 2000000
attribute [local step] code.pop_with_type.total code.pop_types.total
  Wasm2.ScalarReaders.reserved_zero

theorem reader_call_info_bound (st : code.BodyState) (data : Slice U8) (env : metadata.Env)
    (shape : Control.Shape st.core) :
    code.call_info st data env ⦃ out => ∀ index, out.1 = .Ok index →
      index.val < env.func_types.val.length ⦄ := by
  unfold code.call_info
  step*

theorem reader_call_indirect_info_bound (st : code.BodyState) (data : Slice U8) (env : metadata.Env)
    (shape : Control.Shape st.core) :
    code.call_indirect_info st data env ⦃ out => ∀ index table, out.1 = .Ok (index,table) →
      index.val < env.types.val.length ⦄ := by
  unfold code.call_indirect_info
  step*

end Itasca.Runtime.Compiler

end

/-! ## Reader Call Safety -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem compiler_reader_call_wasm2_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.BodyState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (typeIndex : U32)
    (ready : OrdinaryCallbackReady compiler env ctx st.core.vals.val)
    (shape : Control.Shape st.core) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx typeIndex 16#u8 compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.core.vals.val ⦄ := by
  rw [Wasm2.CallbackTrace.dispatch_call]
  have reader := reader_call_info_bound st data env shape
  refine reader_body_run_reached _ _ _ _ (fun state after => ObservedStack after state.core.vals.val) ?_ ?_
  · exact WP.spec_mono reader (by simp)
  · intro state index read
    rw [read,WP.spec_ok] at reader
    have bound := reader index rfl
    exact compiler_on_call_total ops law compiler state.core index
      (by simpa [ready.namespaces.functions] using bound)
      ready.codeFits ready.sourceFits ready.coordinateFits

theorem compiler_reader_call_indirect_wasm2_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.BodyState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (typeIndex : U32)
    (ready : OrdinaryCallbackReady compiler env ctx st.core.vals.val)
    (shape : Control.Shape st.core) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx typeIndex 17#u8 compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.core.vals.val ⦄ := by
  rw [Wasm2.CallbackTrace.dispatch_call_indirect]
  have reader := reader_call_indirect_info_bound st data env shape
  refine reader_body_run_reached _ _ _ _ (fun state after => ObservedStack after state.core.vals.val) ?_ ?_
  · exact WP.spec_mono reader (by simp)
  · intro state pair read
    obtain ⟨index,table⟩ := pair
    rw [read,WP.spec_ok] at reader
    have bound := reader index table rfl
    exact compiler_on_call_indirect_total ops law compiler state.core index table
      (by simpa [ready.namespaces.signatures] using bound)
      ready.pairFits ready.codeFits ready.sourceFits ready.coordinateFits
end Itasca.Runtime.Compiler

end

end
