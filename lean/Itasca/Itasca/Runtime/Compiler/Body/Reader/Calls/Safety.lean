import Itasca.Runtime.Compiler.Body.Reader.Calls.Acceptance
import Itasca.Runtime.Compiler.Body.Reader.Replay.OrdinaryEffects
import Itasca.Runtime.Compiler.Body.Relations.Checking.ExecutableInstructionPrefix
import Itasca.Runtime.Compiler.Local.Checking.ScopeInstructionPrefixes
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerTableScratchLiteral
import Itasca.Runtime.Compiler.Body.Control.StructuredPrefixes
import Itasca.Runtime.Compiler.Body.Reader.Replay.MetadataTypes
import Itasca.Runtime.Compiler.Body.Control.CompiledBody
import Itasca.Runtime.Compiler.Body.Reader.Replay.ReaderCompilerState
import Itasca.Runtime.Compiler.Local.Relations.Stacks.ConcretePops
import Itasca.Runtime.Compiler.Body.Reader.Calls.Instructions
import Itasca.Runtime.Compiler.Body.Reader.Stateful.ExtendedCapacity
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulLowered
import Itasca.Runtime.Compiler.Body.Reader.Safety.Run
import Itasca.Body.Control.Frame
import Itasca.Body.Scalar.Env
import Itasca.Runtime.Compiler.Body.Relations.CallbackReadiness
import Itasca.Runtime.Compiler.Local.Relations.Calls.BranchAndCallSafety

open WebAssembly

/-!
Proofs for Runtime / Compiler / Body / Reader / Calls.

This module collects InstructionPrefix, Safety.
Each section documents its contracts and consumers.
-/

/-! ## InstructionPrefix -/

section

open Itasca.Representation

/-!
Direct and indirect call instruction-prefix certificates, preserving checked instructions and exit-slot bounds for compiler replay.
-/

/-! ## Reader Call Instruction Prefix -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Actual direct-call reading bounds its source base and retains earlier instruction and exit-slot checks. -/
theorem reader_call_open_instructions {data env locals typeIndex st}
    (p : Body.Pending data env locals typeIndex st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (metadata : FunctionParameterSlots before env)
    (layout : CompilerLayout before (Body.Stack.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = 16#u8)
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx typeIndex 16#u8 before = .ok (.Ok (), out, after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨stable,_,_,index,ft,values,front,base,found,input,post,baseAt,lowered⟩ :=
    reader_emit_call p ops law before after out ctx known monomorphic metadata layout reachable codeFits sourceFits coordinateFits byte accepted
  have tables := (reader_call_effects ops law before after st out data env ctx typeIndex (by simpa only [global_simps] using accepted)).tables
  obtain ⟨inputs,_⟩ := lowered.1.source_capacities layout reachable
  rw [input,slots_append] at inputs
  have valid : runtime.bytecode.CompiledFunction.instruction_valid after.function (.Call index base) = .ok true :=
    (CoreInstructionBounds.call (by omega)).accepts
  refine ⟨lowered.1.open_instruction_prefix tables held ?owners valid,
    exits.retained (congrArg alloc.vec.Vec.val stable.frames) stable.capacity⟩
  intro index owned
  simpa only [PendingInstructionSite,stable.frames] using owned

end Itasca.Compiler

end

/-! ## Reader Indirect Instruction Prefix -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Actual indirect-call reading checks the captured table row and source operand region. -/
theorem reader_indirect_call_open_instructions {data env locals typeIndex st}
    (p : Body.Pending data env locals typeIndex st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (C : context) (matched : Translation.Environment.Matches env ⟨locals,p.ft.results⟩ C)
    (contextLocals : C.LOCALS = compilerLocals before)
    (signatures : SignatureSequence before.signatures.val env.types.val)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (layout : CompilerLayout before (Body.Stack.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = 17#u8)
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx typeIndex 17#u8 before = .ok (.Ok (),out,after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨stable,_,_,index,table,values,emitted,output,pairs,post,lowered,emission⟩ :=
    reader_emit_indirect_call p ops law before after out ctx C matched contextLocals signatures known monomorphic layout reachable codeFits sourceFits coordinateFits byte accepted
  obtain ⟨otherIndex,otherTable,_,callback,_⟩ := reader_indirect_call p (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  change runtime.compiler.lower.FunctionCompiler.op ops before out.core 17#u16 otherIndex otherTable 0#u128 = _ at callback
  have tables := compiler_tables_pair_append before.function after.function _ pairs
    (compiler_indirect_call_auxiliary_tables ops law before after out.core otherIndex otherTable (.Ok ()) callback)
  have growth := instruction_check_extends_of_tables_append before.function after.function _ tables
    stable.capacity (by change before.function.code.val.length ≤ after.function.code.val.length; rw [lowered.1.1,List.length_append,List.length_singleton]; omega)
  exact ⟨lowered.1.executable_instruction_prefix layout reachable contextLocals
    (.indirect emission) (by intro depths fallback same; cases same) growth held stable.frames,
    exits.retained (congrArg alloc.vec.Vec.val stable.frames) stable.capacity⟩

end Itasca.Compiler

end

/-! ## Reader Call Checked Prefix -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Actual call reading preserves both invariants on live and unreachable paths. -/
theorem reader_call_checked_prefix {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current st.core.vals.val p.start.val)
    (metadata : FunctionParameterSlots before env)
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val+data.length ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = 16#u8)
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 16#u8 before = .ok (.Ok (),out,after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  by_cases live : before.reachable = true
  · obtain ⟨entered,retained⟩ := invariant.live live
    have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
    obtain ⟨codeFits,sourceFits,_,_⟩ := invariant.capacities bound
    have coordinateFits : before.function.body_start.val+before.next_source.val ≤ Usize.max := by
      have cursor := invariant.cursor
      have position := p.inbounds
      omega
    exact reader_call_open_instructions p ops law before after out ctx (invariant.known live) (monomorphic live) metadata retained.layout live
      codeFits sourceFits coordinateFits held exits byte accepted
  · obtain ⟨target,_,callback,_⟩ := reader_call p (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    change runtime.compiler.lower.FunctionCompiler.op ops before out.core 16#u16 target 0#u32 0#u128 = _ at callback
    exact compiler_dead_op_checked_prefix ops law before after out.core 16#u16 target 0#u32 0#u128 (Bool.eq_false_iff.mpr live) held exits callback

/-- Actual call reading preserves both invariants on live and unreachable paths. -/
theorem reader_indirect_call_checked_prefix {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current st.core.vals.val p.start.val)
    (C : context) (matched : Translation.Environment.Matches env ⟨sourceLocals,p.ft.results⟩ C)
    (contextLocals : C.LOCALS = locals)
    (signatures : SignatureSequence before.signatures.val env.types.val)
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val+data.length ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = 17#u8)
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 17#u8 before = .ok (.Ok (),out,after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  by_cases live : before.reachable = true
  · obtain ⟨entered,retained⟩ := invariant.live live
    have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
    obtain ⟨codeFits,sourceFits,_,_⟩ := invariant.capacities bound
    have coordinateFits : before.function.body_start.val+before.next_source.val ≤ Usize.max := by
      have cursor := invariant.cursor
      have position := p.inbounds
      omega
    exact reader_indirect_call_open_instructions p ops law before after out ctx C matched (contextLocals.trans retained.localsEq.symm) signatures (invariant.known live) (monomorphic live) retained.layout live
      codeFits sourceFits coordinateFits held exits byte accepted
  · obtain ⟨target,table,_,callback,_⟩ := reader_indirect_call p (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
    change runtime.compiler.lower.FunctionCompiler.op ops before out.core 17#u16 target table 0#u128 = _ at callback
    exact compiler_dead_op_checked_prefix ops law before after out.core 17#u16 target table 0#u128 (Bool.eq_false_iff.mpr live) held exits callback

end Itasca.Compiler

end

end

/-! ## Safety -/

section

/-! ## Compilation -/

section

/-!
Live and dormant direct-call source prefixes and their structured compiler-state composition.
-/

/-! ## Structured Reader Prefix Call -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem structured_reader_prefix_call {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context)
    {emit types returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types (env.func_types.val.map Translation.Environment.funcType) returns locals parents current st.core.vals.val p.start.val)
    (reachable : before.reachable = true) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (metadata : FunctionParameterSlots initial env)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_CALL)
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index code.OP_CALL before = .ok (.Ok (), out, after)) :
    ∃ (callee : U32) (ft : Itasca.wasm_types.FuncType) (values : List code.StackType),
      env.func_types.val[callee.val]? = some ft ∧
      Body.ReaderPost p out.core (.CALL (.mk_uN callee.val)) p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types (env.func_types.val.map Translation.Environment.funcType) returns locals parents (current.advance (.CALL (.mk_uN callee.val)))
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
    reader_emit_call p ops law before after out ctx (invariant.known reachable) monomorphic metadataBefore retained.layout reachable
      codeFits sourceFits coordinateFits (by simpa only [global_simps] using byte)
      (by simpa only [global_simps] using accepted)
  have consumed : p.start.val < out.core.pos.val := by have pos := p.pos; have span := post.span; omega
  refine ⟨callee, ft, values, found, post, invariant.call reachable ordinary lower inputTypes ?_ ?_ sources consumed ?_⟩
  · simp only [List.getElem?_map, found, Option.map_some, Translation.Environment.funcType]
  · simpa only [retained.localsEq] using arguments
  · rw [cursor]

end Itasca.Compiler

end

/-! ## Structured Reader Prefix Dead Call -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem structured_reader_prefix_dead_call {jumpTables : List U32} {data env sourceLocals index st}
    (p : Body.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (dead : before.reachable = false)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_CALL)
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index code.OP_CALL before = .ok (.Ok (), out, after)) :
    ∃ (callee : U32) (values : List code.StackType),
      Body.ReaderPost p out.core (.CALL (.mk_uN callee.val)) p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (.CALL (.mk_uN callee.val)))
        out.core.vals.val out.core.pos.val ∧ after.reachable = false := by
  obtain ⟨callee, values, callback, read, post⟩ := reader_call p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx
    (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
  obtain ⟨_, outer, _, _, base, _, controls, _, vals⟩ := p.opened
  change runtime.compiler.lower.FunctionCompiler.op ops before out.core 16#u16 callee 0#u32 0#u128 = _ at callback
  exact ⟨callee, values, post, post.structured_dead_op ops law invariant dead 16#u16 callee 0#u32 0#u128 callback⟩

end Itasca.Compiler

end

/-! ## Structured Reader Compiler Call -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem StructuredReaderCompilerState.call {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerState jumpTables emit initial before types (env.func_types.val.map Translation.Environment.funcType) returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (metadata : FunctionParameterSlots initial env)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = code.OP_CALL)
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index code.OP_CALL before = .ok (.Ok (), out, after)) :
    ∃ (callee : U32) (values : List code.StackType), StructuredReaderCompilerState jumpTables emit initial after types (env.func_types.val.map Translation.Environment.funcType) returns locals data env ctx.locals index ft out
      parents (current.advance (.CALL (.mk_uN callee.val))) savedParents
      (savedCurrent.advance (.plain (.CALL (.mk_uN callee.val))) (.CALL (.mk_uN callee.val))
        savedCurrent.ctrl.polymorphic_base values) := by
  let p := state.boundary.pending next advance inbounds
  cases reach : before.reachable with
  | true =>
    obtain ⟨callee, ft, values, found, post, compiled⟩ := structured_reader_prefix_call p ops law initial before after out ctx
      state.compiled reach (state.reach.current reach) metadata sourceBound bodyBound byte accepted
    exact ⟨callee, values, state.advance next advance inbounds post (by simp [Spec.DeclaredReferences.Instruction, Spec.DeclaredReferences.instructionIndices]) compiled (fun _ => state.reach.current reach)⟩
  | false =>
    obtain ⟨callee, values, post, compiled, dead⟩ := structured_reader_prefix_dead_call p ops law initial before after out ctx
      state.compiled reach byte accepted
    exact ⟨callee, values, state.advance next advance inbounds post (by simp [Spec.DeclaredReferences.Instruction, Spec.DeclaredReferences.instructionIndices]) compiled (by simp [dead])⟩

end Itasca.Compiler

end

end

/-! ## IndirectPrefix -/

section

/-!
A successful callback only appends pair metadata. Live reader typing supplies its operand layout; a dead callback only observes the validator state.

Main declarations: `StatefulReaderPost.indirect_prefix`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- A successful callback only appends pair metadata. Live reader typing supplies
its operand layout; a dead callback only observes the validator state. -/
theorem StatefulReaderPost.indirect_prefix {jumpTables : List U32} {data env sourceLocals index st}
    {p : Body.Pending data env sourceLocals index st} {out : code.OpIterState} {op : SourceMachine.Stateful.Instruction}
    (post : StatefulReaderPost p out op) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (C : context)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (matched : Translation.Environment.Matches env ⟨sourceLocals,p.ft.results⟩ C)
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

end Itasca.Compiler

end

/-! ## Safety -/

section

/-!
Direct-call reader bounds and callback safety, composing accepted reader steps with compiler resource obligations.
-/

/-! ## Reader Call Bounds -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca
attribute [local step] code.pop_with_type.total code.pop_types.total
  Body.ScalarReaders.reserved_zero

theorem reader_call_info_bound (st : code.BodyState) (data : Slice U8) (env : metadata.Env)
    (shape : Body.Control.Shape st.core) :
    code.call_info st data env ⦃ out => ∀ index, out.1 = .Ok index →
      index.val < env.func_types.val.length ⦄ := by
  unfold code.call_info
  step*

theorem reader_call_indirect_info_bound (st : code.BodyState) (data : Slice U8) (env : metadata.Env)
    (shape : Body.Control.Shape st.core) :
    code.call_indirect_info st data env ⦃ out => ∀ index table, out.1 = .Ok (index,table) →
      index.val < env.types.val.length ⦄ := by
  unfold code.call_indirect_info
  step*

end Itasca.Compiler

end

/-! ## Reader Call Safety -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem compiler_reader_call_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.BodyState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (typeIndex : U32)
    (ready : OrdinaryCallbackReady compiler env ctx st.core.vals.val)
    (shape : Body.Control.Shape st.core) :
    code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx typeIndex 16#u8 compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.core.vals.val ⦄ := by
  rw [Body.CallbackTrace.dispatch_call]
  have reader := reader_call_info_bound st data env shape
  refine reader_body_run_reached _ _ _ _ (fun state after => ObservedStack after state.core.vals.val) ?_ ?_
  · exact WP.spec_mono reader (by simp)
  · intro state index read
    rw [read,WP.spec_ok] at reader
    have bound := reader index rfl
    exact compiler_on_call_total ops law compiler state.core index
      (by simpa [ready.namespaces.functions] using bound)
      ready.codeFits ready.sourceFits ready.coordinateFits

theorem compiler_reader_call_indirect_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.BodyState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (typeIndex : U32)
    (ready : OrdinaryCallbackReady compiler env ctx st.core.vals.val)
    (shape : Body.Control.Shape st.core) :
    code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx typeIndex 17#u8 compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.core.vals.val ⦄ := by
  rw [Body.CallbackTrace.dispatch_call_indirect]
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
end Itasca.Compiler

end

end

end
