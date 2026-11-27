import Itasca.Runtime.Compiler.Local.Source.TypedRunClosed
import Itasca.Visitor.BodyReplay
import Itasca.Visitor.RunTrace
import Itasca.Body.Step.Context
import Itasca.Runtime.Compiler.Local.Relations.Syntax.MiscOpcodes
import Itasca.Body.Bulk.Step
import Itasca.Runtime.Compiler.Body.Control.StructuredPrefixes
import Itasca.Runtime.Compiler.Body.Reader.Replay.MetadataTypes
import Itasca.Runtime.Compiler.Body.Reader.Control.Reachability
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerAuxiliaryTables
import Itasca.Runtime.Compiler.Local.Relations.Operations.CoreBasicEmissions
import Itasca.Runtime.Compiler.Local.Relations.Stacks.ConcretePops
import Itasca.Runtime.Compiler.Body.Callbacks.CompilerPrefixStart
import Itasca.Runtime.Compiler.Local.Relations.Syntax.ReaderOpcode
import Itasca.Body.NumericExt.Total
import Itasca.Handler.ScalarOperations
import Itasca.Runtime.Compiler.Body.Reader.Safety.Run
import Itasca.Runtime.Compiler.Body.Reader.Calls.Instructions

open WebAssembly

/-!
Proofs for Runtime / Compiler / Body / Reader / Replay.

This module collects BulkAndSaturatingAcceptance, ReaderCompilerState, Safety.
Each section documents its contracts and consumers.
-/

/-! ## BulkAndSaturatingAcceptance -/

section

/-! ## Agreement -/

section

/-!
Agreement between shared scalar readers and complete body dispatch.

Main declarations: `scalar_eq` and `base_success`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem scalar_eq {V : Type} (visitor : code.OpVisitor V)
    (st : code.BodyState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (index : U32) (opcode : U8) (before : V)
    (ordinary : opcode.val ∉ Body.controlOpcodes) :
    code.step_body visitor st data env ctx index opcode before =
      (if alloc.vec.Vec.len st.core.vals = core.num.Usize.MAX then
        .ok (.Err .StackTooLarge, st, before)
      else do
        let (reply, state, after) ← code.step_wasm2 visitor st.core data env ctx opcode before
        let cf ← core.result.Result.Insts.CoreOpsTry.branch reply
        match cf with
        | .Continue _ => .ok (.Ok (), {core := state}, after)
        | .Break residual =>
          let error ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual Unit
            (core.convert.FromSame error.OpError) residual
          .ok (error, {core := state}, after)) := by
  have hok : core.result.Result.Insts.CoreOpsTry.branch
      (.Ok () : core.result.Result Unit error.OpError) = .ok (.Continue ()) := rfl
  simp only [code.step_body, bind_ok, hok]
  split <;> try rfl
  all_goals exact False.elim (ordinary (by decide))

theorem scalar_success {V : Type} (visitor : code.OpVisitor V)
    (st out : code.BodyState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (index : U32) (opcode : U8) (before after : V)
    (ordinary : opcode.val ∉ Body.controlOpcodes)
    (accepted : code.step_body visitor st data env ctx index opcode before = .ok (.Ok (), out, after)) :
    st.core.vals.val.length < Usize.max ∧
      code.step_wasm2 visitor st.core data env ctx opcode before = .ok (.Ok (), out.core, after) := by
  rw [scalar_eq visitor st data env ctx index opcode before ordinary] at accepted
  by_cases full : alloc.vec.Vec.len st.core.vals = core.num.Usize.MAX
  · simp [full] at accepted
  · rw [if_neg full] at accepted
    obtain ⟨⟨reply, state, changed⟩, called, tail⟩ := Computation.bind_ok_inv _ _ _ accepted
    simp only [Std.uncurry] at tail
    cases reply with
    | Err error =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at tail
    | Ok unit =>
      cases unit
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        Result.ok.injEq, Prod.mk.injEq, true_and] at tail
      obtain ⟨rfl, rfl⟩ := tail
      refine ⟨?_, called⟩
      have length := st.core.vals.property
      have notFull : st.core.vals.val.length ≠ Usize.max := by
        intro equal
        apply full
        apply (UScalar.eq_equiv _ _).mpr
        simpa [core.num.Usize.MAX] using equal
      omega

/-- Successful ordinary Wasm 2 dispatch supplies both the reader capacity
and the exact scalar callback run, with the pending zipper's result context. -/
theorem base_success {V : Type} (visitor : code.OpVisitor V)
    (st out : code.BodyState) (data : Slice U8) (env : metadata.Env) (ctx ctx' : code.Context)
    (index : U32) (opcode : U8) (before after : V)
    (ordinary : opcode.val ∉ Body.controlOpcodes)
    (base : opcode.val ∉ [28, 37, 38, 208, 209, 210, 252, 253])
    (sign : Body.NumericExtensions.signMeaning opcode = none)
    (misc : opcode ≠ code.OP_MISC_PREFIX) (locals : ctx.locals = ctx'.locals)
    (accepted : code.step_body visitor st data env ctx index opcode before = .ok (.Ok (), out, after)) :
    st.core.vals.val.length < Usize.max ∧
      code.step visitor st.core data env ctx' opcode before = .ok (.Ok (), out.core, after) := by
  obtain ⟨capacity, run⟩ := scalar_success visitor st out data env ctx index opcode before after ordinary accepted
  rw [code.step_wasm2.base _ _ _ _ _ _ _ base,
    code.step_extended.base _ _ _ _ _ _ _ sign misc,
    Body.scalar_context _ _ _ _ ctx ctx' _ _ ordinary locals] at run
  exact ⟨capacity, run⟩

end Itasca.Compiler

end

/-! ## BulkAndSaturatingAcceptance -/

section

/-!
Accepted subopcode classification for saturating conversions and the ten bulk operations.

Main declarations: `reader_bulk_accepted_subopcode` and `reader_misc_accepted`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- The actual bulk dispatcher accepts only its ten source subopcodes. -/
theorem reader_bulk_accepted_subopcode {V} (visitor : code.OpVisitor V)
    (st out : code.OpIterState) (data : Slice U8) (env : metadata.Env) (sub : U32)
    (before after : V)
    (accepted : code.step_bulk visitor st data env sub before = .ok (.Ok (),out,after)) :
    sub.val ∈ [8,9,10,11,12,13,14,15,16,17] := by
  rw [code.step_bulk.eq_runs] at accepted
  unfold Body.bulkStep at accepted
  split at accepted <;> first | decide | simp_all

theorem misc_opcode_of_lt_eight (sub : U32) (small : sub.val < 8) : MiscOpcode sub := by
  have meaning : ∃ operation, Body.NumericExtensions.saturatingMeaning sub = some operation := by
    rcases sub with ⟨⟨value,bound⟩⟩
    change value < 8 at small
    interval_cases value <;> exact ⟨_,rfl⟩
  obtain ⟨operation,meaning⟩ := meaning
  obtain ⟨op,extended,number,_⟩ := saturating_float_descriptor meaning
  exact .inl ⟨op,extended,number⟩

/-- Recognition of a misc instruction comes from the actual successful
reader; no independent encoding of the unconsumed suffix is assumed. -/
theorem reader_misc_accepted {V} (visitor : code.OpVisitor V)
    (st out : code.BodyState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (index : U32) (before after : V)
    (accepted : code.step_body visitor st data env ctx index 252#u8 before =
      .ok (.Ok (),out,after)) :
    ∃ sub next, Binary.Leb128.Decoded data st.core.pos sub next ∧ MiscOpcode sub := by
  obtain ⟨_,run⟩ := scalar_success visitor st out data env ctx index 252#u8 before after
    (by decide) accepted
  rw [code.step_wasm2.prefixed] at run
  obtain ⟨result,read,decoded⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data st.core.pos)
  simp only [Body.miscellaneousStep,read,bind_ok] at run
  cases result with
  | Err error => simp at run
  | Ok pair =>
    obtain ⟨sub,next⟩ := pair
    by_cases small : sub < 8#u32
    · exact ⟨sub,next,decoded,misc_opcode_of_lt_eight sub (by scalar_tac)⟩
    · simp only [if_neg small] at run
      exact ⟨sub,next,decoded,.inr (reader_bulk_accepted_subopcode visitor _ _ data env sub before after run)⟩
end Itasca.Compiler

end

end

/-! ## ReaderCompilerState -/

section

/-!
Proofs for Runtime / Compiler / Body / Reader / Replay.

This module collects SkippedOperation, ReaderCompilerState.
Each section documents its contracts and consumers.
-/

/-! ## SkippedOperation -/

section

/-!
Structured reader prefixes for skipped source instructions.

Main declarations: `Body.ReaderPost.structured_skip`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem _root_.Itasca.Body.ReaderPost.structured_skip {jumpTables : List U32} {data env sourceLocals index st}
    {p : Body.Pending data env sourceLocals index st} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A} {out : code.OpIterState}
    {emit types functions returns locals parents current instruction poly values}
    (post : Body.ReaderPost p out instruction poly values)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (dead : before.reachable = false)
    (ordinary : CompilerOrdinaryStable before after) (sources : SourceProgress before after)
    (cursor : after.next_source = out.pos)
    (opcode : U16) (a b : U32) (bits : U128)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before out opcode a b bits = .ok (.Ok (),after)) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance instruction)
      out.vals.val out.pos.val ∧ after.reachable = false := by
  have effect := compiler_dead_op_fields ops law before out opcode a b bits dead
  rw [accepted,WP.spec_ok] at effect
  have consumed : p.start.val < out.pos.val := by have position := p.pos; have span := post.span; omega
  exact ⟨invariant.skip instruction dead effect.2.2.2 ordinary effect.1 sources consumed (by rw [cursor]),effect.2.2.2⟩
end Itasca.Compiler

end

/-! ## ReaderCompilerState -/

section

/-!
# Reader Compiler State

Structured reader states and indexed compiler preservation relate replayed callbacks to the retained compiler state.
-/

/-! ## StructuredState -/

section

/-!
The shared state invariant for structured source/compiler replay.

Main declarations: `StructuredReaderCompilerState`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

structure StructuredReaderCompilerState (jumpTables : List U32) (emit : List valtype → instr → List Bytecode → List valtype → Prop) {A : Type}
    (initial compiler : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (data : Slice U8) (env : metadata.Env) (sourceLocals : alloc.vec.Vec Itasca.wasm_types.ValueType)
    (index : U32) (ft : Itasca.wasm_types.FuncType) (st : code.BodyState)
    (parents : List SourceScope) (current : SourceScope)
    (savedParents : List Body.Frames.Saved) (savedCurrent : Body.Frames.Saved) : Prop where
  compiled : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial compiler types functions returns locals parents current st.core.vals.val st.core.pos.val
  boundary : ReaderBoundary data env sourceLocals index ft st savedParents savedCurrent
  sources : ReaderScopeZipper parents current savedParents savedCurrent
  reach : BodyReaderReachability compiler.reachable parents current savedParents savedCurrent
  fronts : ReaderScopeFronts parents current (savedParents.map Body.Frames.Saved.vals)
  knownFronts : ReaderKnownFronts parents current (savedParents.map Body.Frames.Saved.vals)

theorem StructuredReaderCompilerState.advance {jumpTables : List U32} {A : Type}
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env sourceLocals index ft st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerState (jumpTables := jumpTables) emit initial before types functions returns locals data env sourceLocals index ft
      st parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    {out instruction poly values}
    (post : Body.ReaderPost (state.boundary.pending next advance inbounds) out instruction poly values)
    (declared : Spec.DeclaredReferences.Instruction (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) instruction)
    (compiled : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance instruction)
      out.vals.val out.pos.val) (mono : after.reachable = true → poly = false) :
    StructuredReaderCompilerState (jumpTables := jumpTables) emit initial after types functions returns locals data env sourceLocals index ft {core := out}
      parents (current.advance instruction) savedParents
      (savedCurrent.advance (.plain instruction) instruction poly values) :=
  ⟨compiled, post.boundary declared, state.sources.advance _ _ _ _, state.reach.advance _ _ _ _ _ mono,
    state.fronts.advance instruction, state.knownFronts.advance instruction⟩

end Itasca.Compiler

end

/-! ## StructuredPoint -/

section

/-!
The structured source/compiler point extracted from a reader state.

Main declarations: `StructuredReaderCompilerPoint`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

def StructuredReaderCompilerPoint (jumpTables : List U32) (emit : List valtype → instr → List Bytecode → List valtype → Prop) {A : Type}
    (initial compiler : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (data : Slice U8) (env : metadata.Env) (sourceLocals : alloc.vec.Vec Itasca.wasm_types.ValueType)
    (index : U32) (ft : Itasca.wasm_types.FuncType) (st : code.BodyState) : Prop :=
  ∃ parents current savedParents savedCurrent,
    StructuredReaderCompilerState (jumpTables := jumpTables) emit initial compiler types functions returns locals data env sourceLocals index ft st
      parents current savedParents savedCurrent

theorem StructuredReaderCompilerState.point {jumpTables : List U32} {A : Type}
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env sourceLocals index ft st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerState (jumpTables := jumpTables) emit initial compiler types functions returns locals data env sourceLocals index ft st
      parents current savedParents savedCurrent) :
    StructuredReaderCompilerPoint (jumpTables := jumpTables) emit initial compiler types functions returns locals data env sourceLocals index ft st :=
  ⟨parents, current, savedParents, savedCurrent, state⟩
end Itasca.Compiler

end

/-! ## IndexedPoint -/

section

/-!
The shared reader/compiler point indexed by emitted jump and control tables.

Main declarations: `IndexedTableReaderCompilerPoint`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std

structure IndexedTableReaderCompilerPoint
    (emit : CompilerTables → List valtype → instr → List Bytecode → List valtype → Prop) {A : Type}
    (initial compiler : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (data : Slice U8) (env : Itasca.metadata.Env) (sourceLocals : alloc.vec.Vec Itasca.wasm_types.ValueType)
    (index : U32) (ft : Itasca.wasm_types.FuncType) (st : Itasca.code.BodyState) : Prop where
  tables : CompilerTableBoundary compiler
  future : ∀ more, StructuredReaderCompilerPoint
    ((CompilerTables.ofFunction compiler.function).append more).jumpTables
    (emit ((CompilerTables.ofFunction compiler.function).append more))
    initial compiler types functions returns locals data env sourceLocals index ft st

theorem IndexedTableReaderCompilerPoint.append_step {A : Type}
    {emit initial before after types functions returns locals data env sourceLocals index ft st out}
    (point : @IndexedTableReaderCompilerPoint emit A initial before types functions returns locals data env sourceLocals index ft st)
    (extra : CompilerTables)
    (tables : CompilerTables.ofFunction after.function = (CompilerTables.ofFunction before.function).append extra)
    (boundary : CompilerTableBoundary after)
    (step : ∀ future, StructuredReaderCompilerPoint
      ((CompilerTables.ofFunction after.function).append future).jumpTables
      (emit ((CompilerTables.ofFunction after.function).append future))
      initial before types functions returns locals data env sourceLocals index ft st →
      StructuredReaderCompilerPoint
        ((CompilerTables.ofFunction after.function).append future).jumpTables
        (emit ((CompilerTables.ofFunction after.function).append future))
        initial after types functions returns locals data env sourceLocals index ft out) :
    IndexedTableReaderCompilerPoint emit initial after types functions returns locals data env sourceLocals index ft out := by
  refine ⟨boundary, ?_⟩
  intro future
  apply step future
  simpa only [tables,CompilerTables.append_assoc] using point.future (extra.append future)
end Itasca.Compiler

end

/-! ## DormantOperation -/

section

/-!
Dormant structured prefixes for omitted source operations.

Main declarations: `Body.ReaderPost.structured_dead_op`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem _root_.Itasca.Body.ReaderPost.structured_dead_op {jumpTables : List U32} {data env sourceLocals index st}
    {p : Body.Pending data env sourceLocals index st} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A} {out : code.OpIterState}
    {emit types functions returns locals parents current instruction poly values}
    (post : Body.ReaderPost p out instruction poly values)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (dead : before.reachable = false)
    (opcode : U16) (a b : U32) (bits : U128)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before out opcode a b bits = .ok (.Ok (), after)) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance instruction) out.vals.val out.pos.val ∧ after.reachable = false := by
  have consumed : p.start.val < out.pos.val := by have position := p.pos; have span := post.span; omega
  refine ⟨invariant.dead_op ops law out instruction opcode a b bits dead consumed accepted, ?_⟩
  have observed := compiler_op_dead ops law before out opcode a b bits dead
  rw [accepted, WP.spec_ok] at observed
  exact observed.reachable.trans dead

end Itasca.Compiler

end

/-! ## CompilerBounds -/

section

/-!
Source-coordinate and body bounds retained by reader and compiler states.

Main declarations: `ReaderBoundary.source_bound` and `CompilerStable.body_bound`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem ReaderBoundary.source_bound {data env locals index ft st parents current}
    (boundary : ReaderBoundary data env locals index ft st parents current) :
    data.length ≤ limits.MAX_MODULE_BYTES.val := by
  have bound := boundary.bounds.size
  have cap : limits.MAX_FUNCTION_BYTES.val ≤ limits.MAX_MODULE_BYTES.val := by
    norm_num [limits.MAX_FUNCTION_BYTES, limits.MAX_MODULE_BYTES]
  exact bound.trans cap

/-- All body callbacks retain the absolute source origin, so the initial
entry-span bound remains valid throughout the compiler fold. -/
theorem CompilerStable.body_bound {A : Type}
    {initial current : runtime.compiler.FunctionCompiler A}
    (stable : CompilerStable initial current) {length : Nat}
    (bound : initial.function.body_start.val + length ≤ Usize.max) :
    current.function.body_start.val + length ≤ Usize.max := by
  rw [stable.fields.2.2.2.2.2.2.2.1]
  exact bound
end Itasca.Compiler

end

/-! ## IndexedPreserved -/

section

/-!
Preservation of an indexed reader/compiler point across one step.

Main declarations: `IndexedTableReaderCompilerPoint.preserved_step`.
-/

namespace Itasca.Compiler
open Aeneas.Std

theorem IndexedTableReaderCompilerPoint.preserved_step {A : Type}
    {emit initial before after types functions returns locals data env sourceLocals index ft st out}
    (point : @IndexedTableReaderCompilerPoint emit A initial before types functions returns locals data env sourceLocals index ft st)
    (tables : CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function)
    (depths : after.table_depths = before.table_depths)
    (growth : before.function.code.val.length ≤ after.function.code.val.length)
    (step : ∀ future, StructuredReaderCompilerPoint ((CompilerTables.ofFunction before.function).append future).jumpTables (emit ((CompilerTables.ofFunction before.function).append future))
      initial before types functions returns locals data env sourceLocals index ft st →
      StructuredReaderCompilerPoint ((CompilerTables.ofFunction before.function).append future).jumpTables (emit ((CompilerTables.ofFunction before.function).append future))
      initial after types functions returns locals data env sourceLocals index ft out) :
    IndexedTableReaderCompilerPoint emit initial after types functions returns locals data env sourceLocals index ft out := by
  refine ⟨⟨by simpa only [depths] using point.tables.depths, ?_⟩, ?_⟩
  · have targets := congrArg CompilerTables.jumpTables tables
    change after.function.jump_tables.val = before.function.jump_tables.val at targets
    simpa only [targets] using point.tables.targets.trans growth
  · intro future
    simpa only [tables] using step future (point.future future)
end Itasca.Compiler

end

end

end

/-! ## Safety -/

section

/-! ## OpcodeClassification -/

section

/-!
An unrecognized base opcode rejects before visiting the compiler.

Main declarations: `reader_opcode_base` and `reader_accepted_opcode`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

/-- An unrecognized base opcode rejects before visiting the compiler. -/
theorem reader_opcode_base {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (opcode : U8) (value : V) :
    BaseOpcode opcode ∨
    code.step visitor st data env ctx opcode value =
      .ok (.Err error.OpError.UnrecognizedOpcode,st,value) := by
  by_cases supported : BaseOpcode opcode
  · exact .inl supported
  right
  by_cases high : 69 ≤ opcode.val
  · rw [code.step.numeric_dispatch visitor st data env ctx opcode value high]
    cases meaning : Body.Numeric.opcodeMeaning opcode with
    | none => exact code.step_numeric.unrecognized visitor st opcode value meaning
    | some operation => exact False.elim (supported (numeric_base_opcode meaning))
  · apply code.step.reserved
    rcases opcode with ⟨⟨index,bound⟩⟩
    change ¬ 69 ≤ index at high
    have upper : index ≤ 68 := by omega
    interval_cases index <;> first | (exfalso; apply supported; reader_opcode) | (clear supported; decide +revert)

/-- Extension dispatch likewise rejects every opcode outside the supported
instruction grammar, independently of the reader or visitor state. -/
theorem reader_opcode {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (opcode : U8) (value : V) :
    ReaderOpcode opcode ∨
    code.step_wasm2 visitor st data env ctx opcode value =
      .ok (.Err error.OpError.UnrecognizedOpcode,st,value) := by
  by_cases supported : ReaderOpcode opcode
  · exact .inl supported
  right
  have base : opcode.val ∉ [28,37,38,208,209,210,252,253] := by
    intro member
    rcases opcode with ⟨⟨index,bound⟩⟩
    change index ∈ _ at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    apply supported
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reader_opcode
  have sign : Body.NumericExtensions.signMeaning opcode = none := by
    cases meaning : Body.NumericExtensions.signMeaning opcode with
    | none => rfl
    | some operation => exact False.elim (supported (sign_reader_opcode meaning))
  have misc : opcode ≠ code.OP_MISC_PREFIX := fun equal => supported (.misc (by simpa [code.OP_MISC_PREFIX] using equal))
  rw [code.step_wasm2.base visitor st data env ctx opcode value base,
    code.step_extended.base visitor st data env ctx opcode value sign misc]
  rcases reader_opcode_base visitor st data env ctx opcode value with known | rejected
  · exact False.elim (supported known.reader)
  · exact rejected

theorem reader_accepted_opcode {V : Type} (visitor : code.OpVisitor V)
    (st final : code.BodyState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (typeIndex : U32) (opcode : U8) (value after : V)
    (accepted : code.step_body visitor st data env ctx typeIndex opcode value =
      .ok (.Ok (),final,after)) : ReaderOpcode opcode := by
  by_contra unknown
  have rejected := (reader_opcode visitor st.core data env ctx opcode value).resolve_left unknown
  have hok : core.result.Result.Insts.CoreOpsTry.branch
      (.Ok () : core.result.Result Unit error.OpError) = .ok (.Continue ()) := rfl
  unfold code.step_body at accepted
  simp only [bind_ok, hok] at accepted
  split at accepted
  all_goals try { exfalso; apply unknown; reader_opcode }
  all_goals
    split at accepted
    · simp at accepted
    · simp [rejected,core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
end Itasca.Compiler

end

/-! ## BodySafety -/

section

/-!
Body-state readers invoke the compiler only after their actual successful parse and validation result. Rejections on either side return normally.

Main declarations: `reader_body_run_reached`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Body Itasca.Visitor.Trace

/-- Body-state readers invoke the compiler only after their actual successful
parse and validation result. Rejections on either side return normally. -/
theorem reader_body_run_reached {T V : Type}
    (read : Result (core.result.Result T error.OpError × code.BodyState))
    (visitor : code.OpVisitor V) (action : T → Action)
    (before : V) (post : code.BodyState → V → Prop)
    (reader : read ⦃ _ => True ⦄)
    (callback : ∀ state value, read = .ok (.Ok value,state) →
      invoke visitor before (.op state.core (action value)) ⦃ out => out.1 = .Ok () → post state out.2 ⦄) :
    CallbackTrace.bodyRun read visitor action before ⦃ out =>
      out.1 = .Ok () → post out.2.1 out.2.2 ⦄ := by
  obtain ⟨⟨result,state⟩,readEq,_⟩ := WP.spec_imp_exists reader
  cases result with
  | Err error => simp [CallbackTrace.bodyRun,readEq]
  | Ok value =>
    obtain ⟨⟨result,after⟩,called,ready⟩ := WP.spec_imp_exists (callback state value readEq)
    cases result with
    | Err error => simp [CallbackTrace.bodyRun,readEq,called,hookResult]
    | Ok unitValue =>
      cases unitValue
      simpa [CallbackTrace.bodyRun,readEq,called,hookResult,WP.spec_ok] using ready rfl
end Itasca.Compiler

end

/-! ## Safety -/

section

/-!
The actual body capacity guard is checked before ordinary decoding. Only the non-full branch needs the corresponding scalar-reader theorem.

Main declarations: `reader_scalar_reached`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- The actual body capacity guard is checked before ordinary decoding.
Only the non-full branch needs the corresponding scalar-reader theorem. -/
theorem reader_scalar_reached {V} (visitor : code.OpVisitor V)
    (st : code.BodyState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (index : U32) (opcode : U8) (before : V) (post : code.OpIterState → V → Prop)
    (ordinary : opcode.val ∉ Body.controlOpcodes)
    (step : st.core.vals.val.length < Usize.max →
      code.step_wasm2 visitor st.core data env ctx opcode before ⦃ out =>
        out.1 = .Ok () → post out.2.1 out.2.2 ⦄) :
    code.step_body visitor st data env ctx index opcode before ⦃ out =>
      out.1 = .Ok () → post out.2.1.core out.2.2 ⦄ := by
  rw [scalar_eq visitor st data env ctx index opcode before ordinary]
  by_cases full : alloc.vec.Vec.len st.core.vals = core.num.Usize.MAX
  · simp [full]
  · rw [if_neg full]
    have capacity : st.core.vals.val.length < Usize.max := by
      have length := st.core.vals.property
      have notFull : st.core.vals.val.length ≠ Usize.max := by
        intro equal
        apply full
        apply (UScalar.eq_equiv _ _).mpr
        simpa [core.num.Usize.MAX] using equal
      omega
    obtain ⟨⟨reply,state,after⟩,run,success⟩ := WP.spec_imp_exists (step capacity)
    rw [run]
    cases reply with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok unitValue =>
      cases unitValue
      simpa only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Std.uncurry,WP.spec_ok] using success
end Itasca.Compiler

end

end
