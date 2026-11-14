import Itasca.Runtime.Compiler.Body.Control.Table.StructuredCompilerPrefixFinish
import Itasca.Runtime.Compiler.Local.Control.Simd.StructuredSimdEmbedding
import Itasca.Runtime.Compiler.Body.Reader.Simd.SimdEmissions
import Itasca.Runtime.Compiler.Body.Reader.Replay.SkippedOperation
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerAuxiliaryTables
import Itasca.Runtime.Compiler.Body.Reader.Simd.Dispatch
import Itasca.Runtime.Compiler.Body.Reader.Replay.IndexedPreserved
import Itasca.Runtime.Compiler.Body.Reader.Stateful.ExtendedScratch
import Itasca.Runtime.Compiler.Body.Reader.Stateful.ExtendedCodeMonotone
import Itasca.Runtime.Compiler.Local.Lowering.Simd.SimdBitsCallbacks
import Itasca.Runtime.Compiler.Body.Reader.Safety.Run
import Itasca.Runtime.Compiler.Body.Relations.Calls.ControlCallbackReady
import Itasca.Runtime.Compiler.Local.Lowering.Simd.SimdInstructionAcceptance
import Itasca.Wasm2.Simd.LaneReaders
import Itasca.Runtime.Compiler.Body.Reader.Acceptance.ReachedReferenceDemand
import Itasca.Binary.Wasm1.EncodingUnique
import Itasca.Runtime.Compiler.Local.Coordinates.ScalarTargetEffects
import Itasca.Runtime.Compiler.Local.Publication.StartMapPublication
import Itasca.Visitor.Events

/-!
Sections, each formerly its own module: Prefix, SimdEventTables, IndexedTableCompilerSimd, SimdSafety, SimdPrefixAcceptance, SimdCallbackPublication.
-/

/-! ## Prefix -/

section

/-!
SIMD emitted and callback prefixes and their structured event composition, preserving table and dead-code metadata.
-/

/-! ## Reader Prefix Simd -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem _root_.Itasca.Wasm2.ReaderPost.simd_dead_prefix {jumpTables : List U32} {data env sourceLocals index st}
    {p : Wasm2.Pending data env sourceLocals index st} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A} {out : code.OpIterState}
    {emit types functions returns locals parents current source poly values}
    (post : Wasm2.ReaderPost p out source poly values)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (dead : before.reachable = false) (opcode : U16) (a b : U32) (bits : U128)
    (lower : 512 ≤ opcode.val) (upper : opcode.val < 768)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before out opcode a b bits = .ok (.Ok (),after)) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance source)
      out.vals.val out.pos.val ∧ after.reachable = false ∧
      CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function := by
  obtain ⟨ordinary,sources,cursor,capacity⟩ := compiler_lower_simd_effects ops law before after out opcode a b bits lower upper accepted
  obtain ⟨prefixProof,deadAfter⟩ := post.structured_skip ops law invariant dead ordinary sources cursor opcode a b bits accepted
  rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (dead)] at accepted
  exact ⟨prefixProof,deadAfter,compiler_observe_tables ops law before after out (.Ok ()) accepted⟩
end Itasca.Runtime.Compiler

end

/-! ## Reader Prefix Simd Callback -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- The complete SIMD prefix step handles live emission and polymorphic dead
code, retaining an exact append witness for all function tables. -/
theorem _root_.Itasca.Wasm2.ReaderPost.simd_callback_prefix {jumpTables : List U32} {data env sourceLocals index st source values position inputs output}
    {p : Wasm2.Pending data env sourceLocals index st} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A} {out : code.OpIterState}
    (C : context) {emit} [SimdEmbedding after.function.simd.val after.function.v128_pool.val C emit]
    {types functions returns locals parents current}
    (post : Wasm2.ReaderPost p out source p.current.ctrl.polymorphic_base values)
    (effect : Wasm2.Simd.FixedEffect p.current.ctrl.polymorphic_base p.current.vals inputs output values)
    (read : Wasm2.Simd.readFixed {st.core with pos := position} inputs output = .ok (.Ok (),out))
    (capacity : st.core.vals.val.length < Usize.max)
    (contextLocals : C.LOCALS = locals)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (opcode : U16) (sub a b : U32) (bits : U128)
    (number : opcode.val = 512 + sub.val)
    (meaning : SimdCallbackMeaning C sub a bits inputs source output)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before out opcode a b bits = .ok (.Ok (),after)) :
    ∃ extra, CompilerTables.ofFunction after.function = (CompilerTables.ofFunction before.function).append extra ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance source)
        out.vals.val out.pos.val ∧
      (after.reachable = true → p.current.ctrl.polymorphic_base = false) := by
  cases reachable : before.reachable with
  | false =>
    have bound := meaning.opcode_bound
    obtain ⟨prefixProof,dead,tables⟩ := post.simd_dead_prefix ops law invariant reachable opcode a b bits
      (by omega) (by omega) accepted
    refine ⟨CompilerTables.empty,?_,prefixProof,by simp [dead]⟩
    simpa only [CompilerTables.append_empty] using tables
  | true =>
    obtain ⟨entered,retained⟩ := invariant.live reachable
    have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
    obtain ⟨codeFits,sourceFits,_,_⟩ := invariant.capacities bound
    have coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max := by
      have cursor := invariant.cursor
      have position := p.inbounds
      omega
    obtain ⟨ordinary,sources,cursor,extra,front,emitted,tables,oldTypes,lowered,emission⟩ :=
      reader_simd_callback_emission p ops law before after out C opcode sub a b bits number meaning post effect read
        (invariant.known reachable) (monomorphic reachable) capacity (contextLocals.trans retained.localsEq.symm)
        retained.layout reachable codeFits sourceFits coordinateFits accepted
    have consumed : p.start.val < out.pos.val := by have pos := p.pos; have span := post.span; omega
    refine ⟨extra,tables,?_,fun _ => monomorphic reachable⟩
    apply invariant.ordinary reachable ordinary lowered _ sources consumed (by rw [cursor]) emission.not_branch_table
    simpa only [oldTypes] using (SimdEmbedding.lift (emit := emit) emission)
end Itasca.Runtime.Compiler

end

/-! ## Reader Simd Event Prefix -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca
theorem SimdReaderEvent.prefix {jumpTables : List U32} {A : Type} {ops : runtime.platform.Alloc A}
    {data env sourceLocals index st p initial before after out C}
    (event : @SimdReaderEvent A ops data env sourceLocals index st p before after out C)
    (law : Platform.AllocCorrect ops)
    {emit} [SimdEmbedding after.function.simd.val after.function.v128_pool.val C emit]
    {types functions returns locals parents current}
    (contextLocals : C.LOCALS = locals)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max) :
    ∃ extra, CompilerTables.ofFunction after.function = (CompilerTables.ofFunction before.function).append extra ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance event.source)
        out.vals.val out.pos.val ∧ (after.reachable = true → p.current.ctrl.polymorphic_base = false) :=
  event.post.simd_callback_prefix ops law C event.effect event.read event.capacity contextLocals invariant monomorphic
    event.opcode event.sub event.a event.b event.bits event.number event.meaning sourceBound bodyBound event.callback
end Itasca.Runtime.Compiler

end

end

/-! ## SimdEventTables -/

section

/-!
Compiler table metadata retained by SIMD reader events.

Main declarations: `SimdReaderEvent.tables`. A direct consumer is `Compiler.Body.Reader.Simd.IndexedTableCompilerSimd`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem SimdReaderEvent.tables {jumpTables : List U32} {A : Type} {ops : runtime.platform.Alloc A}
    {data env sourceLocals index st p initial before after out C}
    (event : @SimdReaderEvent A ops data env sourceLocals index st p before after out C)
    (law : Platform.AllocCorrect ops)
    {emit types functions returns locals parents current}
    (contextLocals : C.LOCALS = locals)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max) :
    ∃ extra, CompilerTables.ofFunction after.function = (CompilerTables.ofFunction before.function).append extra := by
  cases reachable : before.reachable with
  | false =>
    have bound := event.meaning.opcode_bound
    have number := event.number
    obtain ⟨prefixProof,dead,tables⟩ := event.post.simd_dead_prefix ops law invariant reachable event.opcode event.a event.b event.bits
      (by omega) (by omega) event.callback
    exact ⟨CompilerTables.empty,by simpa only [CompilerTables.append_empty] using tables⟩
  | true =>
    obtain ⟨entered,retained⟩ := invariant.live reachable
    have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
    obtain ⟨codeFits,sourceFits,_,_⟩ := invariant.capacities bound
    have coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max := by
      have cursor := invariant.cursor
      have position := p.inbounds
      omega
    obtain ⟨ordinary,sources,cursor,extra,front,emitted,tables,oldTypes,lowered,emission⟩ :=
      reader_simd_callback_emission p ops law before after out C event.opcode event.sub event.a event.b event.bits event.number
        event.meaning event.post event.effect event.read (invariant.known reachable) (monomorphic reachable) event.capacity
        (contextLocals.trans retained.localsEq.symm) retained.layout reachable codeFits sourceFits coordinateFits event.callback
    exact ⟨extra,tables⟩
end Itasca.Runtime.Compiler

end

/-! ## IndexedTableCompilerSimd -/

section

/-!
SIMD compilation under the structured reader invariant and the indexed compiler-table invariant.
-/

/-! ## Structured Reader Compiler Simd -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Actual SIMD dispatch extends the same canonical source zipper and the
structured compiler state, including dead code and exact table growth. -/
theorem StructuredReaderCompilerStateWasm2.simd {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (C : context) (contextLocals : C.LOCALS = locals)
    (contextMemories : C.MEMS = env.mem_types.val.map EnvTranslation.memType)
    {emit} [SimdEmbedding after.function.simd.val after.function.v128_pool.val C emit]
    (state : StructuredReaderCompilerStateWasm2 jumpTables emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = 0xfd#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index 0xfd#u8 before = .ok (.Ok (),out,after)) :
    ∃ extra, CompilerTables.ofFunction after.function = (CompilerTables.ofFunction before.function).append extra ∧
      StructuredReaderCompilerPointWasm2 jumpTables emit initial after types functions returns locals data env ctx.locals index ft out := by
  let p := state.boundary.pending next advance inbounds
  obtain ⟨event⟩ := reader_simd_event_wasm2 p ops before after out ctx C contextMemories byte accepted
  obtain ⟨extra,tables,compiled,mono⟩ := event.prefix law contextLocals state.compiled
    state.reach.current sourceBound bodyBound
  exact ⟨extra,tables,(state.advance next advance inbounds event.post (event.meaning.declared _) compiled mono).point⟩
end Itasca.Runtime.Compiler

end

/-! ## Indexed Table Reader Compiler Simd -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- SIMD dispatch preserves the compiler point quantified over future
extensions of every function table. The append witness comes from the actual
accepted callback before the old point is reindexed. -/
theorem IndexedTableReaderCompilerPointWasm2.simd {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx index ft st}
    (C : context) (contextLocals : C.LOCALS = locals)
    (contextMemories : C.MEMS = env.mem_types.val.map EnvTranslation.memType)
    {emit : CompilerTables → List valtype → instr → List Bytecode → List valtype → Prop}
    (embedding : ∀ tables, SimdEmbedding tables.simd tables.constants C (emit tables))
    (point : IndexedTableReaderCompilerPointWasm2 emit initial before types functions returns locals data env ctx.locals index ft st)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = 0xfd#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index 0xfd#u8 before = .ok (.Ok (),out,after)) :
    IndexedTableReaderCompilerPointWasm2 emit initial after types functions returns locals data env ctx.locals index ft out := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  let p := state.boundary.pending next advance inbounds
  obtain ⟨event⟩ := reader_simd_event_wasm2 p ops before after out ctx C contextMemories byte accepted
  obtain ⟨extra,tables⟩ := event.tables law contextLocals state.compiled state.reach.current sourceBound bodyBound
  have depths := event.depths law
  have growth := event.code_mono law
  have bound := event.meaning.opcode_bound
  have number := event.number
  have jumps := (compiler_lower_simd_preserved_tables ops law before after out.core
    event.opcode event.a event.b event.bits (by omega) (by omega) event.callback).2
  have boundary : CompilerTableBoundary after :=
    ⟨by simpa only [depths] using point.tables.depths,
      by simpa only [jumps] using point.tables.targets.trans growth⟩
  apply point.append_step extra tables boundary
  intro future beforePoint
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := beforePoint
  letI : SimdEmbedding ((CompilerTables.ofFunction after.function).append future).simd
      ((CompilerTables.ofFunction after.function).append future).constants C
      (emit ((CompilerTables.ofFunction after.function).append future)) := embedding _
  letI : SimdEmbedding after.function.simd.val after.function.v128_pool.val C
      (emit ((CompilerTables.ofFunction after.function).append future)) :=
    ⟨fun h => (embedding ((CompilerTables.ofFunction after.function).append future)).lift
      (h.append_tables future.simd future.constants)⟩
  obtain ⟨_,_,nextPoint⟩ := state.simd ops law C contextLocals contextMemories next advance inbounds out
    sourceBound bodyBound byte accepted
  exact nextPoint
end Itasca.Runtime.Compiler

end

end

/-! ## SimdSafety -/

section

/-!
Normal return of SIMD subopcode and top-level reader dispatch.

Main declarations: `compiler_reader_simd_sub_total` and `compiler_reader_simd_total`. A direct consumer is `Compiler.Body.Reader.Safety.OrdinarySafety`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Wasm2.Simd

theorem compiler_reader_simd_sub_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (sub : U32)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Control.Shape st) (capacity : st.vals.val.length < Usize.max) :
    subStep (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env sub compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  unfold subStep
  rw [pure_table]
  cases meaning : pureMeaning sub.val with
  | some op =>
    simp only [Option.map_some,bind_ok]
    refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
    · exact WP.spec_mono (signature_total _ _ shape capacity) (by simp)
    · intro state value read
      exact compiler_on_simd_total ops law compiler state sub (pure_bound meaning)
        ready.codeFits ready.sourceFits ready.coordinateFits ready.poolFits ready.simdFits
  | none =>
    simp only [Option.map_none,bind_ok]
    rw [lane_table]
    cases laneMeaningEq : laneMeaning sub.val with
    | some lane =>
      have bound : sub.val < 256 := by
        unfold laneMeaning at laneMeaningEq
        split at laneMeaningEq <;> first | contradiction | omega
      simp only [Option.map_some,bind_ok]
      rcases runtimeEq : lane.runtime with ⟨ty,count,replace⟩
      simp only
      refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
      · exact WP.spec_mono (read_lane_total _ _ _ _ _ shape capacity) (by simp)
      · intro state value read
        exact compiler_on_simd_lane_total ops law compiler state sub value bound
          ready.codeFits ready.sourceFits ready.coordinateFits ready.poolFits ready.simdFits
    | none =>
      simp only [Option.map_none,bind_ok]
      rw [memory_table]
      cases memoryMeaningEq : memoryMeaning sub.val with
      | some mem =>
        have bound : sub.val < 256 := by
          unfold memoryMeaning at memoryMeaningEq
          split at memoryMeaningEq <;> first | contradiction | omega
        simp only [Option.map_some,bind_ok]
        rcases runtimeEq : mem.runtime with ⟨align,store,count⟩
        simp only
        split
        · refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
          · exact WP.spec_mono (memory_lane_total _ _ _ _ _ _ shape capacity) (by simp)
          · intro state value read
            exact compiler_on_simd_memory_lane_total ops law compiler state sub value.1 value.2 bound
              ready.codeFits ready.sourceFits ready.coordinateFits ready.poolFits ready.simdFits
        · split
          · refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
            · exact WP.spec_mono (store_total _ _ _ _ _ shape) (by simp)
            · intro state value read
              exact compiler_on_simd_memory_total ops law compiler state sub value bound
                ready.codeFits ready.sourceFits ready.coordinateFits ready.poolFits ready.simdFits
          · refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
            · exact WP.spec_mono (load_total _ _ _ _ _ shape capacity) (by simp)
            · intro state value read
              exact compiler_on_simd_memory_total ops law compiler state sub value bound
                ready.codeFits ready.sourceFits ready.coordinateFits ready.poolFits ready.simdFits
      | none =>
        simp only [Option.map_none,bind_ok]
        split
        · refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
          · exact WP.spec_mono (constant_total _ _ shape capacity) (by simp)
          · intro state value read
            exact compiler_on_simd_const_total ops law compiler state value.1 value.2
              ready.codeFits ready.sourceFits ready.coordinateFits ready.poolFits ready.simdFits
        · refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
          · exact WP.spec_mono (shuffle_total _ _ shape capacity) (by simp)
          · intro state value read
            exact compiler_on_simd_shuffle_total ops law compiler state value.1 value.2
              ready.codeFits ready.sourceFits ready.coordinateFits ready.poolFits ready.simdFits
        · simp

/-- The actual SIMD prefix handles malformed subopcode LEBs and all six
callback families, with no accepted-reader or compiler-success premise. -/
theorem compiler_reader_simd_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Control.Shape st) (capacity : st.vals.val.length < Usize.max) :
    code.step_simd (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  rw [code.step_simd.eq_runs]
  unfold prefixStep
  obtain ⟨result,read,decoded⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data st.pos)
  rw [read]
  simp only [bind_ok]
  cases result with
  | Err error => simp
  | Ok pair =>
    obtain ⟨sub,next⟩ := pair
    exact compiler_reader_simd_sub_total ops law compiler {st with pos := next} data env ctx sub
      ready ⟨shape.ordered,shape.bounded⟩ capacity
end Itasca.Runtime.Compiler

end

/-! ## SimdPrefixAcceptance -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Independent decoding selects the exact successful source subopcode run. -/
theorem simd_sub_success_of_decoded {V : Type} (source : code.OpVisitor V)
    (st out : code.BodyState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (index : U32) (before after : V) (sub : U32) (next : Usize)
    (decoded : Leb128.Decoded data st.core.pos sub next)
    (reference : code.step_profile source st data env ctx index 253#u8 before = .ok (.Ok (),out,after)) :
    st.core.vals.val.length < Usize.max ∧
      Wasm2.Simd.subStep source {st.core with pos := next} data env sub before = .ok (.Ok (),out.core,after) := by
  obtain ⟨capacity,actual,position,bytes,called⟩ := simd_prefix_success source st out data env ctx index before after reference
  obtain ⟨rfl,rfl⟩ := bytes.unique decoded
  exact ⟨capacity,called⟩

/-- Replay the actual profile guard and unsigned-LEB prefix with an available
subopcode implementation. The target uses exactly the source-decoded cursor. -/
theorem simd_prefix_available {W : Type} (target : code.OpVisitor W)
    (st out : code.BodyState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (index : U32) (compiler : W) (sub : U32) (next : Usize) (post : W → Prop)
    (decoded : Leb128.Decoded data st.core.pos sub next)
    (capacity : st.core.vals.val.length < Usize.max)
    (acceptance : Wasm2.Simd.subStep target {st.core with pos := next} data env sub compiler
      ⦃ result => result.1 = .Ok () ∧ result.2.1 = out.core ∧ post result.2.2 ⦄) :
    code.step_profile target st data env ctx index 253#u8 compiler
      ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧ post result.2.2 ⦄ := by
  apply profile_scalar_available_wasm2 target st out.core data env ctx index 253#u8 compiler post capacity (by decide)
  rw [code.step_wasm2.simd,code.step_simd.eq_runs]
  have read := reader.read_u32_leb.complete data st.core.pos sub next decoded
  simpa only [Wasm2.Simd.prefixStep,read,bind_ok] using acceptance

end Itasca.Runtime.Compiler

end

/-! ## SimdCallbackPublication -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- SIMD visitor arguments use the Wasm 2 subopcode interval. Constant and
shuffle events carry their complete immediate bits directly. -/
inductive SimdPublicationAction : Action → Prop where
  | plain (sub : U32) (bound : sub.val < 256) : SimdPublicationAction (.simd sub)
  | lane (sub : U32) (lane : U8) (bound : sub.val < 256) : SimdPublicationAction (.simd_lane sub lane)
  | memory (sub : U32) (arg : code.MemArg) (bound : sub.val < 256) : SimdPublicationAction (.simd_memory sub arg)
  | memoryLane (sub : U32) (arg : code.MemArg) (lane : U8) (bound : sub.val < 256) :
      SimdPublicationAction (.simd_memory_lane sub arg lane)
  | constant (lo hi : U64) : SimdPublicationAction (.simd_const lo hi)
  | shuffle (lo hi : U64) : SimdPublicationAction (.simd_shuffle lo hi)

/-- All six SIMD event forms dispatch to a bounded ordinary compiler opcode. -/
theorem simd_hook_publication_dispatch {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : code.OpIterState)
    {action : Action} (supported : SimdPublicationAction action) :
    ∃ (opcode : U16) (a b : U32) (bits : U128), 512 ≤ opcode.val ∧ opcode.val < 768 ∧
      invoke (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) compiler (.op state action) =
        runtime.compiler.lower.FunctionCompiler.op ops compiler state opcode a b bits := by
  cases supported with
  | plain sub bound =>
    let opcode : U16 := ⟨⟨512+sub.val,by change 512+sub.val < 65536; omega⟩⟩
    exact ⟨opcode,0#u32,0#u32,0#u128,by change 512 ≤ 512+sub.val; omega,by change 512+sub.val < 768; omega,
      compiler_simd_callback ops compiler state sub opcode bound rfl⟩
  | lane sub lane bound =>
    let opcode : U16 := ⟨⟨512+sub.val,by change 512+sub.val < 65536; omega⟩⟩
    exact ⟨opcode,UScalar.cast .U32 lane,0#u32,0#u128,by change 512 ≤ 512+sub.val; omega,by change 512+sub.val < 768; omega,
      compiler_simd_lane_callback ops compiler state sub opcode bound rfl lane⟩
  | memory sub arg bound =>
    let opcode : U16 := ⟨⟨512+sub.val,by change 512+sub.val < 65536; omega⟩⟩
    exact ⟨opcode,arg.offset,arg.align,0#u128,by change 512 ≤ 512+sub.val; omega,by change 512+sub.val < 768; omega,
      compiler_simd_memory_callback ops compiler state sub opcode bound rfl arg⟩
  | memoryLane sub arg lane bound =>
    let opcode : U16 := ⟨⟨512+sub.val,by change 512+sub.val < 65536; omega⟩⟩
    exact ⟨opcode,arg.offset,arg.align,UScalar.cast .U128 lane,by change 512 ≤ 512+sub.val; omega,by change 512+sub.val < 768; omega,
      compiler_simd_memory_lane_callback ops compiler state sub opcode bound rfl arg lane⟩
  | constant lo hi =>
    exact ⟨524#u16,0#u32,0#u32,initializerBits lo hi,by decide,by decide,
      compiler_simd_constant_callback ops compiler state lo hi⟩
  | shuffle lo hi =>
    exact ⟨525#u16,0#u32,0#u32,initializerBits lo hi,by decide,by decide,
      compiler_simd_shuffle_callback ops compiler state lo hi⟩

/-- Actual SIMD visitor events preserve both publication invariants, including
unreachable code, memory lanes, constants, and shuffles. -/
theorem compiler_simd_hook_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : code.OpIterState) {action : Action} (supported : SimdPublicationAction action)
    (coordinates : SourceCoordinates before) (maps : ControlMapPublication before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (forward : before.next_source.val ≤ state.pos.val)
    (called : invoke (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before (.op state action) =
      .ok (.Ok (),after)) : SourceCoordinates after ∧ ControlMapPublication after := by
  obtain ⟨opcode,a,b,bits,lower,upper,dispatch⟩ := simd_hook_publication_dispatch ops before state supported
  rw [dispatch] at called
  exact ⟨compiler_simd_op_source_coordinates ops law before after state opcode a b bits lower upper
      coordinates inside forward called,
    compiler_lower_simd_map_publication ops law before after state opcode a b bits lower upper called maps forward⟩

end Itasca.Runtime.Compiler

end
