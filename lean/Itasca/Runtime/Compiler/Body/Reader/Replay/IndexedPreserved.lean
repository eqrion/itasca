import Itasca.Runtime.Compiler.Body.Control.Table.StructuredCompilerPrefixFinish
import Itasca.Runtime.Compiler.Body.Reader.Control.Reachability
import Itasca.Runtime.Compiler.Body.Reader.Control.Return
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerAuxiliaryTables
import Itasca.Runtime.Compiler.Local.Relations.Operations.CoreBasicEmissions
import Itasca.Runtime.Compiler.Body.Reader.Replay.MetadataTypes
import Itasca.Runtime.Compiler.Body.Reader.Replay.BulkAndSaturatingAcceptance
import Itasca.Runtime.Compiler.Local.Relations.Stacks.KnownNumericStack
import Itasca.Runtime.Compiler.Body.Callbacks.Prefix.CompilerPrefixStart

/-!
Sections, each formerly its own module: StructuredState, StructuredPoint, IndexedPoint, DormantOperation, CompilerBounds, IndexedPreserved.
-/

/-! ## StructuredState -/

section

/-!
The shared state invariant for structured source/compiler replay.

Main declarations: `StructuredReaderCompilerStateWasm2`. A direct consumer is `Compiler.Body.Reader.Calls.Compilation`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

structure StructuredReaderCompilerStateWasm2 (jumpTables : List U32) (emit : List valtype → instr → List Bytecode → List valtype → Prop) {A : Type}
    (initial compiler : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (data : Slice U8) (env : metadata.Env) (sourceLocals : alloc.vec.Vec Itasca.wasm_types.ValueType)
    (index : U32) (ft : Itasca.wasm_types.FuncType) (st : code.BodyState)
    (parents : List SourceScope) (current : SourceScope)
    (savedParents : List Wasm2.Frames.Saved) (savedCurrent : Wasm2.Frames.Saved) : Prop where
  compiled : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial compiler types functions returns locals parents current st.core.vals.val st.core.pos.val
  boundary : ReaderBoundaryWasm2 data env sourceLocals index ft st savedParents savedCurrent
  sources : ReaderScopeZipperWasm2 parents current savedParents savedCurrent
  reach : ReaderReachabilityWasm2 compiler.reachable parents current savedParents savedCurrent
  fronts : ReaderScopeFronts parents current (savedParents.map Wasm2.Frames.Saved.vals)
  knownFronts : ReaderKnownFronts parents current (savedParents.map Wasm2.Frames.Saved.vals)

theorem StructuredReaderCompilerStateWasm2.advance {jumpTables : List U32} {A : Type}
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env sourceLocals index ft st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerStateWasm2 (jumpTables := jumpTables) emit initial before types functions returns locals data env sourceLocals index ft
      st parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    {out instruction poly values}
    (post : Wasm2.ReaderPost (state.boundary.pending next advance inbounds) out instruction poly values)
    (declared : DeclaredReferences.Instruction (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) instruction)
    (compiled : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance instruction)
      out.vals.val out.pos.val) (mono : after.reachable = true → poly = false) :
    StructuredReaderCompilerStateWasm2 (jumpTables := jumpTables) emit initial after types functions returns locals data env sourceLocals index ft {core := out}
      parents (current.advance instruction) savedParents
      (savedCurrent.advance (.plain instruction) instruction poly values) :=
  ⟨compiled, post.boundary declared, state.sources.advance _ _ _ _, state.reach.advance _ _ _ _ _ mono,
    state.fronts.advance instruction, state.knownFronts.advance instruction⟩

end Itasca.Runtime.Compiler

end

/-! ## StructuredPoint -/

section

/-!
The structured source/compiler point extracted from a reader state.

Main declarations: `StructuredReaderCompilerPointWasm2`. A direct consumer is `Compiler.Body.Reader.Control.ElseCompilation`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

def StructuredReaderCompilerPointWasm2 (jumpTables : List U32) (emit : List valtype → instr → List Bytecode → List valtype → Prop) {A : Type}
    (initial compiler : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (data : Slice U8) (env : metadata.Env) (sourceLocals : alloc.vec.Vec Itasca.wasm_types.ValueType)
    (index : U32) (ft : Itasca.wasm_types.FuncType) (st : code.BodyState) : Prop :=
  ∃ parents current savedParents savedCurrent,
    StructuredReaderCompilerStateWasm2 (jumpTables := jumpTables) emit initial compiler types functions returns locals data env sourceLocals index ft st
      parents current savedParents savedCurrent

theorem StructuredReaderCompilerStateWasm2.point {jumpTables : List U32} {A : Type}
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env sourceLocals index ft st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerStateWasm2 (jumpTables := jumpTables) emit initial compiler types functions returns locals data env sourceLocals index ft st
      parents current savedParents savedCurrent) :
    StructuredReaderCompilerPointWasm2 (jumpTables := jumpTables) emit initial compiler types functions returns locals data env sourceLocals index ft st :=
  ⟨parents, current, savedParents, savedCurrent, state⟩
end Itasca.Runtime.Compiler

end

/-! ## IndexedPoint -/

section

/-!
The shared reader/compiler point indexed by emitted jump and control tables.

Main declarations: `IndexedTableReaderCompilerPointWasm2`. A direct consumer is `Compiler.Body.Reader.Acceptance.SourceBoundPointAcceptance`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

structure IndexedTableReaderCompilerPointWasm2
    (emit : CompilerTables → List valtype → instr → List Bytecode → List valtype → Prop) {A : Type}
    (initial compiler : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (data : Slice U8) (env : Itasca.metadata.Env) (sourceLocals : alloc.vec.Vec Itasca.wasm_types.ValueType)
    (index : U32) (ft : Itasca.wasm_types.FuncType) (st : Itasca.code.BodyState) : Prop where
  tables : CompilerTableBoundary compiler
  future : ∀ more, StructuredReaderCompilerPointWasm2
    ((CompilerTables.ofFunction compiler.function).append more).jumpTables
    (emit ((CompilerTables.ofFunction compiler.function).append more))
    initial compiler types functions returns locals data env sourceLocals index ft st

theorem IndexedTableReaderCompilerPointWasm2.append_step {A : Type}
    {emit initial before after types functions returns locals data env sourceLocals index ft st out}
    (point : @IndexedTableReaderCompilerPointWasm2 emit A initial before types functions returns locals data env sourceLocals index ft st)
    (extra : CompilerTables)
    (tables : CompilerTables.ofFunction after.function = (CompilerTables.ofFunction before.function).append extra)
    (boundary : CompilerTableBoundary after)
    (step : ∀ future, StructuredReaderCompilerPointWasm2
      ((CompilerTables.ofFunction after.function).append future).jumpTables
      (emit ((CompilerTables.ofFunction after.function).append future))
      initial before types functions returns locals data env sourceLocals index ft st →
      StructuredReaderCompilerPointWasm2
        ((CompilerTables.ofFunction after.function).append future).jumpTables
        (emit ((CompilerTables.ofFunction after.function).append future))
        initial after types functions returns locals data env sourceLocals index ft out) :
    IndexedTableReaderCompilerPointWasm2 emit initial after types functions returns locals data env sourceLocals index ft out := by
  refine ⟨boundary, ?_⟩
  intro future
  apply step future
  simpa only [tables,CompilerTables.append_assoc] using point.future (extra.append future)
end Itasca.Runtime.Compiler

end

/-! ## DormantOperation -/

section

/-!
Dormant structured prefixes for omitted source operations.

Main declarations: `Wasm2.ReaderPost.structured_dead_op`. A direct consumer is `Compiler.Body.Reader.Calls.Compilation`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem _root_.Itasca.Wasm2.ReaderPost.structured_dead_op {jumpTables : List U32} {data env sourceLocals index st}
    {p : Wasm2.Pending data env sourceLocals index st} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A} {out : code.OpIterState}
    {emit types functions returns locals parents current instruction poly values}
    (post : Wasm2.ReaderPost p out instruction poly values)
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

end Itasca.Runtime.Compiler

end

/-! ## CompilerBounds -/

section

/-!
Source-coordinate and body bounds retained by reader and compiler states.

Main declarations: `ReaderBoundaryWasm2.source_bound` and `CompilerStable.body_bound`. A direct consumer is `Compiler.Body.Reader.Control.ClosedInstructionPrefix`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem ReaderBoundaryWasm2.source_bound {data env locals index ft st parents current}
    (boundary : ReaderBoundaryWasm2 data env locals index ft st parents current) :
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
end Itasca.Runtime.Compiler

end

/-! ## IndexedPreserved -/

section

/-!
Preservation of an indexed reader/compiler point across one step.

Main declarations: `IndexedTableReaderCompilerPointWasm2.preserved_step`. A direct consumer is `Compiler.Body.Control.Closing.IndexedAdvanceOrClosed`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas.Std

theorem IndexedTableReaderCompilerPointWasm2.preserved_step {A : Type}
    {emit initial before after types functions returns locals data env sourceLocals index ft st out}
    (point : @IndexedTableReaderCompilerPointWasm2 emit A initial before types functions returns locals data env sourceLocals index ft st)
    (tables : CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function)
    (depths : after.table_depths = before.table_depths)
    (growth : before.function.code.val.length ≤ after.function.code.val.length)
    (step : ∀ future, StructuredReaderCompilerPointWasm2 ((CompilerTables.ofFunction before.function).append future).jumpTables (emit ((CompilerTables.ofFunction before.function).append future))
      initial before types functions returns locals data env sourceLocals index ft st →
      StructuredReaderCompilerPointWasm2 ((CompilerTables.ofFunction before.function).append future).jumpTables (emit ((CompilerTables.ofFunction before.function).append future))
      initial after types functions returns locals data env sourceLocals index ft out) :
    IndexedTableReaderCompilerPointWasm2 emit initial after types functions returns locals data env sourceLocals index ft out := by
  refine ⟨⟨by simpa only [depths] using point.tables.depths, ?_⟩, ?_⟩
  · have targets := congrArg CompilerTables.jumpTables tables
    change after.function.jump_tables.val = before.function.jump_tables.val at targets
    simpa only [targets] using point.tables.targets.trans growth
  · intro future
    simpa only [tables] using step future (point.future future)
end Itasca.Runtime.Compiler

end
