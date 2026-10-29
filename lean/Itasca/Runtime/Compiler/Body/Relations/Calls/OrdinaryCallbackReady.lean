import Itasca.Runtime.Compiler.Local.Relations.Local.LocalDeclarations
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CallbackBounds
import Itasca.Runtime.Compiler.Body.Reader.Replay.IndexedPoint
import Itasca.Runtime.Compiler.Body.Reader.Replay.CompilerBounds
import Itasca.Runtime.Compiler.Body.Reader.Calls.CallLowering
import Itasca.Runtime.Compiler.Local.Relations.Table.SignatureTable
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

structure OrdinaryNamespaces {A} (compiler : runtime.compiler.FunctionCompiler A)
    (env : module.Env) (ctx : code.Context) : Prop where
  locals : compiler.function.locals.val.length = ctx.locals.val.length
  offsets : compiler.local_offsets.val.length = ctx.locals.val.length
  functions : compiler.func_param_slots.val.length = env.func_types.val.length
  signatures : compiler.signatures.val.length = env.types.val.length

theorem OrdinaryNamespaces.of_initial {A} {compiler : runtime.compiler.FunctionCompiler A}
    {env : module.Env} {ctx : code.Context}
    (layout : LocalLayout compiler) (locals : compiler.function.locals = ctx.locals)
    (functions : FunctionParameterSlots compiler env)
    (signatures : SignatureSequence compiler.signatures.val env.types.val) :
    OrdinaryNamespaces compiler env ctx := by
  have offsets := congrArg List.length layout.offsets
  have counts := congrArg List.length functions
  refine ⟨by rw [locals],?_,?_,List.Forall₂.length_eq signatures⟩
  · simpa only [compilerLocals,List.length_map,List.length_range,locals] using offsets
  · simpa only [List.length_map] using counts

theorem OrdinaryNamespaces.stable {A} {before after : runtime.compiler.FunctionCompiler A}
    {env : module.Env} {ctx : code.Context}
    (names : OrdinaryNamespaces before env ctx) (stable : CompilerStable before after) :
    OrdinaryNamespaces after env ctx := by
  obtain ⟨signatures,functions,_,_,locals,_,_,_,_,offsets⟩ := stable.fields
  exact ⟨by simpa [locals] using names.locals,by simpa [offsets] using names.offsets,
    by simpa [functions] using names.functions,by simpa [signatures] using names.signatures⟩

/-- All bounds used by ordinary callbacks are numerical invariants of the
reached compiler; raw stack observation includes polymorphic bottom operands. -/
structure OrdinaryCallbackReady {A} (compiler : runtime.compiler.FunctionCompiler A)
    (env : module.Env) (ctx : code.Context) (values : List code.StackType) : Prop where
  namespaces : OrdinaryNamespaces compiler env ctx
  observed : ObservedStack compiler values
  codeFits : compiler.function.code.val.length < Usize.max
  sourceFits : compiler.function.source_offsets.val.length < Usize.max
  coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max
  pairFits : compiler.function.indirect.val.length < Usize.max
  simdFits : compiler.function.simd.val.length < Usize.max
  poolFits : compiler.function.v128_pool.val.length < Usize.max

theorem ordinary_callback_ready_of_prefix {A} {initial compiler : runtime.compiler.FunctionCompiler A}
    {jumpTables emit types functions returns locals parents current values position}
    (point : StructuredCompilerPrefix jumpTables emit initial compiler types functions returns locals parents current values position)
    {env : module.Env} {ctx : code.Context} (length : Nat)
    (namespaces : OrdinaryNamespaces initial env ctx)
    (observed : ObservedStack compiler values)
    (bounded : length ≤ limits.MAX_MODULE_BYTES.val) (positionBound : position ≤ length)
    (bodyBound : initial.function.body_start.val + length ≤ Usize.max)
    (pairs : compiler.function.indirect.val.length ≤ compiler.function.code.val.length)
    (simd : compiler.function.simd.val.length ≤ compiler.function.code.val.length)
    (pool : compiler.function.v128_pool.val.length ≤ compiler.function.code.val.length) :
    OrdinaryCallbackReady compiler env ctx values := by
  have capacities := point.capacities (positionBound.trans bounded)
  have body := point.metadata.body_bound bodyBound
  have cursor := point.cursor
  exact ⟨namespaces.stable point.metadata,observed,capacities.1,capacities.2.1,
    by omega,by omega,by omega,by omega⟩

theorem IndexedTableReaderCompilerPointWasm2.ordinary_ready {A} {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env sourceLocals index ft st}
    (point : IndexedTableReaderCompilerPointWasm2 emit initial compiler types functions returns locals data env sourceLocals index ft st)
    (namespaces : OrdinaryNamespaces initial env ⟨sourceLocals,ft.results⟩)
    (observed : ObservedStack compiler st.core.vals.val)
    (bodyBound : initial.function.body_start.val + data.length ≤ Usize.max)
    (pairs : compiler.function.indirect.val.length ≤ compiler.function.code.val.length)
    (simd : compiler.function.simd.val.length ≤ compiler.function.code.val.length)
    (pool : compiler.function.v128_pool.val.length ≤ compiler.function.code.val.length) :
    OrdinaryCallbackReady compiler env ⟨sourceLocals,ft.results⟩ st.core.vals.val := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  exact ordinary_callback_ready_of_prefix state.compiled data.length namespaces observed
    state.boundary.source_bound state.boundary.bounds.pos bodyBound pairs simd pool
end Itasca.Runtime.Compiler
