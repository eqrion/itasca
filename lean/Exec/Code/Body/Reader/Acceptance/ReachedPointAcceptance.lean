import Exec.Code.Body.Reader.Acceptance.ReachedNumericAcceptance
import Exec.Code.Body.Reader.Memory.ReachedMemoryAcceptance
import Exec.Code.Body.Reader.Table.IndexedTableReaderCompilerPoint

namespace Exec.Code
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 4096

/-- A reached compiler/source prefix supplies all typed-layout premises for
numeric acceptance; the independent reference supplies the next source result. -/
theorem IndexedTableReaderCompilerPointWasm2.numeric_available {A V : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns localTypes data env sourceLocals index ft st}
    (point : IndexedTableReaderCompilerPointWasm2 emit initial compiler types functions returns localTypes
      data env sourceLocals index ft st)
    (source : code.OpVisitor V) (before after : V) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    (next : Usize) (advance : next.val = st.core.pos.val+1) (inbounds : st.core.pos.val<data.length)
    (demand : CallbackDemand compiler out.core bound) (op : Abs.Numeric.Instruction) (base : (integerOpcode op).val < 192)
    (byte : data.val[st.core.pos.val] = UScalar.cast .U8 (integerOpcode op))
    (reference : code.step_profile source {core := {st.core with pos := next}} data env ctx index .Wasm2
      data.val[st.core.pos.val] before = .ok (.Ok (),out,after)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 data.val[st.core.pos.val] compiler ⦃ result =>
      result.1 = .Ok () ∧ result.2.1 = out ∧ CompilationBudgetEffect compiler.budget result.2.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  let pending := state.boundary.pending next advance inbounds
  rw [byte] at reference ⊢
  exact reached_profile_numeric_available_wasm2 pending ops bound available source before after compiler out ctx
    contextLocals demand op base state.compiled.known state.reach.current
    (fun live => (state.compiled.live live).2.layout) byte reference

/-- A reached compiler/source prefix supplies all typed-layout premises for
float acceptance; the independent reference supplies the next source result. -/
theorem IndexedTableReaderCompilerPointWasm2.float_available {A V : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns localTypes data env sourceLocals index ft st}
    (point : IndexedTableReaderCompilerPointWasm2 emit initial compiler types functions returns localTypes
      data env sourceLocals index ft st)
    (source : code.OpVisitor V) (before after : V) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    (next : Usize) (advance : next.val = st.core.pos.val+1) (inbounds : st.core.pos.val<data.length)
    (demand : CallbackDemand compiler out.core bound) (op : Abs.Float.Instruction) (base : (floatOpcode op).val < 256)
    (byte : data.val[st.core.pos.val] = UScalar.cast .U8 (floatOpcode op))
    (reference : code.step_profile source {core := {st.core with pos := next}} data env ctx index .Wasm2
      data.val[st.core.pos.val] before = .ok (.Ok (),out,after)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 data.val[st.core.pos.val] compiler ⦃ result =>
      result.1 = .Ok () ∧ result.2.1 = out ∧ CompilationBudgetEffect compiler.budget result.2.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  let pending := state.boundary.pending next advance inbounds
  rw [byte] at reference ⊢
  exact reached_profile_float_available_wasm2 pending ops bound available source before after compiler out ctx
    contextLocals demand op base state.compiled.known state.reach.current
    (fun live => (state.compiled.live live).2.layout) byte reference

/-- A reached compiler/source prefix supplies all typed-layout premises for
memory load acceptance; the independent reference supplies the next source result. -/
theorem IndexedTableReaderCompilerPointWasm2.memory_load_available {A V : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns localTypes data env sourceLocals index ft st}
    (point : IndexedTableReaderCompilerPointWasm2 emit initial compiler types functions returns localTypes
      data env sourceLocals index ft st)
    (source : code.OpVisitor V) (before after : V) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    (next : Usize) (advance : next.val = st.core.pos.val+1) (inbounds : st.core.pos.val<data.length)
    (demand : CallbackDemand compiler out.core bound) (op : Abs.Memory.Load)
    (byte : data.val[st.core.pos.val] = UScalar.cast .U8 (memoryLoadOpcode op))
    (reference : code.step_profile source {core := {st.core with pos := next}} data env ctx index .Wasm2
      data.val[st.core.pos.val] before = .ok (.Ok (),out,after)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 data.val[st.core.pos.val] compiler ⦃ result =>
      result.1 = .Ok () ∧ result.2.1 = out ∧ CompilationBudgetEffect compiler.budget result.2.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  let pending := state.boundary.pending next advance inbounds
  rw [byte] at reference ⊢
  exact reached_profile_memory_load_available_wasm2 pending ops bound available source before after compiler out ctx
    contextLocals demand op state.compiled.known state.reach.current
    (fun live => (state.compiled.live live).2.layout) byte reference

/-- A reached compiler/source prefix supplies all typed-layout premises for
memory store acceptance; the independent reference supplies the next source result. -/
theorem IndexedTableReaderCompilerPointWasm2.memory_store_available {A V : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns localTypes data env sourceLocals index ft st}
    (point : IndexedTableReaderCompilerPointWasm2 emit initial compiler types functions returns localTypes
      data env sourceLocals index ft st)
    (source : code.OpVisitor V) (before after : V) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    (next : Usize) (advance : next.val = st.core.pos.val+1) (inbounds : st.core.pos.val<data.length)
    (demand : CallbackDemand compiler out.core bound) (op : Abs.Memory.Store)
    (byte : data.val[st.core.pos.val] = UScalar.cast .U8 (memoryStoreOpcode op))
    (reference : code.step_profile source {core := {st.core with pos := next}} data env ctx index .Wasm2
      data.val[st.core.pos.val] before = .ok (.Ok (),out,after)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 data.val[st.core.pos.val] compiler ⦃ result =>
      result.1 = .Ok () ∧ result.2.1 = out ∧ CompilationBudgetEffect compiler.budget result.2.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  let pending := state.boundary.pending next advance inbounds
  rw [byte] at reference ⊢
  exact reached_profile_memory_store_available_wasm2 pending ops bound available source before after compiler out ctx
    contextLocals demand op state.compiled.known state.reach.current
    (fun live => (state.compiled.live live).2.layout) byte reference

end Exec.Code
