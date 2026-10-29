import Itasca.Runtime.Compiler.Body.Reader.Acceptance.ReachedNumericAcceptance
import Itasca.Runtime.Compiler.Body.Reader.Memory.Acceptance
import Itasca.Runtime.Compiler.Body.Reader.Replay.IndexedPoint
import Itasca.Runtime.Compiler.Body.Reader.Acceptance.ReachedReferenceDemand
import Itasca.Runtime.Compiler.Local.Capacity.BodyReplay

/-!
Integer, float and scalar-memory replay from source bounds at an indexed point. The final statements convert reached-point availability into the independent source demand premise.
-/

/-! ## Reached Point Acceptance -/

section

namespace Itasca.Runtime.Compiler
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
    (demand : CallbackDemand compiler out.core bound) (op : SourceMachine.Numeric.Instruction) (base : (integerOpcode op).val < 192)
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
    (demand : CallbackDemand compiler out.core bound) (op : SourceMachine.Float.Instruction) (base : (floatOpcode op).val < 256)
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
    (demand : CallbackDemand compiler out.core bound) (op : SourceMachine.Memory.Load)
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
    (demand : CallbackDemand compiler out.core bound) (op : SourceMachine.Memory.Store)
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

end Itasca.Runtime.Compiler

end

/-! ## Source Bound Point Acceptance -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace
set_option maxRecDepth 4096

/-- Source byte bounds and the independently retained reference suffix
construct all numeric callback demands. No accepted target step,
completed code certificate, or caller-supplied callback-demand record is used. -/
theorem IndexedTableReaderCompilerPointWasm2.numeric_available_from_source {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns localTypes data env sourceLocals index ft st}
    (point : IndexedTableReaderCompilerPointWasm2 emit initial compiler types functions returns localTypes
      data env sourceLocals index ft st)
    (before after final : List Observation) (out : code.BodyState)
    (room : BodyResourceRoom initial data.length (observationDemand final).operands bound)
    (budget : SourceCompilationBudget initial.budget compiler.budget bodyResourceRate st.core.pos.val)
    (nonempty : st.core.ctrls.val ≠ []) (next : Usize)
    (advance : next.val = st.core.pos.val+1) (inbounds : st.core.pos.val<data.length)
    (op : SourceMachine.Numeric.Instruction) (base : (integerOpcode op).val < 192)
    (byte : data.val[st.core.pos.val] = UScalar.cast .U8 (integerOpcode op))
    (reference : code.step_profile recorder {core := {st.core with pos := next}} data env
      ⟨sourceLocals,ft.results⟩ index .Wasm2 data.val[st.core.pos.val] before = .ok (.Ok (),out,after))
    (suffix : code.body_loop_loop recorder data env ⟨sourceLocals,ft.results⟩ index .Wasm2 before st =
      .ok (.Ok (),final)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ⟨sourceLocals,ft.results⟩ index .Wasm2
      data.val[st.core.pos.val] compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  have tail := code.body_loop_loop.accepted_tail recorder data env ⟨sourceLocals,ft.results⟩ index .Wasm2 st out
    before after final nonempty inbounds next advance reference suffix
  have canonical := reference
  rw [byte] at canonical
  obtain ⟨operation,hook,meaning,handler,_,_,_,_,ordinary,plain,sign,misc⟩ :=
    integer_reader_facts ops compiler out.core op base
  obtain ⟨_,raw⟩ := profile_base_success_wasm2 recorder _ out data env ⟨sourceLocals,ft.results⟩ ⟨sourceLocals,ft.results⟩
    index _ before after ordinary plain sign misc rfl canonical
  rw [dispatch_numeric recorder _ data env ⟨sourceLocals,ft.results⟩ before _ operation hook meaning handler] at raw
  have demand := reference_reader_demand final room budget state.compiled.metadata state.compiled.codeBudget
    state.compiled.sources state.compiled.cursor inbounds _ (fun (_ : Unit) => .numeric hook) before after out raw
    data env ⟨sourceLocals,ft.results⟩ index .Wasm2 tail
  exact point.numeric_available ops bound available recorder before after out ⟨sourceLocals,ft.results⟩ rfl
    next advance inbounds demand op base byte reference

/-- Source byte bounds and the independently retained reference suffix
construct all float callback demands. No accepted target step,
completed code certificate, or caller-supplied callback-demand record is used. -/
theorem IndexedTableReaderCompilerPointWasm2.float_available_from_source {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns localTypes data env sourceLocals index ft st}
    (point : IndexedTableReaderCompilerPointWasm2 emit initial compiler types functions returns localTypes
      data env sourceLocals index ft st)
    (before after final : List Observation) (out : code.BodyState)
    (room : BodyResourceRoom initial data.length (observationDemand final).operands bound)
    (budget : SourceCompilationBudget initial.budget compiler.budget bodyResourceRate st.core.pos.val)
    (nonempty : st.core.ctrls.val ≠ []) (next : Usize)
    (advance : next.val = st.core.pos.val+1) (inbounds : st.core.pos.val<data.length)
    (op : SourceMachine.Float.Instruction) (base : (floatOpcode op).val < 256)
    (byte : data.val[st.core.pos.val] = UScalar.cast .U8 (floatOpcode op))
    (reference : code.step_profile recorder {core := {st.core with pos := next}} data env
      ⟨sourceLocals,ft.results⟩ index .Wasm2 data.val[st.core.pos.val] before = .ok (.Ok (),out,after))
    (suffix : code.body_loop_loop recorder data env ⟨sourceLocals,ft.results⟩ index .Wasm2 before st =
      .ok (.Ok (),final)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ⟨sourceLocals,ft.results⟩ index .Wasm2
      data.val[st.core.pos.val] compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  have tail := code.body_loop_loop.accepted_tail recorder data env ⟨sourceLocals,ft.results⟩ index .Wasm2 st out
    before after final nonempty inbounds next advance reference suffix
  have canonical := reference
  rw [byte] at canonical
  obtain ⟨operation,hook,meaning,handler,_,_,_,_,ordinary,plain,sign,misc⟩ :=
    float_reader_facts ops compiler out.core op base
  obtain ⟨_,raw⟩ := profile_base_success_wasm2 recorder _ out data env ⟨sourceLocals,ft.results⟩ ⟨sourceLocals,ft.results⟩
    index _ before after ordinary plain sign misc rfl canonical
  rw [dispatch_numeric recorder _ data env ⟨sourceLocals,ft.results⟩ before _ operation hook meaning handler] at raw
  have demand := reference_reader_demand final room budget state.compiled.metadata state.compiled.codeBudget
    state.compiled.sources state.compiled.cursor inbounds _ (fun (_ : Unit) => .numeric hook) before after out raw
    data env ⟨sourceLocals,ft.results⟩ index .Wasm2 tail
  exact point.float_available ops bound available recorder before after out ⟨sourceLocals,ft.results⟩ rfl
    next advance inbounds demand op base byte reference

/-- Source byte bounds and the independently retained reference suffix
construct all memory load callback demands. No accepted target step,
completed code certificate, or caller-supplied callback-demand record is used. -/
theorem IndexedTableReaderCompilerPointWasm2.memory_load_available_from_source {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns localTypes data env sourceLocals index ft st}
    (point : IndexedTableReaderCompilerPointWasm2 emit initial compiler types functions returns localTypes
      data env sourceLocals index ft st)
    (before after final : List Observation) (out : code.BodyState)
    (room : BodyResourceRoom initial data.length (observationDemand final).operands bound)
    (budget : SourceCompilationBudget initial.budget compiler.budget bodyResourceRate st.core.pos.val)
    (nonempty : st.core.ctrls.val ≠ []) (next : Usize)
    (advance : next.val = st.core.pos.val+1) (inbounds : st.core.pos.val<data.length)
    (op : SourceMachine.Memory.Load)
    (byte : data.val[st.core.pos.val] = UScalar.cast .U8 (memoryLoadOpcode op))
    (reference : code.step_profile recorder {core := {st.core with pos := next}} data env
      ⟨sourceLocals,ft.results⟩ index .Wasm2 data.val[st.core.pos.val] before = .ok (.Ok (),out,after))
    (suffix : code.body_loop_loop recorder data env ⟨sourceLocals,ft.results⟩ index .Wasm2 before st =
      .ok (.Ok (),final)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ⟨sourceLocals,ft.results⟩ index .Wasm2
      data.val[st.core.pos.val] compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  have tail := code.body_loop_loop.accepted_tail recorder data env ⟨sourceLocals,ft.results⟩ index .Wasm2 st out
    before after final nonempty inbounds next advance reference suffix
  have canonical := reference
  rw [byte] at canonical
  obtain ⟨meaning,_,_,_,_,ordinary,plain,sign,misc⟩ := memory_load_reader_facts ops compiler out.core op ⟨0#u32,0#u32⟩
  obtain ⟨hook,handler,_⟩ := MemoryHook.of_meaning meaning
  obtain ⟨_,raw⟩ := profile_base_success_wasm2 recorder _ out data env ⟨sourceLocals,ft.results⟩ ⟨sourceLocals,ft.results⟩
    index _ before after ordinary plain sign misc rfl canonical
  rw [dispatch_memory recorder _ data env ⟨sourceLocals,ft.results⟩ before _ (memoryLoadMeaning op) hook meaning handler] at raw
  have demand := reference_reader_demand final room budget state.compiled.metadata state.compiled.codeBudget
    state.compiled.sources state.compiled.cursor inbounds _ (fun arg : code.MemArg => .memory hook arg) before after out raw
    data env ⟨sourceLocals,ft.results⟩ index .Wasm2 tail
  exact point.memory_load_available ops bound available recorder before after out ⟨sourceLocals,ft.results⟩ rfl
    next advance inbounds demand op byte reference

/-- Source byte bounds and the independently retained reference suffix
construct all memory store callback demands. No accepted target step,
completed code certificate, or caller-supplied callback-demand record is used. -/
theorem IndexedTableReaderCompilerPointWasm2.memory_store_available_from_source {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns localTypes data env sourceLocals index ft st}
    (point : IndexedTableReaderCompilerPointWasm2 emit initial compiler types functions returns localTypes
      data env sourceLocals index ft st)
    (before after final : List Observation) (out : code.BodyState)
    (room : BodyResourceRoom initial data.length (observationDemand final).operands bound)
    (budget : SourceCompilationBudget initial.budget compiler.budget bodyResourceRate st.core.pos.val)
    (nonempty : st.core.ctrls.val ≠ []) (next : Usize)
    (advance : next.val = st.core.pos.val+1) (inbounds : st.core.pos.val<data.length)
    (op : SourceMachine.Memory.Store)
    (byte : data.val[st.core.pos.val] = UScalar.cast .U8 (memoryStoreOpcode op))
    (reference : code.step_profile recorder {core := {st.core with pos := next}} data env
      ⟨sourceLocals,ft.results⟩ index .Wasm2 data.val[st.core.pos.val] before = .ok (.Ok (),out,after))
    (suffix : code.body_loop_loop recorder data env ⟨sourceLocals,ft.results⟩ index .Wasm2 before st =
      .ok (.Ok (),final)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ⟨sourceLocals,ft.results⟩ index .Wasm2
      data.val[st.core.pos.val] compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  have tail := code.body_loop_loop.accepted_tail recorder data env ⟨sourceLocals,ft.results⟩ index .Wasm2 st out
    before after final nonempty inbounds next advance reference suffix
  have canonical := reference
  rw [byte] at canonical
  obtain ⟨meaning,_,_,_,_,ordinary,plain,sign,misc⟩ := memory_store_reader_facts ops compiler out.core op ⟨0#u32,0#u32⟩
  obtain ⟨hook,handler,_⟩ := MemoryHook.of_meaning meaning
  obtain ⟨_,raw⟩ := profile_base_success_wasm2 recorder _ out data env ⟨sourceLocals,ft.results⟩ ⟨sourceLocals,ft.results⟩
    index _ before after ordinary plain sign misc rfl canonical
  rw [dispatch_memory recorder _ data env ⟨sourceLocals,ft.results⟩ before _ (memoryStoreMeaning op) hook meaning handler] at raw
  have demand := reference_reader_demand final room budget state.compiled.metadata state.compiled.codeBudget
    state.compiled.sources state.compiled.cursor inbounds _ (fun arg : code.MemArg => .memory hook arg) before after out raw
    data env ⟨sourceLocals,ft.results⟩ index .Wasm2 tail
  exact point.memory_store_available ops bound available recorder before after out ⟨sourceLocals,ft.results⟩ rfl
    next advance inbounds demand op byte reference

end Itasca.Runtime.Compiler

end
