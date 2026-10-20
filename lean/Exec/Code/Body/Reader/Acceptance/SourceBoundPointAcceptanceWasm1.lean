import Exec.Code.Body.Reader.Source.SourceReaderCapacityWasm1
import Exec.Code.Body.Reader.Acceptance.ReachedNumericAcceptance
import Exec.Code.Body.Reader.Memory.ReachedMemoryAcceptance

namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Wasm 1 numeric acceptance constructs callback capacity
from independent source validation and the source-only body resource bound. -/
theorem IndexedTableReaderCompilerPointWasm1.numeric_available_from_source {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns localTypes data env ctx bodyBt st}
    (point : IndexedTableReaderCompilerPointWasm1 emit initial compiler types functions returns localTypes
      data env ctx bodyBt st)
    (before after final : List Observation) (out : code.BodyState)
    (room : BodyResourceRoom initial data.length (observationDemand final).operands bound)
    (budget : SourceCompilationBudget initial.budget compiler.budget bodyResourceRate st.pos.val)
    (index : U32) (nonempty : st.ctrls.val ≠ []) (next : Usize)
    (advance : next.val = st.pos.val+1) (inbounds : st.pos.val<data.length)
    (op : Abs.Numeric.Instruction) (base : (integerOpcode op).val < 192)
    (byte : data.val[st.pos.val] = UScalar.cast .U8 (integerOpcode op))
    (reference : code.step_profile recorder {core := {st with pos := next}} data env ctx index .Wasm1
      data.val[st.pos.val] before = .ok (.Ok (),out,after))
    (suffix : code.body_loop_loop recorder data env ctx index .Wasm1 before {core := st} = .ok (.Ok (),final)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st with pos := next}} data env ctx index .Wasm1 data.val[st.pos.val] compiler
      ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧ CompilationBudgetEffect compiler.budget result.2.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  let pending := state.boundary.pending next advance inbounds
  have canonical := reference
  rw [byte] at canonical
  obtain ⟨operation,hook,meaning,handler,_⟩ := integer_reader_facts ops compiler out.core op base
  obtain ⟨capacity,_,_,_⟩ := point.capacity_from_source_read before after final out bound room budget index nonempty next advance
    inbounds (UScalar.cast .U8 (integerOpcode op)) (Numeric.read operation {st with pos := next})
    (fun (_ : Unit) => .numeric hook)
    (dispatch_numeric recorder _ data env ctx before _ operation hook meaning handler) canonical byte suffix
  have raw := profile_raw_success_wasm1 recorder _ out data env ctx index (UScalar.cast .U8 (integerOpcode op)) before after canonical
  rw [byte]
  apply profile_raw_available_wasm1 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) _ out data env ctx index
    (UScalar.cast .U8 (integerOpcode op)) compiler (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0))
  exact reached_reader_numeric_available_wasm1 pending ops bound allocation recorder before after compiler out.core
    (capacity.one (by decide)) op base (by have bound := pending.val_capacity; omega) state.compiled.known state.reach.current
    (fun live => (state.compiled.live live).2.layout) byte raw

/-- Wasm 1 float acceptance constructs callback capacity
from independent source validation and the source-only body resource bound. -/
theorem IndexedTableReaderCompilerPointWasm1.float_available_from_source {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns localTypes data env ctx bodyBt st}
    (point : IndexedTableReaderCompilerPointWasm1 emit initial compiler types functions returns localTypes
      data env ctx bodyBt st)
    (before after final : List Observation) (out : code.BodyState)
    (room : BodyResourceRoom initial data.length (observationDemand final).operands bound)
    (budget : SourceCompilationBudget initial.budget compiler.budget bodyResourceRate st.pos.val)
    (index : U32) (nonempty : st.ctrls.val ≠ []) (next : Usize)
    (advance : next.val = st.pos.val+1) (inbounds : st.pos.val<data.length)
    (op : Abs.Float.Instruction) (base : (floatOpcode op).val < 256)
    (byte : data.val[st.pos.val] = UScalar.cast .U8 (floatOpcode op))
    (reference : code.step_profile recorder {core := {st with pos := next}} data env ctx index .Wasm1
      data.val[st.pos.val] before = .ok (.Ok (),out,after))
    (suffix : code.body_loop_loop recorder data env ctx index .Wasm1 before {core := st} = .ok (.Ok (),final)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st with pos := next}} data env ctx index .Wasm1 data.val[st.pos.val] compiler
      ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧ CompilationBudgetEffect compiler.budget result.2.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  let pending := state.boundary.pending next advance inbounds
  have canonical := reference
  rw [byte] at canonical
  obtain ⟨operation,hook,meaning,handler,_⟩ := float_reader_facts ops compiler out.core op base
  obtain ⟨capacity,_,_,_⟩ := point.capacity_from_source_read before after final out bound room budget index nonempty next advance
    inbounds (UScalar.cast .U8 (floatOpcode op)) (Numeric.read operation {st with pos := next})
    (fun (_ : Unit) => .numeric hook)
    (dispatch_numeric recorder _ data env ctx before _ operation hook meaning handler) canonical byte suffix
  have raw := profile_raw_success_wasm1 recorder _ out data env ctx index (UScalar.cast .U8 (floatOpcode op)) before after canonical
  rw [byte]
  apply profile_raw_available_wasm1 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) _ out data env ctx index
    (UScalar.cast .U8 (floatOpcode op)) compiler (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0))
  exact reached_reader_float_available_wasm1 pending ops bound allocation recorder before after compiler out.core
    (capacity.one (by decide)) op base (by have bound := pending.val_capacity; omega) state.compiled.known state.reach.current
    (fun live => (state.compiled.live live).2.layout) byte raw

/-- Wasm 1 memory load acceptance constructs callback capacity
from independent source validation and the source-only body resource bound. -/
theorem IndexedTableReaderCompilerPointWasm1.memory_load_available_from_source {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns localTypes data env ctx bodyBt st}
    (point : IndexedTableReaderCompilerPointWasm1 emit initial compiler types functions returns localTypes
      data env ctx bodyBt st)
    (before after final : List Observation) (out : code.BodyState)
    (room : BodyResourceRoom initial data.length (observationDemand final).operands bound)
    (budget : SourceCompilationBudget initial.budget compiler.budget bodyResourceRate st.pos.val)
    (index : U32) (nonempty : st.ctrls.val ≠ []) (next : Usize)
    (advance : next.val = st.pos.val+1) (inbounds : st.pos.val<data.length)
    (op : Abs.Memory.Load)
    (byte : data.val[st.pos.val] = UScalar.cast .U8 (memoryLoadOpcode op))
    (reference : code.step_profile recorder {core := {st with pos := next}} data env ctx index .Wasm1
      data.val[st.pos.val] before = .ok (.Ok (),out,after))
    (suffix : code.body_loop_loop recorder data env ctx index .Wasm1 before {core := st} = .ok (.Ok (),final)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st with pos := next}} data env ctx index .Wasm1 data.val[st.pos.val] compiler
      ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧ CompilationBudgetEffect compiler.budget result.2.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  let pending := state.boundary.pending next advance inbounds
  have canonical := reference
  rw [byte] at canonical
  obtain ⟨meaning,_⟩ := memory_load_reader_facts ops compiler out.core op ⟨0#u32,0#u32⟩
  obtain ⟨hook,handler,_⟩ := MemoryHook.of_meaning meaning
  obtain ⟨capacity,_,_,_⟩ := point.capacity_from_source_read before after final out bound room budget index nonempty next advance
    inbounds (UScalar.cast .U8 (memoryLoadOpcode op))
    (if (memoryLoadMeaning op).store then
      code.read_store {st with pos := next} data env (memoryLoadMeaning op).ty (memoryLoadMeaning op).naturalAlign
     else code.read_load {st with pos := next} data env (memoryLoadMeaning op).ty (memoryLoadMeaning op).naturalAlign)
    (fun arg : code.MemArg => .memory hook arg)
    (dispatch_memory recorder _ data env ctx before _ (memoryLoadMeaning op) hook meaning handler) canonical byte suffix
  have raw := profile_raw_success_wasm1 recorder _ out data env ctx index (UScalar.cast .U8 (memoryLoadOpcode op)) before after canonical
  rw [byte]
  apply profile_raw_available_wasm1 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) _ out data env ctx index
    (UScalar.cast .U8 (memoryLoadOpcode op)) compiler (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0))
  exact reached_reader_memory_load_available_wasm1 pending ops bound allocation recorder before after compiler out.core
    (capacity.one (by decide)) op (by have bound := pending.val_capacity; omega) state.compiled.known state.reach.current
    (fun live => (state.compiled.live live).2.layout) byte raw

/-- Wasm 1 memory store acceptance constructs callback capacity
from independent source validation and the source-only body resource bound. -/
theorem IndexedTableReaderCompilerPointWasm1.memory_store_available_from_source {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns localTypes data env ctx bodyBt st}
    (point : IndexedTableReaderCompilerPointWasm1 emit initial compiler types functions returns localTypes
      data env ctx bodyBt st)
    (before after final : List Observation) (out : code.BodyState)
    (room : BodyResourceRoom initial data.length (observationDemand final).operands bound)
    (budget : SourceCompilationBudget initial.budget compiler.budget bodyResourceRate st.pos.val)
    (index : U32) (nonempty : st.ctrls.val ≠ []) (next : Usize)
    (advance : next.val = st.pos.val+1) (inbounds : st.pos.val<data.length)
    (op : Abs.Memory.Store)
    (byte : data.val[st.pos.val] = UScalar.cast .U8 (memoryStoreOpcode op))
    (reference : code.step_profile recorder {core := {st with pos := next}} data env ctx index .Wasm1
      data.val[st.pos.val] before = .ok (.Ok (),out,after))
    (suffix : code.body_loop_loop recorder data env ctx index .Wasm1 before {core := st} = .ok (.Ok (),final)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st with pos := next}} data env ctx index .Wasm1 data.val[st.pos.val] compiler
      ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧ CompilationBudgetEffect compiler.budget result.2.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  let pending := state.boundary.pending next advance inbounds
  have canonical := reference
  rw [byte] at canonical
  obtain ⟨meaning,_⟩ := memory_store_reader_facts ops compiler out.core op ⟨0#u32,0#u32⟩
  obtain ⟨hook,handler,_⟩ := MemoryHook.of_meaning meaning
  obtain ⟨capacity,_,_,_⟩ := point.capacity_from_source_read before after final out bound room budget index nonempty next advance
    inbounds (UScalar.cast .U8 (memoryStoreOpcode op))
    (if (memoryStoreMeaning op).store then
      code.read_store {st with pos := next} data env (memoryStoreMeaning op).ty (memoryStoreMeaning op).naturalAlign
     else code.read_load {st with pos := next} data env (memoryStoreMeaning op).ty (memoryStoreMeaning op).naturalAlign)
    (fun arg : code.MemArg => .memory hook arg)
    (dispatch_memory recorder _ data env ctx before _ (memoryStoreMeaning op) hook meaning handler) canonical byte suffix
  have raw := profile_raw_success_wasm1 recorder _ out data env ctx index (UScalar.cast .U8 (memoryStoreOpcode op)) before after canonical
  rw [byte]
  apply profile_raw_available_wasm1 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) _ out data env ctx index
    (UScalar.cast .U8 (memoryStoreOpcode op)) compiler (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0))
  exact reached_reader_memory_store_available_wasm1 pending ops bound allocation recorder before after compiler out.core
    (capacity.one (by decide)) op (by have bound := pending.val_capacity; omega) state.compiled.known state.reach.current
    (fun live => (state.compiled.live live).2.layout) byte raw

end Exec.Code
