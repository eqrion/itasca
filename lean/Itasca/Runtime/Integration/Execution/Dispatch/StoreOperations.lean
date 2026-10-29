import Itasca.Runtime.Integration.Execution.Dispatch.StoreRead
import Itasca.Runtime.Integration.Execution.Dispatch.MemoryBulk
import Itasca.Runtime.Integration.Execution.Dispatch.TableBulk
import Itasca.Runtime.Integration.Execution.Dispatch.SegmentDrop
import Itasca.Runtime.Integration.Execution.Dispatch.TableSet
import Itasca.Runtime.Integration.Api.SupportedMemoryGrowExecution
import Itasca.Runtime.Integration.Api.SupportedTableGrowExecution
namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std Itasca.Runtime.Interp
theorem stateful_execution_supported
 {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P) (index : Usize)
    (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    [Machine.StatefulProjection (emission compiled) compiled.indirect.val]
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr) (op : SourceMachine.Stateful.Instruction)
    (last : index.val+1=exec.frames.length)
    (frameFound : exec.frames.val[index.val]?=some raw)
    (found : store.instances.val[raw.instance.val]?=some inst)
    (codeFound : inst.module.functions.val[raw.function.val]?=some compiled)
    (moduleEq : f.module=Store.decodeInstance store inst) (slots : FrameSlots exec raw f)
    (point : Machine.FramePoint (Store.decodeStore view code store) raw {f with code:=op.source::after} compiled C targets next output)
    (expected : List valtype)
    (machine : Machine.Execution view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code:=op.source::after}::rest,[]⟩ expected raw.pc.val false)
    (program : FrameProgram store raw compiled (f.locals.map Compiler.valueType) f.resultTypes C.FUNCS)
    (shaped : Store.Shape view store) (sourceSyntax : Store.StoreSyntax code store) (bounds : Store.SegmentBounds store)
    (owned : SourceMachine.Ownership.StatefulOwned (Store.ownershipBounds store) ⟨Store.decodeStore view code store,ambient,{f with code:=op.source::after}::rest,[]⟩) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      SupportedStepOutcome allocator hooks view code exec store platform expected compiled.code.length raw.pc.val false
        ⟨Store.decodeStore view code store,ambient,{f with code:=op.source::after}::rest,[]⟩ out ⦄ := by
  cases op with
  | refNull type =>
    exact stateful_read_execution_supported memory hooks floats allocator view laws code exec store platform index raw inst compiled C targets next output ambient f rest after (.refNull type) rfl last frameFound found codeFound moduleEq slots point expected machine program shaped sourceSyntax bounds
  | refFunc function =>
    exact stateful_read_execution_supported memory hooks floats allocator view laws code exec store platform index raw inst compiled C targets next output ambient f rest after (.refFunc function) rfl last frameFound found codeFound moduleEq slots point expected machine program shaped sourceSyntax bounds
  | refIsNull  =>
    exact stateful_read_execution_supported memory hooks floats allocator view laws code exec store platform index raw inst compiled C targets next output ambient f rest after (.refIsNull) rfl last frameFound found codeFound moduleEq slots point expected machine program shaped sourceSyntax bounds
  | tableGet table =>
    exact stateful_read_execution_supported memory hooks floats allocator view laws code exec store platform index raw inst compiled C targets next output ambient f rest after (.tableGet table) rfl last frameFound found codeFound moduleEq slots point expected machine program shaped sourceSyntax bounds
  | tableSize table =>
    exact stateful_read_execution_supported memory hooks floats allocator view laws code exec store platform index raw inst compiled C targets next output ambient f rest after (.tableSize table) rfl last frameFound found codeFound moduleEq slots point expected machine program shaped sourceSyntax bounds
  | memorySize  =>
    exact stateful_read_execution_supported memory hooks floats allocator view laws code exec store platform index raw inst compiled C targets next output ambient f rest after (.memorySize) rfl last frameFound found codeFound moduleEq slots point expected machine program shaped sourceSyntax bounds
  | tableSet table =>
    exact stateful_table_set_execution_supported memory hooks floats allocator view code exec store platform index raw inst compiled C targets next output ambient f rest after table last frameFound found codeFound moduleEq slots point expected machine program shaped sourceSyntax bounds owned
  | tableGrow table =>
    exact stateful_table_grow_execution_supported memory hooks floats allocator allocation view code exec store platform index raw inst compiled C targets next output ambient f rest after table last frameFound found codeFound moduleEq slots point expected machine program shaped sourceSyntax bounds owned
  | tableFill table =>
    exact stateful_table_fill_execution_supported memory hooks floats allocator view code exec store platform index raw inst compiled C targets next output ambient f rest after table last frameFound found codeFound moduleEq slots point expected machine program shaped sourceSyntax bounds owned
  | tableCopy destination source =>
    exact stateful_table_copy_execution_supported memory hooks floats allocator view code exec store platform index raw inst compiled C targets next output ambient f rest after destination source last frameFound found codeFound moduleEq slots point expected machine program shaped sourceSyntax bounds
  | tableInit table element =>
    exact stateful_table_init_execution_supported memory hooks floats allocator view code exec store platform index raw inst compiled C targets next output ambient f rest after table element last frameFound found codeFound moduleEq slots point expected machine program shaped sourceSyntax bounds
  | memoryGrow  =>
    exact stateful_memory_grow_execution_supported memory hooks floats allocator view laws code exec store platform index raw inst compiled C targets next output ambient f rest after  last frameFound found codeFound moduleEq slots point expected machine program shaped sourceSyntax bounds
  | memoryFill  =>
    exact stateful_memory_fill_execution_supported memory hooks floats allocator view laws code exec store platform index raw inst compiled C targets next output ambient f rest after  last frameFound found codeFound moduleEq slots point expected machine program shaped sourceSyntax bounds
  | memoryCopy  =>
    exact stateful_memory_copy_execution_supported memory hooks floats allocator view laws code exec store platform index raw inst compiled C targets next output ambient f rest after  last frameFound found codeFound moduleEq slots point expected machine program shaped sourceSyntax bounds
  | memoryInit data =>
    exact stateful_memory_init_execution_supported memory hooks floats allocator view laws code exec store platform index raw inst compiled C targets next output ambient f rest after data last frameFound found codeFound moduleEq slots point expected machine program shaped sourceSyntax bounds
  | elemDrop element =>
    exact stateful_drop_execution_supported memory hooks floats allocator view code exec store platform index raw inst compiled C targets next output ambient f rest after (.elemDrop element) rfl last frameFound found codeFound moduleEq slots point expected machine program shaped sourceSyntax bounds
  | dataDrop data =>
    exact stateful_drop_execution_supported memory hooks floats allocator view code exec store platform index raw inst compiled C targets next output ambient f rest after (.dataDrop data) rfl last frameFound found codeFound moduleEq slots point expected machine program shaped sourceSyntax bounds

end Itasca.Runtime.Integration
