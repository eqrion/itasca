import Exec.Interp.StructuredMachine.FloatHeads
import Exec.Code.Local.Lowering.Float.FloatCoreProjection
import Exec.Interp.Memory.MemoryCoreOperandBounds
import Exec.Interp.StructuredMachine.MemoryContinue
namespace Exec.Interp.StructuredMachine.Memory
variable {emission : FunctionEmission} [∀ compiled, FloatHeads (emission compiled)]
open Exec.Interp.MemoryDescriptor
open Aeneas Aeneas.Std SpecExt

theorem coreFramePoint_load_prepare {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.Instance) (raw : runtime.interp.Frame)
    (f : Abs.AFrame) (compiled : runtime.bytecode.CompiledFunction) (C : context) (targets : List Code.LabelTarget)
    (next : Nat) (output : List valtype) (after : List instr) (op : Abs.Memory.Load) (argument : memarg)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (typed : Abs.FrameTyped (Store.decodeStore view code store) {f with code := op.source argument :: after} [])
    (point : FramePoint emission (Store.decodeStore view code store) raw {f with code := op.source argument :: after} compiled C targets next output) :
    (∃ target : U32, raw.pc.val < target.val ∧ compiled.code.val[raw.pc.val]? = some (.Jump target) ∧
      FramePoint emission (Store.decodeStore view code store) {raw with pc := target} {f with code := op.source argument :: after} compiled C targets next output) ∨
    (∃ front bits memoryAddress object address offset,
      f.vals = front ++ [Abs.integerVal .I32 bits] ∧ bits < 2^32 ∧
      inst.memories.val[0]? = some memoryAddress ∧ store.memories.val[memoryAddress.index.val]? = some object ∧
      (∀ label ∈ f.labels, label.height ≤ front.length) ∧
      address.val = Code.slots (f.locals.map Code.valueType) + Code.slots (front.map Code.valueType) ∧
      proj_uN_0 argument.OFFSET = offset.val ∧
      compiled.code.val[raw.pc.val]? = some (Code.memoryLoadInstruction op address address offset) ∧
      Code.StructuredCodeWithTables.Point (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS compiled.code.val compiled.jump_tables.val targets
        (front.map Code.valueType ++ [valtype_numtype op.type]) after (raw.pc.val+1) next output) := by
  rcases corePoint_load_head op argument after point.code with ⟨target,forward,fetch,tail⟩ | ⟨types,address,offset,input,position,offsetEq,fetch,tail⟩
  · exact Or.inl ⟨target,forward,fetch,⟨point.bindings,point.locals,point.labels,tail⟩⟩
  · obtain ⟨front,bits,memoryAddress,object,values,bound,mapped,issued,wf,heights⟩ :=
      load_typed_operands_full view code store inst f after op argument moduleEq typed
    have typesEq : front.map Code.valueType = types := by
      have eq := input
      simp only [values,List.map_append,List.map_cons,List.map_nil,Code.valueType,Abs.integerVal,numtype_Inn] at eq
      exact List.append_cancel_right eq
    refine Or.inr ⟨front,bits,memoryAddress,object,address,offset,values,bound,mapped,issued,heights,?_,?_,fetch,?_⟩
    · simpa only [← point.locals,typesEq] using position
    · simp only [offsetEq,proj_uN_0]
    · simpa only [typesEq] using tail

theorem coreFramePoint_store_prepare {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.Instance) (raw : runtime.interp.Frame)
    (f : Abs.AFrame) (compiled : runtime.bytecode.CompiledFunction) (C : context) (targets : List Code.LabelTarget)
    (next : Nat) (output : List valtype) (after : List instr) (op : Abs.Memory.Store) (argument : memarg)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (typed : Abs.FrameTyped (Store.decodeStore view code store) {f with code := op.source argument :: after} [])
    (point : FramePoint emission (Store.decodeStore view code store) raw {f with code := op.source argument :: after} compiled C targets next output) :
    (∃ target : U32, raw.pc.val < target.val ∧ compiled.code.val[raw.pc.val]? = some (.Jump target) ∧
      FramePoint emission (Store.decodeStore view code store) {raw with pc := target} {f with code := op.source argument :: after} compiled C targets next output) ∨
    (∃ front bits number memoryAddress object address value offset,
      f.vals = front ++ [Abs.integerVal .I32 bits,.CONST op.type number] ∧ bits < 2^32 ∧ wf_num_ op.type number ∧
      inst.memories.val[0]? = some memoryAddress ∧ store.memories.val[memoryAddress.index.val]? = some object ∧
      (∀ label ∈ f.labels, label.height ≤ front.length) ∧
      address.val = Code.slots (f.locals.map Code.valueType) + Code.slots (front.map Code.valueType) ∧
      value.val = address.val+1 ∧ proj_uN_0 argument.OFFSET = offset.val ∧
      compiled.code.val[raw.pc.val]? = some (Code.memoryStoreInstruction op address value offset) ∧
      Code.StructuredCodeWithTables.Point (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS compiled.code.val compiled.jump_tables.val targets
        (front.map Code.valueType) after (raw.pc.val+1) next output) := by
  rcases corePoint_store_head op argument after point.code with ⟨target,forward,fetch,tail⟩ | ⟨types,address,value,offset,input,position,valuePosition,offsetEq,fetch,tail⟩
  · exact Or.inl ⟨target,forward,fetch,⟨point.bindings,point.locals,point.labels,tail⟩⟩
  · obtain ⟨front,bits,number,memoryAddress,object,values,bound,numberWf,mapped,issued,wf,heights⟩ :=
      store_typed_operands_full view code store inst f after op argument moduleEq typed
    have typesEq : front.map Code.valueType = types := by
      have eq := input
      simp only [values,List.map_append,List.map_cons,List.map_nil,Code.valueType,Abs.integerVal,numtype_Inn] at eq
      exact List.append_cancel_right eq
    refine Or.inr ⟨front,bits,number,memoryAddress,object,address,value,offset,values,bound,numberWf,mapped,issued,heights,?_,valuePosition,?_,fetch,?_⟩
    · simpa only [← point.locals,typesEq] using position
    · simp only [offsetEq,proj_uN_0]
    · simpa only [typesEq] using tail
end Exec.Interp.StructuredMachine.Memory
