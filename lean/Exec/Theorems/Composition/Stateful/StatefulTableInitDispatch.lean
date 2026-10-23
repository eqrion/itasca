import Exec.Theorems.Composition.Stateful.StatefulTableInit
import Exec.Interp.State.StatefulIntegerOperands
import Exec.Interp.State.StatefulLookup
import Exec.Store.Initialization.SegmentStep
import Exec.Interp.State.StatefulSegmentLookup
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Store Exec.Interp Exec.Interp.Stateful

theorem stateful_table_init_dispatch {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P) (frameIndex : Usize)
    (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction) (C : context)
    (state : Abs.AState) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr)
    (front operands : List val) (input output : List valtype) (tableIndex sourceIndex : Nat) (first second a b entry : U32)
    (signature : Abs.Stateful.Signature C (.tableInit tableIndex sourceIndex) input output)
    (bindings : Abs.ModuleBindings (decodeStore view code store) (decodeInstance store inst) C)
    (found : store.instances.val[raw.instance.val]?=some inst)
    (functionFound : inst.module.functions.val[raw.function.val]?=some compiled)
    (sourceStore : state.store=decodeStore view code store) (moduleEq : f.module=decodeInstance store inst)
    (slots : FrameSlots exec raw f) (values : f.vals=front++operands)
    (operandTypes : operands.map Code.valueType=input)
    (typed : ∀ value∈operands,Val_ok (decodeStore view code store) value (Code.valueType value))
    (position : first.val=Code.slots (f.locals.map Code.valueType)+Code.slots (front.map Code.valueType))
    (arguments : Code.StatefulArguments (.tableInit tableIndex sourceIndex) a b)
    (pair : Code.StatefulPair compiled.indirect.val (.tableInit tableIndex sourceIndex) a b entry) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform frameIndex raw.instance raw.function raw.base
      (Code.statefulInstruction (.tableInit tableIndex sourceIndex) first second a entry) ⦃ out =>
      out.2.1=exec ∧ out.2.2.2=platform ∧ output=[] ∧
      (∃ address : runtime.TableAddr,∃ sourceAddress : Usize,∃ object sourceObject destination source count, store.tables.val[address.index.val]?=some object ∧
        store.elems.val[sourceAddress.val]?=some sourceObject ∧ sourceObject.ty=object.ty ∧
        TableInitializationEffect store address.index object sourceObject destination source count (out.1,out.2.2.1)) ∧
      FrameStoreMetadata store out.2.2.1 ∧ FrameSlots out.2.1 raw {f with code:=after,vals:=front} ∧
      Abs.Stateful.Transition state f rest after (.tableInit tableIndex sourceIndex)
        (statefulBulkResult view code state f rest after front (out.1,out.2.2.1)) ⦄ := by
  cases signature with
  | tableInit tableIndex sourceIndex type limits selected sourceSelected =>
    obtain ⟨destination,source,count,rfl⟩ := three_i32_operands _ operands operandTypes typed
    obtain ⟨destinationSlot,sourceSlot,countSlot⟩ := frame_three_i32_slots destination source count slots values position
    obtain ⟨address,object,mapped,issued,objectType⟩ := table_binding_raw view code store inst C tableIndex _ bindings selected
    obtain ⟨sourceAddress,sourceObject,sourceMapped,sourceFound,sourceType⟩ := element_object_binding_raw view code store inst C sourceIndex _ bindings sourceSelected
    have sameType : sourceObject.ty=object.ty := decode_elem_type_injective (sourceType.trans objectType.symm)
    have tableEq : b.val=tableIndex := arguments.2
    have sourceEq : a.val=sourceIndex := arguments.1
    rw [←tableEq] at mapped
    rw [←sourceEq] at sourceMapped
    have normalized : f.vals=front++[Abs.integerVal .I32 (bulkWord (UScalar.cast .U64 destination)).val,
        Abs.integerVal .I32 (bulkWord (UScalar.cast .U64 source)).val,Abs.integerVal .I32 (bulkWord (UScalar.cast .U64 count)).val] := by
      simpa [bulkWord] using values
    obtain ⟨out,run,same,effect,metadata,transition⟩ := WP.spec_imp_exists
      (segment_execute_bulk memory exec store raw.instance raw.function raw.base (.TableInit first entry) _
        (stateful_table_init_effect memory view code store raw.instance raw.function raw.base (alloc.vec.Vec.deref exec.slots)
          first entry b a inst compiled address sourceAddress object sourceObject (UScalar.cast .U64 destination) (UScalar.cast .U64 source) (UScalar.cast .U64 count)
          state f rest after front found functionFound pair sourceMapped sourceFound sameType.symm mapped issued (by simpa [alloc.vec.Vec.deref] using destinationSlot) (by simpa [alloc.vec.Vec.deref] using sourceSlot) (by simpa [alloc.vec.Vec.deref] using countSlot) sourceStore moduleEq normalized))
    simp only [Code.statefulInstruction,runtime.interp.dispatch,run,bind_ok,WP.spec_ok]
    exact ⟨same,rfl,trivial,⟨address,sourceAddress,object,sourceObject,_,_,_,issued,sourceFound,sameType,effect⟩,metadata,
      by rw [same];exact frame_consume after slots values,by simpa only [tableEq,sourceEq] using transition⟩
end Exec.Theorems
