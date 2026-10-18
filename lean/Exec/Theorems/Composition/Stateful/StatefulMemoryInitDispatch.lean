import Exec.Theorems.Composition.Stateful.StatefulMemoryInit
import Exec.Interp.State.StatefulIntegerOperands
import Exec.Interp.State.StatefulLookup
import Exec.Store.Initialization.SegmentStep
import Exec.Interp.State.StatefulSegmentLookup
import Exec.Store.Invariant.Typing
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Store Exec.Interp Exec.Interp.Stateful

theorem stateful_memory_init_dispatch {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P) (frameIndex : Usize)
    (raw : runtime.interp.Frame) (inst : runtime.store.Instance) (C : context)
    (state : Abs.AState) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr)
    (front operands : List val) (input output : List valtype) (index : Nat) (first second a b entry : U32)
    (signature : Abs.Stateful.Signature C (.memoryInit index) input output)
    (bindings : Abs.ModuleBindings (decodeStore view code store) (decodeInstance store inst) C)
    (found : store.instances.val[raw.instance.val]?=some inst)
    (shapes : ∀ object∈store.memories.val,MemoryShape view object) (bounds : SegmentBounds store)
    (sourceStore : state.store=decodeStore view code store) (moduleEq : f.module=decodeInstance store inst)
    (slots : FrameSlots exec raw f) (values : f.vals=front++operands)
    (operandTypes : operands.map Code.valueType=input)
    (typed : ∀ value∈operands,Val_ok (decodeStore view code store) value (Code.valueType value))
    (position : first.val=Code.slots (f.locals.map Code.valueType)+Code.slots (front.map Code.valueType))
    (arguments : Code.StatefulArguments (.memoryInit index) a b) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform frameIndex raw.instance raw.function raw.base
      (Code.statefulInstruction (.memoryInit index) first second a entry) ⦃ out =>
      out.2.1=exec ∧ out.2.2.2=platform ∧ output=[] ∧
      (∃ address : runtime.MemoryAddr,∃ object segment destination source count, store.memories.val[address.index.val]?=some object ∧
        MemoryInitializationEffect view store address.index object segment destination source count (out.1,out.2.2.1)) ∧
      FrameStoreMetadata store out.2.2.1 ∧ FrameSlots out.2.1 raw {f with code:=after,vals:=front} ∧
      Abs.Stateful.Transition state f rest after (.memoryInit index)
        (statefulBulkResult view code state f rest after front (out.1,out.2.2.1)) ⦄ := by
  cases signature with
  | memoryInit index type selected dataSelected =>
    obtain ⟨destination,source,count,rfl⟩ := three_i32_operands _ operands operandTypes typed
    obtain ⟨destinationSlot,sourceSlot,countSlot⟩ := frame_three_i32_slots destination source count slots values position
    obtain ⟨address,object,mapped,issued⟩ := memory_binding_raw view code store inst C type bindings selected
    have indexEq : a.val=index := arguments.1
    obtain ⟨dataAddress,dataMapped,dataIssued⟩ := data_binding_raw view code store inst C index _ bindings dataSelected
    rw [←indexEq] at dataMapped
    let segment := store.datas.val[dataAddress.val]
    have resolved : store.datas.val[dataAddress.val]?=some segment := List.getElem?_eq_getElem dataIssued
    have dataBound := bounds.data segment (List.mem_of_getElem? resolved)
    have normalized : f.vals=front++[Abs.integerVal .I32 (bulkWord (UScalar.cast .U64 destination)).val,
        Abs.integerVal .I32 (bulkWord (UScalar.cast .U64 source)).val,Abs.integerVal .I32 (bulkWord (UScalar.cast .U64 count)).val] := by
      simpa [bulkWord] using values
    obtain ⟨out,run,same,effect,metadata,transition⟩ := WP.spec_imp_exists
      (segment_admin_bulk memory hooks floats allocator exec store raw.instance raw.function raw.base (.MemoryInit first a) _
        (stateful_memory_init_effect memory view laws code store raw.instance raw.function raw.base (alloc.vec.Vec.deref exec.slots)
          first a inst address dataAddress object segment (UScalar.cast .U64 destination) (UScalar.cast .U64 source) (UScalar.cast .U64 count)
          state f rest after front found mapped issued (by simpa [alloc.vec.Vec.deref] using destinationSlot) (by simpa [alloc.vec.Vec.deref] using sourceSlot) (by simpa [alloc.vec.Vec.deref] using countSlot) dataMapped resolved (shapes object (List.mem_of_getElem? issued)).length_bound (Nat.le_of_lt dataBound) sourceStore moduleEq normalized))
    simp only [Code.statefulInstruction,runtime.interp.dispatch,run,bind_ok,WP.spec_ok]
    exact ⟨same,rfl,trivial,⟨address,object,segment,_,_,_,issued,effect⟩,metadata,
      by rw [same];exact frame_consume after slots values,by simpa only [indexEq] using transition⟩
end Exec.Theorems
