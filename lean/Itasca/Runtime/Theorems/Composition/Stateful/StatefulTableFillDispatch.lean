import Itasca.Runtime.Theorems.Composition.Stateful.StatefulTableFill
import Itasca.Runtime.Interp.State.StatefulIntegerOperands
import Itasca.Runtime.Interp.State.StatefulLookup
import Itasca.Runtime.Store.Initialization.SegmentStep
namespace Itasca.Runtime.Theorems
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Store Itasca.Runtime.Interp Itasca.Runtime.Interp.Stateful

theorem stateful_table_fill_dispatch {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P) (frameIndex : Usize)
    (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst) (C : context)
    (state : Abs.AState) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr)
    (front operands : List val) (input output : List valtype) (index : Nat) (first second a b entry : U32)
    (signature : Abs.Stateful.Signature C (.tableFill index) input output)
    (bindings : Abs.ModuleBindings (decodeStore view code store) (decodeInstance store inst) C)
    (found : store.instances.val[raw.instance.val]?=some inst)
    (sourceStore : state.store=decodeStore view code store) (moduleEq : f.module=decodeInstance store inst)
    (slots : FrameSlots exec raw f) (values : f.vals=front++operands)
    (operandTypes : operands.map Code.valueType=input)
    (typed : ∀ value∈operands,Val_ok (decodeStore view code store) value (Code.valueType value))
    (position : first.val=Code.slots (f.locals.map Code.valueType)+Code.slots (front.map Code.valueType))
    (arguments : Code.StatefulArguments (.tableFill index) a b) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform frameIndex raw.instance raw.function raw.base
      (Code.statefulInstruction (.tableFill index) first second a entry) ⦃ out =>
      out.2.1=exec ∧ out.2.2.2=platform ∧ output=[] ∧
      (∃ address : runtime.TableAddr,∃ object destination value count, store.tables.val[address.index.val]?=some object ∧ val_ref (decodeRef object.ty value)∈f.vals ∧
        TableFillEffect store address.index object destination value count (out.1,out.2.2.1)) ∧
      FrameStoreMetadata store out.2.2.1 ∧ FrameSlots out.2.1 raw {f with code:=after,vals:=front} ∧
      Abs.Stateful.Transition state f rest after (.tableFill index)
        (statefulBulkResult view code state f rest after front (out.1,out.2.2.1)) ⦄ := by
  cases signature with
  | tableFill index type limits selected =>
    obtain ⟨x,y,z,rfl,xType,yType,zType⟩ := three_operand_values operandTypes
    have xTyped := typed x (by simp)
    have yTyped := typed y (by simp)
    have zTyped := typed z (by simp)
    rw [xType] at xTyped
    rw [yType] at yTyped
    rw [zType] at zTyped
    obtain ⟨destinationBits,rfl,destinationBound⟩ := Abs.integer_val_inv (ty:=.I32) xTyped
    obtain ⟨reference,rfl,referenceTyped⟩ := Abs.Stateful.reference_operand yTyped
    obtain ⟨countBits,rfl,countBound⟩ := Abs.integer_val_inv (ty:=.I32) zTyped
    let destination : U32 := UScalar.ofNatCore destinationBits destinationBound
    let count : U32 := UScalar.ofNatCore countBits countBound
    obtain ⟨referenceBits,referenceEncoded⟩ := reference_encoding reference
    have encoded : Code.encodeValues [Abs.integerVal .I32 destinationBits,val_ref reference,Abs.integerVal .I32 countBits]=
        [destinationBits,referenceBits,countBits] := by
      simp only [Code.encodeValues,List.flatMap_cons,List.flatMap_nil,List.append_nil,referenceEncoded]
      rfl
    have destinationSlot := frame_read_scalar slots values position encoded 0 (by simp) (UScalar.cast .U64 destination) (by simp [destination])
    simp only [Nat.add_zero] at destinationSlot
    have countSlot := frame_read_scalar slots values position encoded 2 (by simp) (UScalar.cast .U64 count) (by simp [count])
    obtain ⟨valueBound,valueEq⟩ := frame_read_suffix_word slots values position encoded 1 (by simp)
    simp only [List.getElem!_cons_succ,List.getElem!_cons_zero] at valueEq
    let value := exec.slots.val[raw.base.val+first.val+1]!
    have valueSlot : exec.slots.val[raw.base.val+first.val+1]?=some value := by
      simp only [value,List.getElem?_eq_getElem valueBound,_root_.getElem!_pos exec.slots.val (raw.base.val+first.val+1) valueBound]
    obtain ⟨address,object,mapped,issued,objectType⟩ := table_binding_raw view code store inst C index _ bindings selected
    change decodeElemType object.ty=type at objectType
    have indexEq : a.val=index := arguments.1
    rw [←indexEq] at mapped
    have referenceEq : val_ref reference=val_ref (decodeRef object.ty value) :=
      reference_word_value _ _ _ (by simpa only [objectType] using yType) (by rw [valueEq];exact referenceEncoded)
    have normalized : f.vals=front++[Abs.integerVal .I32 (bulkWord (UScalar.cast .U64 destination)).val,
        val_ref (decodeRef object.ty value),Abs.integerVal .I32 (bulkWord (UScalar.cast .U64 count)).val] := by
      rw [←referenceEq]
      simpa [bulkWord,destination,count,Nat.mod_eq_of_lt (show destinationBits<4294967296 from destinationBound),Nat.mod_eq_of_lt (show countBits<4294967296 from countBound)] using values
    obtain ⟨out,run,same,effect,metadata,transition⟩ := WP.spec_imp_exists
      (segment_execute_bulk memory exec store raw.instance raw.function raw.base (.TableFill first a) _
        (stateful_table_fill_effect memory view code store raw.instance raw.function raw.base (alloc.vec.Vec.deref exec.slots)
          first a inst address object (UScalar.cast .U64 destination) value (UScalar.cast .U64 count)
          state f rest after front found mapped issued (by simpa [alloc.vec.Vec.deref] using destinationSlot)
          (by simpa [alloc.vec.Vec.deref] using valueSlot) (by simpa [alloc.vec.Vec.deref] using countSlot) sourceStore moduleEq normalized))
    simp only [Code.statefulInstruction,runtime.interp.dispatch,run,bind_ok,WP.spec_ok]
    exact ⟨same,rfl,trivial,⟨address,object,_,_,_,issued,by rw [←referenceEq,values];simp,effect⟩,metadata,
      by rw [same];exact frame_consume after slots values,by simpa only [indexEq] using transition⟩
end Itasca.Runtime.Theorems
