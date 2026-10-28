import Exec.Interp.State.StatefulOperandSlots
import Exec.Interp.State.StatefulReferenceValue
namespace Itasca.Runtime.Interp.Stateful
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Store

theorem two_operand_values {operands : List val} {left right : valtype}
    (types : operands.map Code.valueType=[left,right]) :
    ∃ x y,operands=[x,y] ∧ Code.valueType x=left ∧ Code.valueType y=right := by
  cases operands with
  | nil => simp at types
  | cons x xs =>
    cases xs with
    | nil => simp at types
    | cons y ys =>
      simp only [List.map_cons,List.cons.injEq,List.map_eq_nil_iff] at types
      exact ⟨x,y,by rw [types.2.2],types.1,types.2.1⟩

theorem three_operand_values {operands : List val} {first second third : valtype}
    (types : operands.map Code.valueType=[first,second,third]) :
    ∃ x y z,operands=[x,y,z] ∧ Code.valueType x=first ∧ Code.valueType y=second ∧ Code.valueType z=third := by
  cases operands with
  | nil => simp at types
  | cons x xs =>
    have firstEq : Code.valueType x=first := (List.cons.inj types).1
    obtain ⟨y,z,rfl,secondEq,thirdEq⟩ := two_operand_values (List.cons.inj types).2
    exact ⟨x,y,z,rfl,firstEq,secondEq,thirdEq⟩

theorem frame_reference_second {exec : runtime.interp.Execution} {raw : runtime.interp.Frame}
    {f : Abs.AFrame} {front : List val} {firstValue : val} {bits : Nat} {reference : ref}
    {first second : U32} {type : Itasca.types.ElemType}
    (slots : FrameSlots exec raw f) (values : f.vals=front++[firstValue,val_ref reference])
    (prefixBits : Code.encodeValue firstValue=[bits])
    (referenceType : Code.valueType (val_ref reference)=valtype_reftype (decodeElemType type))
    (position : first.val=Code.slots (f.locals.map Code.valueType)+Code.slots (front.map Code.valueType))
    (secondSlot : second.val=first.val+1) :
    val_ref reference=val_ref (decodeRef type exec.slots.val[raw.base.val+second.val]!) := by
  obtain ⟨referenceBits,encoded⟩ := reference_encoding reference
  have suffix : Code.encodeValues [firstValue,val_ref reference]=[bits,referenceBits] := by
    simp [Code.encodeValues,prefixBits,encoded]
  obtain ⟨bound,word⟩ := frame_read_suffix_word slots values position suffix 1 (by simp)
  have wordEq : exec.slots.val[raw.base.val+second.val]!.val=referenceBits := by
    simpa [secondSlot,Nat.add_assoc] using word
  exact reference_word_value _ _ _ referenceType (by rw [wordEq];exact encoded)
theorem frame_read_scalar {exec : runtime.interp.Execution} {raw : runtime.interp.Frame}
    {f : Abs.AFrame} {front consumed : List val} {bits : List Nat} {src : U32}
    (slots : FrameSlots exec raw f) (values : f.vals=front++consumed)
    (position : src.val=Code.slots (f.locals.map Code.valueType)+Code.slots (front.map Code.valueType))
    (encoded : Code.encodeValues consumed=bits) (index : Nat) (bound : index<bits.length)
    (word : U64) (wordValue : word.val=bits[index]!) :
    exec.slots.val[raw.base.val+src.val+index]?=some word := by
  obtain ⟨fits,actual⟩ := frame_read_suffix_word slots values position encoded index bound
  have equal : exec.slots.val[raw.base.val+src.val+index]! = word := by scalar_tac
  rw [List.getElem?_eq_getElem fits]
  rw [←_root_.getElem!_pos exec.slots.val (raw.base.val+src.val+index) fits,equal]
end Itasca.Runtime.Interp.Stateful
