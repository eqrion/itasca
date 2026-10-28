import Exec.Interp.State.StatefulSlots
namespace Itasca.Runtime.Interp.Stateful
open Aeneas Aeneas.Std

theorem reference_word_value (value : val) (type : Itasca.types.ElemType) (word : U64)
    (typed : Code.valueType value=valtype_reftype (Store.decodeElemType type))
    (encoded : Code.encodeValue value=[word.val]) :
    value=val_ref (Store.decodeRef type word) := by
  cases value with
  | CONST ty bits => cases ty <;> cases type <;> simp [Code.valueType,Store.decodeElemType,valtype_reftype,valtype_numtype] at typed
  | VCONST ty bits => cases type <;> simp [Code.valueType,Store.decodeElemType,valtype_reftype,valtype_numtype] at typed
  | REF_NULL reference =>
    cases reference <;> cases type <;> simp_all [Code.valueType,Code.encodeValue,Store.decodeElemType,valtype_reftype,Store.decodeRef,val_ref]
  | REF_FUNC_ADDR index =>
    cases type <;> simp_all [Code.valueType,Code.encodeValue,Store.decodeElemType,valtype_reftype,Store.decodeRef,val_ref]
    all_goals simp [←encoded]
  | REF_HOST_ADDR index =>
    cases type <;> simp_all [Code.valueType,Code.encodeValue,Store.decodeElemType,valtype_reftype,Store.decodeRef,val_ref]
    all_goals simp [←encoded]
theorem reference_encoding (reference : ref) : ∃ bits, Code.encodeValue (val_ref reference) = [bits] := by
  cases reference <;> exact ⟨_,rfl⟩

theorem ref_is_null_value_slots
    (exec : runtime.interp.Execution) (raw : runtime.interp.Frame) (dst : U32)
    (type : Itasca.types.ElemType) (state : Abs.AState) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (after : List instr) (front : List val) (reference : ref)
    (slots : FrameSlots exec raw f) (values : f.vals=front++[val_ref reference])
    (referenceType : Code.valueType (val_ref reference)=valtype_reftype (Store.decodeElemType type))
    (position : dst.val=Code.slots (f.locals.map Code.valueType)+Code.slots (front.map Code.valueType)) :
    runtime.interp.execute_ref_is_null exec raw.base dst dst ⦃ out =>
      out.1=.Ok () ∧ ∃ word : U64, word.val=Spec.referenceIsNull reference ∧
        SlotsEffect exec out.2 (exec.slots.val.set (raw.base.val+dst.val) word) ∧
        FrameSlots out.2 raw {f with code:=after,vals:=front++[Abs.integerVal .I32 word.val]} ∧
        Abs.Stateful.Transition state f rest after .refIsNull
          (Abs.advance state {f with code:=after,vals:=front++[Abs.integerVal .I32 word.val]} rest) ⦄ := by
  obtain ⟨bits,encoded⟩ := reference_encoding reference
  have wordEq := (frame_read_word slots values position encoded).2
  have same := reference_word_value (val_ref reference) type exec.slots.val[raw.base.val+dst.val]! referenceType (by rw [wordEq]; exact encoded)
  have referenceEq : reference=Store.decodeRef type exec.slots.val[raw.base.val+dst.val]! := by
    have equality := congrArg Abs.Stateful.asReference same
    simpa only [Abs.Stateful.asReference_value,Option.some.injEq] using equality
  have decodedValues : f.vals=front++[val_ref (Store.decodeRef type exec.slots.val[raw.base.val+dst.val]!)] := by rw [←referenceEq]; exact values
  apply WP.spec_mono (ref_is_null_slots exec raw dst type state f rest after front slots decodedValues position)
  intro out effect
  simpa only [←referenceEq] using effect
end Itasca.Runtime.Interp.Stateful
