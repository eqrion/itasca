import Itasca.Runtime.Interp.State.StatefulSlots
namespace Itasca.Runtime.Interp.Stateful
open Aeneas Aeneas.Std

theorem reference_word_value (value : val) (type : Itasca.wasm_types.ElemType) (word : U64)
    (typed : Compiler.valueType value=valtype_reftype (Store.decodeElemType type))
    (encoded : Compiler.encodeValue value=[word.val]) :
    value=val_ref (Store.decodeRef type word) := by
  cases value with
  | CONST ty bits => cases ty <;> cases type <;> simp [Compiler.valueType,Store.decodeElemType,valtype_reftype,valtype_numtype] at typed
  | VCONST ty bits => cases type <;> simp [Compiler.valueType,Store.decodeElemType,valtype_reftype,valtype_numtype] at typed
  | REF_NULL reference =>
    cases reference <;> cases type <;> simp_all [Compiler.valueType,Compiler.encodeValue,Store.decodeElemType,valtype_reftype,Store.decodeRef,val_ref]
  | REF_FUNC_ADDR index =>
    cases type <;> simp_all [Compiler.valueType,Compiler.encodeValue,Store.decodeElemType,valtype_reftype,Store.decodeRef,val_ref]
    all_goals simp [←encoded]
  | REF_HOST_ADDR index =>
    cases type <;> simp_all [Compiler.valueType,Compiler.encodeValue,Store.decodeElemType,valtype_reftype,Store.decodeRef,val_ref]
    all_goals simp [←encoded]
theorem reference_encoding (reference : ref) : ∃ bits, Compiler.encodeValue (val_ref reference) = [bits] := by
  cases reference <;> exact ⟨_,rfl⟩

theorem ref_is_null_value_slots
    (exec : runtime.interp.Execution) (raw : runtime.interp.Frame) (dst : U32)
    (type : Itasca.wasm_types.ElemType) (state : SourceMachine.AState) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (after : List instr) (front : List val) (reference : ref)
    (slots : FrameSlots exec raw f) (values : f.vals=front++[val_ref reference])
    (referenceType : Compiler.valueType (val_ref reference)=valtype_reftype (Store.decodeElemType type))
    (position : dst.val=Compiler.slots (f.locals.map Compiler.valueType)+Compiler.slots (front.map Compiler.valueType)) :
    runtime.interp.execute_ref_is_null exec raw.base dst dst ⦃ out =>
      out.1=.Ok () ∧ ∃ word : U64, word.val=Spec.referenceIsNull reference ∧
        SlotsEffect exec out.2 (exec.slots.val.set (raw.base.val+dst.val) word) ∧
        FrameSlots out.2 raw {f with code:=after,vals:=front++[SourceMachine.integerVal .I32 word.val]} ∧
        SourceMachine.Stateful.Transition state f rest after .refIsNull
          (SourceMachine.advance state {f with code:=after,vals:=front++[SourceMachine.integerVal .I32 word.val]} rest) ⦄ := by
  obtain ⟨bits,encoded⟩ := reference_encoding reference
  have wordEq := (frame_read_word slots values position encoded).2
  have same := reference_word_value (val_ref reference) type exec.slots.val[raw.base.val+dst.val]! referenceType (by rw [wordEq]; exact encoded)
  have referenceEq : reference=Store.decodeRef type exec.slots.val[raw.base.val+dst.val]! := by
    have equality := congrArg SourceMachine.Stateful.asReference same
    simpa only [SourceMachine.Stateful.as_reference_value,Option.some.injEq] using equality
  have decodedValues : f.vals=front++[val_ref (Store.decodeRef type exec.slots.val[raw.base.val+dst.val]!)] := by rw [←referenceEq]; exact values
  apply WP.spec_mono (ref_is_null_slots exec raw dst type state f rest after front slots decodedValues position)
  intro out effect
  simpa only [←referenceEq] using effect
end Itasca.Runtime.Interp.Stateful
