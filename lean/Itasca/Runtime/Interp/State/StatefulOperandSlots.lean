import Itasca.Runtime.Interp.State.StatefulSlots
namespace Itasca.Runtime.Interp.Stateful
open Aeneas Aeneas.Std

theorem frame_consume {exec : runtime.interp.Execution} {raw : runtime.interp.Frame}
    {f : SourceMachine.AFrame} {front consumed : List val} (after : List instr)
    (slots : FrameSlots exec raw f) (values : f.vals=front++consumed) :
    FrameSlots exec raw {f with code:=after,vals:=front} := by
  apply ValuesAt.locals (values := consumed)
  simpa only [FrameSlots,values,List.append_assoc] using slots

theorem frame_read_suffix {exec : runtime.interp.Execution} {raw : runtime.interp.Frame}
    {f : SourceMachine.AFrame} {front consumed : List val} {bits : List Nat} {src : U32}
    (slots : FrameSlots exec raw f) (values : f.vals=front++consumed)
    (position : src.val=Compiler.slots (f.locals.map Compiler.valueType)+Compiler.slots (front.map Compiler.valueType))
    (encoded : Compiler.encodeValues consumed=bits) :
    WordsAt exec.slots.val (raw.base.val+src.val) bits := by
  have words : WordsAt exec.slots.val raw.base.val (Compiler.encodeValues (f.locals++front)++bits) := by
    simpa only [FrameSlots,ValuesAt,values,Compiler.encode_values_append,encoded,List.append_assoc] using slots
  simpa only [Compiler.encode_values_length,List.map_append,Compiler.slots_append,←position] using words.append_right

theorem frame_read_suffix_word {exec : runtime.interp.Execution} {raw : runtime.interp.Frame}
    {f : SourceMachine.AFrame} {front consumed : List val} {bits : List Nat} {src : U32}
    (slots : FrameSlots exec raw f) (values : f.vals=front++consumed)
    (position : src.val=Compiler.slots (f.locals.map Compiler.valueType)+Compiler.slots (front.map Compiler.valueType))
    (encoded : Compiler.encodeValues consumed=bits) (index : Nat) (bound : index<bits.length) :
    raw.base.val+src.val+index<exec.slots.length ∧
    exec.slots.val[raw.base.val+src.val+index]!.val=bits[index]! :=
  frame_read_suffix slots values position encoded index bound
end Itasca.Runtime.Interp.Stateful
