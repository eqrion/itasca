import Exec.Interp.StructuredMachine.StatefulHeads
namespace Exec.Interp.Stateful
open Aeneas.Std

theorem linear_decode_none {locals before instruction emitted after}
    (head : Code.LinearEmission locals before instruction emitted after) :
    Abs.Stateful.decodeInstruction instruction = none := by
  cases head with
  | binary stack type op a b left right => cases op <;> rfl
  | numeric stack op a b left right => cases op <;> rfl
  | _ => rfl

theorem core_decode_none {C before instruction emitted after}
    (head : Code.CoreEmission C before instruction emitted after) :
    Abs.Stateful.decodeInstruction instruction = none := by
  cases head with
  | pure h => exact linear_decode_none h
  | _ => rfl

theorem float_decode_none {C before instruction emitted after}
    (head : Code.FloatCoreEmission C before instruction emitted after) :
    Abs.Stateful.decodeInstruction instruction = none := by
  cases head with
  | core h => exact core_decode_none h
  | scalar stack op a b left right => cases op <;> rfl

theorem cumulative_emission_inv {pairs C before emitted after} (op : Abs.Stateful.Instruction)
    (head : Code.CumulativeEmission pairs C before op.source emitted after) :
    ∃ stack input output first second a b entry,
      Abs.Stateful.Signature C op input output ∧ before = stack++input ∧ after = stack++output ∧
      first.val = Code.slots C.LOCALS+Code.slots stack ∧
      (op.arity ≥ 2 → second.val = first.val+1) ∧
      Code.StatefulArguments op a b ∧ Code.StatefulPair pairs op a b entry ∧
      emitted = [Code.statefulInstruction op first second a entry] := by
  cases head with
  | left h =>
    have impossible := float_decode_none h
    simp only [Abs.Stateful.decode_source] at impossible
    contradiction
  | indirect h =>
    generalize sourceEq : op.source = source at h
    cases h with
    | call front params results typeIndex tableIndex entry index base bounds signature table pair basePosition indexPosition =>
      have impossible := congrArg Abs.Stateful.decodeInstruction sourceEq
      rw [Abs.Stateful.decode_source] at impossible
      contradiction
  | right h =>
    generalize sourceEq : op.source = source at h
    cases h with
    | instruction stack input output other signature first second a b entry firstSlot secondSlot arguments pair =>
      have same := Abs.Stateful.source_injective sourceEq
      subst other
      exact ⟨stack,input,output,first,second,a,b,entry,signature,rfl,rfl,firstSlot,secondSlot,arguments,pair,rfl⟩

theorem cumulative_point_head {pairs C returns code labels stack pc next output}
    (op : Abs.Stateful.Instruction) (after : List instr)
    (point : Code.StructuredCode.Point (Code.CumulativeEmission pairs C) C.TYPES C.FUNCS returns C.LOCALS
      code labels stack (op.source::after) pc next output) :
    (∃ target : U32, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Code.StructuredCode.Point (Code.CumulativeEmission pairs C) C.TYPES C.FUNCS returns C.LOCALS
        code labels stack (op.source::after) target.val next output) ∨
    (∃ front input result first second a b entry,
      Abs.Stateful.Signature C op input result ∧ stack = front++input ∧
      first.val = Code.slots C.LOCALS+Code.slots front ∧
      (op.arity ≥ 2 → second.val = first.val+1) ∧
      Code.StatefulArguments op a b ∧ Code.StatefulPair pairs op a b entry ∧
      code[pc]? = some (Code.statefulInstruction op first second a entry) ∧
      Code.StructuredCode.Point (Code.CumulativeEmission pairs C) C.TYPES C.FUNCS returns C.LOCALS
        code labels (front++result) after (pc+1) next output) := by
  have relation := point.current
  generalize sourceEq : op.source::after = source at relation
  cases relation with
  | linear head fragment rest =>
    obtain ⟨headEq,tailEq⟩ := List.cons.inj sourceEq
    subst_vars
    obtain ⟨front,input,result,first,second,a,b,entry,signature,stackEq,resultEq,firstSlot,secondSlot,arguments,pair,emitted⟩ := cumulative_emission_inv op head
    subst_vars
    have fetch := fragment.fetch (index := 0) (by rfl)
    obtain ⟨_,_,_,_,nextEq⟩ := fragment
    refine Or.inr ⟨front,input,result,first,second,a,b,entry,signature,rfl,firstSlot,secondSlot,arguments,pair,by simpa using fetch,?_⟩
    exact ⟨by simpa only [List.length_singleton] using nextEq ▸ rest,point.targets,point.normal,point.exit,point.root⟩
  | skip forward instruction rest =>
    subst_vars
    exact Or.inl ⟨_,forward,instruction,⟨rest,point.targets,point.normal,point.exit,point.root⟩⟩
  | _ => cases op <;> simp [Abs.Stateful.Instruction.source] at sourceEq
end Exec.Interp.Stateful
