import Itasca.Runtime.Interp.Machine.Execution
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulEmission
import Itasca.Runtime.Interp.Machine.Coverage.OrdinaryHeads

/-!
Inversion of stateful emission and frame-point heads.

Main declarations: `emission_inv` and `point_head`. A direct consumer is `Interp.Machine.Stateful.Prepare`.
-/

namespace Itasca.Runtime.Interp.Stateful
open Aeneas.Std

variable {jumpTables : List Aeneas.Std.U32}
theorem emission_inv {pairs C before emitted after} (op : SourceMachine.Stateful.Instruction)
    (head : Compiler.StatefulEmission pairs C before op.source emitted after) :
    ∃ stack input output first second a b entry,
      SourceMachine.Stateful.Signature C op input output ∧ before = stack++input ∧ after = stack++output ∧
      first.val = Compiler.slots C.LOCALS+Compiler.slots stack ∧
      (op.arity ≥ 2 → second.val = first.val+1) ∧
      Compiler.StatefulArguments op a b ∧ Compiler.StatefulPair pairs op a b entry ∧
      emitted = [Compiler.statefulInstruction op first second a entry] := by
  generalize sourceEq : op.source=source at head
  cases head with
  | instruction stack input output other signature first second a b entry firstSlot secondSlot arguments pair =>
    have same := SourceMachine.Stateful.source_injective sourceEq
    subst other
    exact ⟨stack,input,output,first,second,a,b,entry,signature,rfl,rfl,firstSlot,secondSlot,arguments,pair,rfl⟩

theorem point_head {emission : Machine.ContextEmission} {pairs C returns code labels stack pc next output}
    [projection : Machine.StatefulProjection emission pairs]
    (op : SourceMachine.Stateful.Instruction) (after : List instr)
    (point : Compiler.StructuredCode.Point (emission C) C.TYPES C.FUNCS returns C.LOCALS
      code jumpTables labels stack (op.source::after) pc next output) :
    (∃ target : U32, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Compiler.StructuredCode.Point (emission C) C.TYPES C.FUNCS returns C.LOCALS
        code jumpTables labels stack (op.source::after) target.val next output) ∨
    (∃ front input result first second a b entry,
      SourceMachine.Stateful.Signature C op input result ∧ stack = front++input ∧
      first.val = Compiler.slots C.LOCALS+Compiler.slots front ∧
      (op.arity ≥ 2 → second.val = first.val+1) ∧
      Compiler.StatefulArguments op a b ∧ Compiler.StatefulPair pairs op a b entry ∧
      code[pc]? = some (Compiler.statefulInstruction op first second a entry) ∧
      Compiler.StructuredCode.Point (emission C) C.TYPES C.FUNCS returns C.LOCALS
        code jumpTables labels (front++result) after (pc+1) next output) := by
  have relation := point.current
  generalize sourceEq : op.source::after = source at relation
  cases relation with
  | linear head ordinary fragment rest =>
    obtain ⟨headEq,tailEq⟩ := List.cons.inj sourceEq
    subst_vars
    obtain ⟨front,input,result,first,second,a,b,entry,signature,stackEq,resultEq,firstSlot,secondSlot,arguments,pair,emitted⟩ := emission_inv op (Machine.StatefulProjection.project (pairs:=pairs) head)
    subst_vars
    have fetch := fragment.fetch (index := 0) (by rfl)
    obtain ⟨_,_,_,_,nextEq⟩ := fragment
    refine Or.inr ⟨front,input,result,first,second,a,b,entry,signature,rfl,firstSlot,secondSlot,arguments,pair,by simpa using fetch,?_⟩
    exact ⟨by simpa only [List.length_singleton] using nextEq ▸ rest,point.targets,point.normal,point.exit,point.root⟩
  | skip forward instruction rest =>
    subst_vars
    exact Or.inl ⟨_,forward,instruction,⟨rest,point.targets,point.normal,point.exit,point.root⟩⟩
  | _ => cases op <;> simp [SourceMachine.Stateful.Instruction.source] at sourceEq
end Itasca.Runtime.Interp.Stateful
