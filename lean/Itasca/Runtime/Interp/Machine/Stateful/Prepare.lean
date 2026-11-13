import Itasca.Runtime.Interp.Machine.Execution
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulEmission
import Itasca.Runtime.Interp.Machine.Coverage.OrdinaryHeads
import Itasca.Runtime.Interp.State.StatefulSegmentLookup

/-!
Sections, each formerly its own module: Projection, Prepare.
-/

/-! ## Projection -/

section

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

end

/-! ## Prepare -/

section

/-!
Source operand values at a stateful code point.

Main declarations: `point_values`. A direct consumer is `Integration.Api.StatefulMemoryGrowExecution`.
-/

namespace Itasca.Runtime.Interp.Stateful
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Spec
variable {jumpTables : List Aeneas.Std.U32}
theorem point_values {emission : Machine.ContextEmission} {pairs C returns code labels pc next output}
    [Machine.StatefulProjection emission pairs]
    (s : store) (f : SourceMachine.AFrame) (op : SourceMachine.Stateful.Instruction) (after : List instr)
    (typed : SourceMachine.FrameTyped s {f with code:=op.source::after} [])
    (point : Compiler.StructuredCode.Point (emission C) C.TYPES C.FUNCS returns C.LOCALS
      code jumpTables labels (f.vals.map Compiler.valueType) (op.source::after) pc next output) :
    (∃ target : U32, pc<target.val ∧ code[pc]?=some (.Jump target) ∧
      Compiler.StructuredCode.Point (emission C) C.TYPES C.FUNCS returns C.LOCALS
        code jumpTables labels (f.vals.map Compiler.valueType) (op.source::after) target.val next output) ∨
    (∃ front operands input result first second a b entry,
      f.vals=front++operands ∧ operands.map Compiler.valueType=input ∧
      SourceMachine.Stateful.Signature C op input result ∧
      (∀ label ∈ f.labels,label.height≤front.length) ∧
      (∀ value ∈ operands,Val_ok s value (Compiler.valueType value)) ∧
      first.val=Compiler.slots C.LOCALS+Compiler.slots (front.map Compiler.valueType) ∧
      (op.arity≥2 → second.val=first.val+1) ∧ Compiler.StatefulArguments op a b ∧
      Compiler.StatefulPair pairs op a b entry ∧ code[pc]?=some (Compiler.statefulInstruction op first second a entry) ∧
      Compiler.StructuredCode.Point (emission C) C.TYPES C.FUNCS returns C.LOCALS
        code jumpTables labels (front.map Compiler.valueType++result) after (pc+1) next output) := by
  rcases point_head (pairs:=pairs) op after point with jump | operation
  · exact Or.inl jump
  · obtain ⟨types,input,result,first,second,a,b,entry,signature,stack,position,secondSlot,arguments,pair,fetch,tail⟩ := operation
    obtain ⟨front,operands,values,frontTypes,operandTypes⟩ := List.map_eq_append_iff.mp stack
    have arity : operands.length=op.arity := by
      have h := congrArg List.length operandTypes
      simpa only [List.length_map,signature.input_length] using h
    refine Or.inr ⟨front,operands,input,result,first,second,a,b,entry,values,operandTypes,signature,
      operand_heights typed front operands values arity,?_,?_,secondSlot,arguments,pair,fetch,?_⟩
    · intro value member
      cases typed with
      | mk context bindings localTypes locals actualValues returns code frameWf =>
        have included : value∈f.vals := by rw [values]; exact List.mem_append_right front member
        simpa only [value_type_eq_abs] using SourceMachine.results_typed_self_mem actualValues included
    · simpa only [frontTypes] using position
    · simpa only [frontTypes] using tail
end Itasca.Runtime.Interp.Stateful

end
