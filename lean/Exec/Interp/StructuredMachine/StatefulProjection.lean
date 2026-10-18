import Exec.Interp.Cumulative.Machine
import Exec.Interp.State.StatefulPoint
namespace Exec.Interp.StructuredMachine

/-- The current stateful source head retains its exact immutable index-pair metadata. -/
class StatefulProjection (emission : ContextEmission) (pairs : List (Aeneas.Std.U32 × Aeneas.Std.U32)) : Prop where
  project : ∀ {C before op emitted after}, emission C before (Abs.Stateful.Instruction.source op) emitted after →
    Code.StatefulEmission pairs C before op.source emitted after

end Exec.Interp.StructuredMachine
namespace Exec.Interp.Stateful
open Aeneas.Std

variable {jumpTables : List Aeneas.Std.U32}
theorem emission_inv {pairs C before emitted after} (op : Abs.Stateful.Instruction)
    (head : Code.StatefulEmission pairs C before op.source emitted after) :
    ∃ stack input output first second a b entry,
      Abs.Stateful.Signature C op input output ∧ before = stack++input ∧ after = stack++output ∧
      first.val = Code.slots C.LOCALS+Code.slots stack ∧
      (op.arity ≥ 2 → second.val = first.val+1) ∧
      Code.StatefulArguments op a b ∧ Code.StatefulPair pairs op a b entry ∧
      emitted = [Code.statefulInstruction op first second a entry] := by
  generalize sourceEq : op.source=source at head
  cases head with
  | instruction stack input output other signature first second a b entry firstSlot secondSlot arguments pair =>
    have same := Abs.Stateful.source_injective sourceEq
    subst other
    exact ⟨stack,input,output,first,second,a,b,entry,signature,rfl,rfl,firstSlot,secondSlot,arguments,pair,rfl⟩

theorem point_head {emission : StructuredMachine.ContextEmission} {pairs C returns code labels stack pc next output}
    [projection : StructuredMachine.StatefulProjection emission pairs]
    (op : Abs.Stateful.Instruction) (after : List instr)
    (point : Code.StructuredCodeWithTables.Point (emission C) C.TYPES C.FUNCS returns C.LOCALS
      code jumpTables labels stack (op.source::after) pc next output) :
    (∃ target : U32, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Code.StructuredCodeWithTables.Point (emission C) C.TYPES C.FUNCS returns C.LOCALS
        code jumpTables labels stack (op.source::after) target.val next output) ∨
    (∃ front input result first second a b entry,
      Abs.Stateful.Signature C op input result ∧ stack = front++input ∧
      first.val = Code.slots C.LOCALS+Code.slots front ∧
      (op.arity ≥ 2 → second.val = first.val+1) ∧
      Code.StatefulArguments op a b ∧ Code.StatefulPair pairs op a b entry ∧
      code[pc]? = some (Code.statefulInstruction op first second a entry) ∧
      Code.StructuredCodeWithTables.Point (emission C) C.TYPES C.FUNCS returns C.LOCALS
        code jumpTables labels (front++result) after (pc+1) next output) := by
  have relation := point.current
  generalize sourceEq : op.source::after = source at relation
  cases relation with
  | linear head ordinary fragment rest =>
    obtain ⟨headEq,tailEq⟩ := List.cons.inj sourceEq
    subst_vars
    obtain ⟨front,input,result,first,second,a,b,entry,signature,stackEq,resultEq,firstSlot,secondSlot,arguments,pair,emitted⟩ := emission_inv op (StructuredMachine.StatefulProjection.project (pairs:=pairs) head)
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

namespace Exec.Interp.StructuredMachine
instance {pairs} : StatefulProjection (Code.CumulativeEmission pairs) pairs where
  project := by
    intro C before op emitted after head
    cases head with
    | left h =>
      have impossible := Stateful.float_decode_none h
      simp only [Abs.Stateful.decode_source] at impossible
      contradiction
    | right h => exact h
    | indirect h =>
      generalize sourceEq : op.source=source at h
      cases h with
      | call front params results typeIndex tableIndex entry index base bounds signature table pair basePosition indexPosition =>
        have impossible := congrArg Abs.Stateful.decodeInstruction sourceEq
        rw [Abs.Stateful.decode_source] at impossible
        contradiction
end Exec.Interp.StructuredMachine

namespace Exec.Interp.StructuredMachine
instance (compiled : runtime.bytecode.CompiledFunction) :
    StatefulProjection (Cumulative.emission compiled) compiled.indirect.val := by
  unfold Cumulative.emission
  infer_instance
end Exec.Interp.StructuredMachine
