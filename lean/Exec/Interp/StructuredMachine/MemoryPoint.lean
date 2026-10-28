import Exec.Interp.StructuredMachine.OrdinaryHeads
import Exec.Code.Local.Lowering.Float.FloatEmissionInversion
import Exec.Interp.Memory.MemoryCoreEmission
namespace Itasca.Runtime.Interp.StructuredMachine.Memory
variable {jumpTables : List Aeneas.Std.U32}
variable {family : ContextEmission} [FloatHeads family]
open Itasca.Runtime.Interp.MemoryDescriptor
open Aeneas Aeneas.Std

 theorem corePoint_load_head {C returns code labels stack pc next output}
    (op : Abs.Memory.Load) (argument : memarg) (after : List instr)
    (point : Code.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
      (op.source argument :: after) pc next output) :
    (∃ target : U32, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Code.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
        (op.source argument :: after) target.val next output) ∨
    (∃ front address offset, stack = front ++ [.I32] ∧
      address.val = Code.slots C.LOCALS + Code.slots front ∧ argument.OFFSET = .mk_uN offset.val ∧
      code[pc]? = some (Code.memoryLoadInstruction op address address offset) ∧
      Code.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels
        (front ++ [valtype_numtype op.type]) after (pc+1) next output) := by
  have relation := point.current
  generalize sourceEq : op.source argument :: after = source at relation
  cases relation with
  | linear head ordinary fragment rest =>
    obtain ⟨headEq,tailEq⟩ := List.cons.inj sourceEq
    subst_vars
    obtain ⟨front,address,offset,input,emitted,result,offsetEq,position⟩ := scalarEmission_load_inv op argument (FloatHeads.project (.core (.load op argument)) head)
    subst_vars
    have fetch := fragment.fetch (index := 0) (by rfl)
    obtain ⟨_,_,_,_,nextEq⟩ := fragment
    refine Or.inr ⟨front,address,offset,rfl,position,offsetEq,by simpa using fetch,?_⟩
    exact ⟨by simpa only [List.length_singleton] using nextEq ▸ rest,point.targets,point.normal,point.exit,point.root⟩
  | skip forward instruction rest =>
    subst_vars
    exact Or.inl ⟨_,forward,instruction,⟨rest,point.targets,point.normal,point.exit,point.root⟩⟩
  | _ => simp [Abs.Memory.Load.source] at sourceEq

 theorem corePoint_store_head {C returns code labels stack pc next output}
    (op : Abs.Memory.Store) (argument : memarg) (after : List instr)
    (point : Code.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
      (op.source argument :: after) pc next output) :
    (∃ target : U32, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Code.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
        (op.source argument :: after) target.val next output) ∨
    (∃ front address value offset, stack = front ++ [.I32,valtype_numtype op.type] ∧
      address.val = Code.slots C.LOCALS + Code.slots front ∧ value.val = address.val+1 ∧ argument.OFFSET = .mk_uN offset.val ∧
      code[pc]? = some (Code.memoryStoreInstruction op address value offset) ∧
      Code.StructuredCode.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels
        front after (pc+1) next output) := by
  have relation := point.current
  generalize sourceEq : op.source argument :: after = source at relation
  cases relation with
  | linear head ordinary fragment rest =>
    obtain ⟨headEq,tailEq⟩ := List.cons.inj sourceEq
    subst_vars
    obtain ⟨front,address,value,offset,input,emitted,result,offsetEq,position,valuePosition⟩ := scalarEmission_store_inv op argument (FloatHeads.project (.core (.store op argument)) head)
    subst_vars
    have fetch := fragment.fetch (index := 0) (by rfl)
    obtain ⟨_,_,_,_,nextEq⟩ := fragment
    refine Or.inr ⟨front,address,value,offset,rfl,position,valuePosition,offsetEq,by simpa using fetch,?_⟩
    exact ⟨by simpa only [List.length_singleton] using nextEq ▸ rest,point.targets,point.normal,point.exit,point.root⟩
  | skip forward instruction rest =>
    subst_vars
    exact Or.inl ⟨_,forward,instruction,⟨rest,point.targets,point.normal,point.exit,point.root⟩⟩
  | _ => simp [Abs.Memory.Store.source] at sourceEq
end Itasca.Runtime.Interp.StructuredMachine.Memory
