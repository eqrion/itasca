import Exec.Interp.Numeric.Float.FloatPoint
import Exec.Code.Local.Lowering.Float.FloatCoreProjection
import Exec.Interp.Memory.MemoryCoreEmission
namespace Exec.Interp.FloatMemoryDescriptor
open Exec.Interp.MemoryDescriptor
open Aeneas Aeneas.Std

 theorem corePoint_load_head {C returns code labels stack pc next output}
    (op : Abs.Memory.Load) (argument : memarg) (after : List instr)
    (point : Code.StructuredCode.Point (Code.FloatCoreEmission C) C.TYPES C.FUNCS returns C.LOCALS code labels stack
      (op.source argument :: after) pc next output) :
    (∃ target : U32, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Code.StructuredCode.Point (Code.FloatCoreEmission C) C.TYPES C.FUNCS returns C.LOCALS code labels stack
        (op.source argument :: after) target.val next output) ∨
    (∃ front address offset, stack = front ++ [.I32] ∧
      address.val = Code.slots C.LOCALS + Code.slots front ∧ argument.OFFSET = .mk_uN offset.val ∧
      code[pc]? = some (Code.memoryLoadInstruction op address address offset) ∧
      Code.StructuredCode.Point (Code.FloatCoreEmission C) C.TYPES C.FUNCS returns C.LOCALS code labels
        (front ++ [valtype_numtype op.type]) after (pc+1) next output) := by
  have relation := point.current
  generalize sourceEq : op.source argument :: after = source at relation
  cases relation with
  | linear head fragment rest =>
    obtain ⟨headEq,tailEq⟩ := List.cons.inj sourceEq
    subst_vars
    obtain ⟨front,address,offset,input,emitted,result,offsetEq,position⟩ := coreEmission_load_inv op argument (head.core_inv (by cases op <;> rfl))
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
    (point : Code.StructuredCode.Point (Code.FloatCoreEmission C) C.TYPES C.FUNCS returns C.LOCALS code labels stack
      (op.source argument :: after) pc next output) :
    (∃ target : U32, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Code.StructuredCode.Point (Code.FloatCoreEmission C) C.TYPES C.FUNCS returns C.LOCALS code labels stack
        (op.source argument :: after) target.val next output) ∨
    (∃ front address value offset, stack = front ++ [.I32,valtype_numtype op.type] ∧
      address.val = Code.slots C.LOCALS + Code.slots front ∧ value.val = address.val+1 ∧ argument.OFFSET = .mk_uN offset.val ∧
      code[pc]? = some (Code.memoryStoreInstruction op address value offset) ∧
      Code.StructuredCode.Point (Code.FloatCoreEmission C) C.TYPES C.FUNCS returns C.LOCALS code labels
        front after (pc+1) next output) := by
  have relation := point.current
  generalize sourceEq : op.source argument :: after = source at relation
  cases relation with
  | linear head fragment rest =>
    obtain ⟨headEq,tailEq⟩ := List.cons.inj sourceEq
    subst_vars
    obtain ⟨front,address,value,offset,input,emitted,result,offsetEq,position,valuePosition⟩ := coreEmission_store_inv op argument (head.core_inv (by cases op <;> rfl))
    subst_vars
    have fetch := fragment.fetch (index := 0) (by rfl)
    obtain ⟨_,_,_,_,nextEq⟩ := fragment
    refine Or.inr ⟨front,address,value,offset,rfl,position,valuePosition,offsetEq,by simpa using fetch,?_⟩
    exact ⟨by simpa only [List.length_singleton] using nextEq ▸ rest,point.targets,point.normal,point.exit,point.root⟩
  | skip forward instruction rest =>
    subst_vars
    exact Or.inl ⟨_,forward,instruction,⟨rest,point.targets,point.normal,point.exit,point.root⟩⟩
  | _ => simp [Abs.Memory.Store.source] at sourceEq
end Exec.Interp.FloatMemoryDescriptor
