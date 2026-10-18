import Exec.Interp.StructuredMachine.FloatHeads
import Exec.Code.Local.Lowering.Float.FloatCoreProjection
import Exec.Interp.Machines.Core.CoreIntegerConstantPoint
namespace Exec.Interp.StructuredMachine.IntegerConstant
variable {jumpTables : List Aeneas.Std.U32}
variable {family : ContextEmission} [FloatHeads family]
open Aeneas Aeneas.Std SpecExt Exec.Interp.IntegerConstant
theorem corePoint_integer32_head {C returns code labels stack pc next output}
    (value : U32) (after : List instr)
    (point : Code.StructuredCodeWithTables.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
      (.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val)) :: after) pc next output) :
    (∃ target : U32, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Code.StructuredCodeWithTables.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
        (.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val)) :: after) target.val next output) ∨
    (∃ dst bits, value = bits ∧
      dst.val = Code.slots C.LOCALS + Code.slots stack ∧ code[pc]? = some (.Const32 dst bits) ∧
      Code.StructuredCodeWithTables.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels
        (stack ++ [.I32]) after (pc+1) next output) := by
  have relation := point.current
  generalize sourceEq : instr.CONST .I32 (.mk_num__0 .I32 (.mk_uN value.val)) :: after = source at relation
  cases relation with
  | linear head ordinary fragment rest =>
    obtain ⟨headEq,tailEq⟩ := List.cons.inj sourceEq
    subst_vars
    obtain ⟨dst,bits,emitted,result,valueEq,position⟩ := coreEmission_integer32_inv value ((FloatHeads.project (.core (.slice (.const .I32 (.mk_uN value.val)))) head).core_inv rfl)
    subst_vars
    have fetch := fragment.fetch (index := 0) (by rfl)
    obtain ⟨_,_,_,_,nextEq⟩ := fragment
    refine Or.inr ⟨dst,bits,rfl,position,by simpa using fetch,?_⟩
    exact ⟨by simpa only [List.length_singleton] using nextEq ▸ rest,point.targets,point.normal,point.exit,point.root⟩
  | skip forward instruction rest =>
    subst_vars
    exact Or.inl ⟨_,forward,instruction,⟨rest,point.targets,point.normal,point.exit,point.root⟩⟩
  | _ => cases sourceEq


theorem corePoint_integer64_head {C returns code labels stack pc next output}
    (value : U64) (after : List instr)
    (point : Code.StructuredCodeWithTables.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
      (.CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val)) :: after) pc next output) :
    (∃ target : U32, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Code.StructuredCodeWithTables.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels stack
        (.CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val)) :: after) target.val next output) ∨
    (∃ dst bits, value = bits ∧
      dst.val = Code.slots C.LOCALS + Code.slots stack ∧ code[pc]? = some (.Const64 dst bits) ∧
      Code.StructuredCodeWithTables.Point (family C) C.TYPES C.FUNCS returns C.LOCALS code jumpTables labels
        (stack ++ [.I64]) after (pc+1) next output) := by
  have relation := point.current
  generalize sourceEq : instr.CONST .I64 (.mk_num__0 .I64 (.mk_uN value.val)) :: after = source at relation
  cases relation with
  | linear head ordinary fragment rest =>
    obtain ⟨headEq,tailEq⟩ := List.cons.inj sourceEq
    subst_vars
    obtain ⟨dst,bits,emitted,result,valueEq,position⟩ := coreEmission_integer64_inv value ((FloatHeads.project (.core (.slice (.const .I64 (.mk_uN value.val)))) head).core_inv rfl)
    subst_vars
    have fetch := fragment.fetch (index := 0) (by rfl)
    obtain ⟨_,_,_,_,nextEq⟩ := fragment
    refine Or.inr ⟨dst,bits,rfl,position,by simpa using fetch,?_⟩
    exact ⟨by simpa only [List.length_singleton] using nextEq ▸ rest,point.targets,point.normal,point.exit,point.root⟩
  | skip forward instruction rest =>
    subst_vars
    exact Or.inl ⟨_,forward,instruction,⟨rest,point.targets,point.normal,point.exit,point.root⟩⟩
  | _ => cases sourceEq


end Exec.Interp.StructuredMachine.IntegerConstant
