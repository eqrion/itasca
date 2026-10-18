import Exec.Interp.Numeric.Float.FloatPoint
import Exec.Code.Local.Lowering.Float.FloatCoreProjection
import Exec.Interp.Machines.Core.CoreFloatConstantPoint
namespace Exec.Interp.FloatCoreConstant
open Aeneas Aeneas.Std SpecExt Exec.Interp.FloatConstant
theorem corePoint_float32_head {C returns code labels stack pc next output}
    (value : fN) (after : List instr)
    (point : Code.StructuredCode.Point (Code.FloatCoreEmission C) C.TYPES C.FUNCS returns C.LOCALS code labels stack
      (.CONST .F32 (.mk_num__1 .F32 value) :: after) pc next output) :
    (∃ target : U32, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Code.StructuredCode.Point (Code.FloatCoreEmission C) C.TYPES C.FUNCS returns C.LOCALS code labels stack
        (.CONST .F32 (.mk_num__1 .F32 value) :: after) target.val next output) ∨
    (∃ dst bits, value = Builtins.floatOfBits 32 bits.val ∧
      dst.val = Code.slots C.LOCALS + Code.slots stack ∧ code[pc]? = some (.Const32 dst bits) ∧
      Code.StructuredCode.Point (Code.FloatCoreEmission C) C.TYPES C.FUNCS returns C.LOCALS code labels
        (stack ++ [.F32]) after (pc+1) next output) := by
  have relation := point.current
  generalize sourceEq : instr.CONST .F32 (.mk_num__1 .F32 value) :: after = source at relation
  cases relation with
  | linear head fragment rest =>
    obtain ⟨headEq,tailEq⟩ := List.cons.inj sourceEq
    subst_vars
    obtain ⟨dst,bits,emitted,result,valueEq,position⟩ := coreEmission_float32_inv value (head.core_inv rfl)
    subst_vars
    have fetch := fragment.fetch (index := 0) (by rfl)
    obtain ⟨_,_,_,_,nextEq⟩ := fragment
    refine Or.inr ⟨dst,bits,rfl,position,by simpa using fetch,?_⟩
    exact ⟨by simpa only [List.length_singleton] using nextEq ▸ rest,point.targets,point.normal,point.exit,point.root⟩
  | skip forward instruction rest =>
    subst_vars
    exact Or.inl ⟨_,forward,instruction,⟨rest,point.targets,point.normal,point.exit,point.root⟩⟩
  | _ => cases sourceEq


theorem corePoint_float64_head {C returns code labels stack pc next output}
    (value : fN) (after : List instr)
    (point : Code.StructuredCode.Point (Code.FloatCoreEmission C) C.TYPES C.FUNCS returns C.LOCALS code labels stack
      (.CONST .F64 (.mk_num__1 .F64 value) :: after) pc next output) :
    (∃ target : U32, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Code.StructuredCode.Point (Code.FloatCoreEmission C) C.TYPES C.FUNCS returns C.LOCALS code labels stack
        (.CONST .F64 (.mk_num__1 .F64 value) :: after) target.val next output) ∨
    (∃ dst bits, value = Builtins.floatOfBits 64 bits.val ∧
      dst.val = Code.slots C.LOCALS + Code.slots stack ∧ code[pc]? = some (.Const64 dst bits) ∧
      Code.StructuredCode.Point (Code.FloatCoreEmission C) C.TYPES C.FUNCS returns C.LOCALS code labels
        (stack ++ [.F64]) after (pc+1) next output) := by
  have relation := point.current
  generalize sourceEq : instr.CONST .F64 (.mk_num__1 .F64 value) :: after = source at relation
  cases relation with
  | linear head fragment rest =>
    obtain ⟨headEq,tailEq⟩ := List.cons.inj sourceEq
    subst_vars
    obtain ⟨dst,bits,emitted,result,valueEq,position⟩ := coreEmission_float64_inv value (head.core_inv rfl)
    subst_vars
    have fetch := fragment.fetch (index := 0) (by rfl)
    obtain ⟨_,_,_,_,nextEq⟩ := fragment
    refine Or.inr ⟨dst,bits,rfl,position,by simpa using fetch,?_⟩
    exact ⟨by simpa only [List.length_singleton] using nextEq ▸ rest,point.targets,point.normal,point.exit,point.root⟩
  | skip forward instruction rest =>
    subst_vars
    exact Or.inl ⟨_,forward,instruction,⟨rest,point.targets,point.normal,point.exit,point.root⟩⟩
  | _ => cases sourceEq


end Exec.Interp.FloatCoreConstant
